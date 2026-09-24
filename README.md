# liveness

A dead store elimination pass for a small imperative language, implemented and verified in Lean 4. The optimiser runs a backwards liveness analysis, replaces writes to dead variables with `skip`, and carries a machine checked proof that its output is observationally equivalent to the source, meaning that it terminates precisely when the source does and that the final states coincide on every observed variable. The loop case of the analysis is a least fixed point obtained by an executable Kleene iteration whose termination, fixed point and leastness are themselves proved.

## Semantics

Expressions are integer constants, variables, `+`, `-`, `*`, `<` and `=`, where a comparison evaluates to `1` when it holds and to `0` otherwise, and statements are `skip`, assignment, sequencing, `ite` and `while`. States are total functions `String → Int`, so evaluation is total and effect free, and conditionals treat zero as false and anything else as true. The small step relation `Step` on `Stmt × State` has six rules, with `while e s` unfolding to `ite e (s; while e s) skip`, and termination and divergence are defined over its closures without fuel:

```
Terminates s σ σ' := Steps (s, σ) (.skip, σ')
Diverges c        := ∀ n, ∃ c', StepsN n c c'
```

The relation is deterministic, every configuration other than `skip` can step, terminating results are unique, and a configuration diverges exactly when it does not terminate, which coincides with having an infinite trace. A big step relation used only inside proofs is shown equivalent to termination, and the executable interpreter in `Interp.lean` is proved sound and complete against `Step`, so the fuelled runner reports a final state exactly for the terminating programs once the fuel reaches the length of their run, and reports exhaustion at every fuel for the diverging ones.

Two states agree on `L` when they coincide on every variable in `L`, and two programs are observationally equivalent when every terminating run of either is matched by a terminating run of the other with agreeing final states:

```
ObsEquiv L s t := ∀ σ,
  (∀ σ₁, Terminates s σ σ₁ → ∃ σ₂, Terminates t σ σ₂ ∧ Agree L σ₁ σ₂) ∧
  (∀ σ₂, Terminates t σ σ₂ → ∃ σ₁, Terminates s σ σ₁ ∧ Agree L σ₁ σ₂)
```

Because both directions demand termination, divergence can be neither introduced nor removed.

## Liveness

```
liveIn skip L         = L
liveIn (x := e) L     = (L \ {x}) ∪ FV(e)      if x ∈ L
                      = L                      otherwise
liveIn (s₁; s₂) L     = liveIn s₁ (liveIn s₂ L)
liveIn (ite e s₁ s₂) L = FV(e) ∪ liveIn s₁ L ∪ liveIn s₂ L
liveIn (while e s) L  = μX. L ∪ FV(e) ∪ liveIn s X
```

The analysis is monotone and bounded by `L ∪ vars s`, and the loop result contains `L` and `FV(e)`, is closed under the body transfer, is the least such set and is a genuine fixed point. Its semantic content is `liveness_sound`, which states that running `s` from two states agreeing on `liveIn s L` yields states agreeing on `L`.

The fixed point is computed by Kleene iteration from `∅` over the finite universe `L ∪ FV(e) ∪ vars s`, returning `X` once `F X ⊆ X` and otherwise continuing from `X ∪ F X`. Termination is well founded recursion on the number of universe elements not yet in `X`, which strictly decreases at every step, so no iteration bound is needed, and because the boundedness proof is required inside the recursive definition, `liveIn` is defined through a subtype carrying `liveIn s L ⊆ L ∪ vars s`. Variable sets are lists reasoned about through membership, and the optimiser depends only on the set a list denotes.

## Transformation

`dse s L` returns the optimised statement together with its live-in set, which is proved equal to `liveIn s L`. Dead assignments become `skip`, sequencing threads the live-in set of the second statement into the first, both branches of a conditional share the live-out set, and loop bodies are optimised against the fixed point `X`. The output mentions no new variables, is never larger than the input, and is idempotent in the form `optimise (optimise s X) Y = optimise s Y` for `Y ⊆ X`. Eliminated stores leave `skip` residue inside sequences, so `compact` folds `skip; t` and `t; skip` to `t` recursively through branches and loop bodies, and `optimiseCompact s L` is `compact (optimise s L)`. Compaction preserves big step derivations in both directions, so it is observationally equivalent on every observation set, and the composed pass inherits the variable and size bounds.

## Correctness

```
theorem dse_correct (s : Stmt) (L : VarSet) : ObsEquiv L s (optimise s L)
```

The theorem is proved twice. It generalises it to two initial states agreeing on the live-in set and proceeds by induction on big step derivations in each direction, with agreement on `X` as the loop invariant, which gives equal guards because `FV(e) ⊆ X`, admits the body hypothesis because `liveIn s X ⊆ X`, and is re-established after the body. It proves it on the small step semantics through `Match L (s, σ₁) (t, σ₂) := t = optimise s L ∧ Agree (liveIn s L) σ₁ σ₂`, matching each source step with one target step or with a stutter that only an eliminated assignment can cause and that strictly shrinks the source statement, so a diverging source always forces a target step and the backward direction follows from determinism.

## Examples

`x := 10; y := 20; x := 30` observed on `{x}` becomes `skip; skip; x := 30`, while `x := 10; if c then x := 20 else y := 30` keeps the first store because the else branch does not overwrite `x`, and `x := 0; y := 5; while (x - 10) do (x := x + 1; y := y + 1)` keeps both stores to `x` and drops both to `y`

 The loop `while 1 do y := y + 1; z := 0` becomes `while 1 do skip; skip` with divergence of both sides proved as theorems. Loop free cases are proved by `decide`. The loop fixed points do not reduce in the kernel because the iteration is defined by well founded recursion, so each loop case names its fixed point and proves it equal as a set through `liveIn_while_equiv_of`, which combines leastness with the post fixed point property, after which congruence of the optimiser in its live set reduces the transformation and the live-in set to `decide`. The test executable checks the same cases by running the solver and the verified interpreter.
