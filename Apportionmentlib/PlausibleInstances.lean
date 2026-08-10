/-
Copyright (c) 2025 Michał Dobranowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michał Dobranowski
-/
import Plausible.Arbitrary
import Mathlib.Testing.Plausible.Sampleable
import Apportionmentlib.Basic

/-!
# Instances for Plausible

In this file, we define some instances (like `Shrinkable`, `Arbitrary`, `SampleableExt`) so that
you can use the `plausible` tactic with Apportionmentlib. For example, try:

```lean4
import Apportionmentlib
import Plausible

open Apportionmentlib

example (e : Election 4) : e.votes[0] ≤ 15 + e.votes[1] := by
  plausible

#sample Election 2
```
-/

open Plausible

namespace Apportionmentlib

instance instShrinkableVectorNat {n : ℕ} : Shrinkable (Vector ℕ n) where
  shrink v :=
    (List.finRange n).flatMap fun (i : Fin n) =>
      (Shrinkable.shrink v[i]).map fun v' => v.set i v'

instance {n : ℕ} : Shrinkable (Election n) where
  shrink e :=
    let shrunkVotes := Shrinkable.shrink e.votes
    let shrunkHouseSizes := Shrinkable.shrink e.houseSize
    -- shrink votes only, shrink houseSize only, or shrink both
    (shrunkVotes.filterMap fun v =>
      if h : 0 < v.sum then some ⟨v, e.houseSize, h⟩ else none) ++
    (shrunkHouseSizes.map fun h => ⟨e.votes, h, e.votes_sum_pos⟩) ++
    (shrunkVotes.flatMap fun v =>
      if hv : 0 < v.sum then shrunkHouseSizes.map fun h => ⟨v, h, hv⟩ else [])

instance {n : ℕ} [NeZero n] : Arbitrary (Election n) where
  arbitrary := do
    let votes ← (Vector.replicate n ()).mapM fun _ => Gen.chooseNat
    let houseSize ← Gen.choose Nat 1 20 (by decide)
    have n_pos := NeZero.pos n
    let votes' := votes.set 0 (votes[0] + 1)
    return {
      votes := votes',
      houseSize := ⟨houseSize.val, houseSize.prop.left⟩,
      votes_sum_pos := by
        rw [sum_pos_iff_exists_pos]
        exact ⟨0, by simp [votes']⟩
    }

instance {n : ℕ} [NeZero n] : SampleableExt (Election n) := SampleableExt.selfContained

end Apportionmentlib
