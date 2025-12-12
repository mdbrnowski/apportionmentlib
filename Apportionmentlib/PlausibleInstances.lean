/-
Copyright (c) 2025 Michał Dobranowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michał Dobranowski
-/
import Plausible.Arbitrary
import Apportionmentlib.Basic

/-!
# Instances for Plausible

In this file, we define some instances (like `Shrinkable`, `Arbitrary`, `SampleableExt`) so that
you can use the `plausible` tactic with Apportionmentlib. For example, try:

```lean4
import Apportionmentlib
import Plausible

open Apportionmentlib

example (p q : Party) : p.name ≠ q.name := by
  plausible
```
-/

open Plausible

namespace Apportionmentlib

-- instances for `Party`

instance : Shrinkable Party := {} -- there is not point in "simplifying" the name of a Party

instance : Arbitrary Party where
  arbitrary := do
    let n ← Gen.choose Nat 0 20 (by decide)
    return ⟨toString n⟩

instance : SampleableExt Party := SampleableExt.selfContained

-- instances for `Election`

instance : Shrinkable Election where
  shrink e := sorry

instance : Arbitrary Election where
  arbitrary := do
    let numParties ← Gen.choose Nat 1 10 (by decide)
    let partyList := (List.range numParties).map (fun i => (⟨toString (i + 1)⟩ : Party))
    let randomVotes ← partyList.mapM (fun _ => Gen.choose Nat 0 1000 (by decide))
    let voteMap := partyList.zip randomVotes
    let voteFunction := fun (p : Party) =>
      match voteMap.lookup p with
      | some count => count.val
      | none => 0
    let houseSize ← Gen.choose Nat 1 20 (by decide)
    return {
      parties := partyList.toFinset,
      votes := voteFunction,
      house_size := houseSize
    }

-- #sample Election

-- #eval Plausible.Shrinkable.shrink 5
-- #eval Plausible.Shrinkable.shrink (⟨"AB"⟩ : Party)

-- example (election : Election) : election.house_size = 2 := by
--   plausible

end Apportionmentlib
