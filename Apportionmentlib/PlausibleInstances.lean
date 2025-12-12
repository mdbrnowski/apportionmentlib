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

example {n : ℕ} (e : Election n) (h : 2 < n) : e.votes[0] > e.votes[1] := by
  plausible
```
-/

open Plausible

namespace Apportionmentlib

instance {n : ℕ} : Shrinkable (Election n) where
  shrink e :=
    let shrunkHouseSizes := Shrinkable.shrink e.houseSize
    Election.mk
      <$> pure e.votes
      <*> shrunkHouseSizes

instance {n : ℕ} : Arbitrary (Election n) where
  arbitrary := do
    let votes ← (Vector.replicate n ()).mapM fun _ => Gen.chooseNat
    let houseSize ← Gen.choose Nat 1 20 (by decide)
    return {
      votes := votes,
      houseSize := houseSize
    }

instance {n : ℕ} : SampleableExt (Election n) := SampleableExt.selfContained

#eval Shrinkable.shrink 10

#eval Shrinkable.shrink ({
  votes := #v[100, 200, 300],
  houseSize := 10
} : Election 3)

-- #sample Election 3


example {n : ℕ} (e : Election n) (h : 2 < n) : e.votes[0] > e.votes[1] := by
  plausible

end Apportionmentlib
