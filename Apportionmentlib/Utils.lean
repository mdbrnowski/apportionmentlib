/-
Copyright (c) 2026 Michał Dobranowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michał Dobranowski
-/
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

lemma sum_pos_iff_exists_pos {n : ℕ} {v : Vector ℕ n} : 0 < v.sum ↔ ∃ i : Fin n, 0 < v[i] := by
  constructor
  · contrapose!
    intro h_nonpos
    have h_zero (i : Fin n) := nonpos_iff_eq_zero.mp (h_nonpos i)
    rw [nonpos_iff_eq_zero]
    unfold Vector.sum
    rw [←Array.sum_eq_sum_toList]
    apply List.sum_eq_zero_iff.mpr
    intro x hx
    obtain ⟨i, hi⟩ : ∃ i : Fin n, x = v[i] := by
      apply List.mem_iff_get.mp hx |> fun ⟨i, hi⟩ => ⟨⟨i, by grind⟩, by convert hi.symm⟩
    exact hi.trans (h_zero i)
  · intro ⟨i, hi⟩
    have h_sum_pos : v.sum ≥ v[i] := by
      unfold Vector.sum
      rw [←Array.sum_eq_sum_toList]
      exact List.le_sum_of_mem (by simp)
    omega
