/-
Copyright (c) 2025 Michał Dobranowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michał Dobranowski
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Rat.Init
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.NormNum

open BigOperators

/-- Party (or candidate, state, ...) in an election. They are identified by their name. -/
structure Party where
  name : String
  deriving DecidableEq, Inhabited

instance : ToString Party where
  toString p := p.name

instance : Repr Party where
  reprPrec p _ := s!"{p.name} : Party"

/-- An election with a finite set of parties, a function giving the number of votes for each party,
and the total number of seats to be allocated. -/
structure Election where
  parties : Finset Party
  votes : Party -> ℕ
  total_seats : ℕ
  deriving Inhabited

@[simp]
def Election.total_voters (election : Election) : ℕ :=
  ∑ p ∈ election.parties, election.votes p

def Apportionment : Type := Party -> ℕ
def Rule : Type := Election -> Apportionment

/-- A rule is a quota rule if the number of seats allocated to each party `p` is either the floor
or the ceiling of its quota. -/
def is_quota_rule (rule : Rule) : Prop :=
  ∀ election : Election,
    let num_voters := election.total_voters
    ∀ p ∈ election.parties,
      let quota := (election.votes p * election.total_seats : ℚ) / (num_voters : ℚ)
      rule election p = ⌊quota⌋ ∨ rule election p = ⌈quota⌉

/-- A rule is population monotone if when the number of votes for a party `p` increases, but the
total number of votes remains the same, then the number of seats allocated to `p` does not decrease.
-/
def is_population_monotone (rule : Rule) : Prop :=
  ∀ election₁ election₂ : Election,
    election₁.parties = election₂.parties ∧
    election₁.total_seats = election₂.total_seats ∧
    election₁.total_voters = election₂.total_voters →
    ∀ p ∈ election₁.parties,
      election₁.votes p < election₂.votes p →
      rule election₁ p ≤ rule election₂ p


theorem balinski_young (rule : Rule) : is_quota_rule rule → ¬ is_population_monotone rule := by
  intro h_quota

  let e₁ : Election := {
    parties := {⟨"A"⟩, ⟨"B"⟩, ⟨"C"⟩, ⟨"D"⟩},
    votes := fun
      | ⟨"A"⟩ => 660
      | ⟨"B"⟩ => 670
      | ⟨"C"⟩ => 2450
      | ⟨"D"⟩ => 6220
      | _ => 0
    total_seats := 8
  }
  replace h_quota := h_quota e₁
  unfold is_quota_rule at h_quota
  have m_c_le_2 : rule e₁ ⟨"C"⟩ ≤ 2 := by
    have h_c := h_quota ⟨"C"⟩ (by decide)
    simp [e₁] at h_c
    norm_num at h_c
    grind
  have m_d_le_5 : rule e₁ ⟨"D"⟩ ≤ 5 := by
    have h_d := h_quota ⟨"D"⟩ (by decide)
    simp [e₁] at h_d
    norm_num at h_d
    grind
  have m_b_eq_1 : rule e₁ ⟨"B"⟩ = 1 := by
    have h_b := h_quota ⟨"B"⟩ (by decide)
    simp [e₁] at h_b
    norm_num at h_b
    rcases h_b with (m_b_eq_0 | m_b_eq_1)
    · have m_a_eq_1 : rule e₁ ⟨"A"⟩ = 0 := by
        sorry -- need another assumption
      have : ∑ p ∈ e₁.parties, rule e₁ p ≤ 7 := by
        grind
      sorry -- contradiction with total_seats := 8
    · assumption

  -- let e₂ =
  sorry
