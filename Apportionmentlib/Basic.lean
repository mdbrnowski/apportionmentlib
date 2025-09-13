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
def Rule : Type :=
  (election : Election) → {apportionment : Apportionment //
    ∑ p ∈ election.parties, apportionment p = election.total_seats
  }

/-- A rule is a quota rule if the number of seats allocated to each party `p` is either the floor
or the ceiling of its quota. -/
def isQuotaRule (rule : Rule) : Prop :=
  ∀ election : Election,
    let num_voters := election.total_voters
    ∀ p ∈ election.parties,
      let quota := (election.votes p * election.total_seats : ℚ) / (num_voters : ℚ)
      (rule election).val p = ⌊quota⌋ ∨ (rule election).val p = ⌈quota⌉

/-- A rule is population monotone if population paradoxes do not occur. Population paradox is a
situation where support for party `p` increases and support for party `q` decreases, but `p` loses a
seat and `q` gains a seat. -/
def isPopulationMonotone (rule : Rule) : Prop :=
  ∀ election₁ election₂ : Election,
    election₁.parties = election₂.parties ∧
    election₁.total_seats = election₂.total_seats →
    ∀ p ∈ election₁.parties,
      ∀ q ∈ election₁.parties,
        election₁.votes p < election₂.votes p ∧ -- p get more votes
        election₁.votes q > election₂.votes q → -- q get less votes
        ¬((rule election₁).val p > (rule election₂).val p ∧ -- p gets less seats
          (rule election₁).val q < (rule election₂).val q)  -- q gets more seats


/-- Balinski-Young theorem: If a rule is a quota rule, then it is not population monotone. Thus, no
apportionment method can satisfy both properties simultaneously. -/
theorem balinski_young (rule : Rule) : isQuotaRule rule → ¬isPopulationMonotone rule := by
  intro h_quota
  unfold isQuotaRule at h_quota

  let e : Election := {
    parties := {⟨"A"⟩, ⟨"B"⟩, ⟨"C"⟩, ⟨"D"⟩},
    votes := fun
      | ⟨"A"⟩ => 660
      | ⟨"B"⟩ => 670
      | ⟨"C"⟩ => 2450
      | ⟨"D"⟩ => 6220
      | _ => 0
    total_seats := 8
  }
  have m_c_le_2 : (rule e).val ⟨"C"⟩ ≤ 2 := by
    have h_c := h_quota e ⟨"C"⟩ (by decide)
    simp [e] at h_c
    norm_num at h_c
    grind
  have m_d_le_5 : (rule e).val ⟨"D"⟩ ≤ 5 := by
    have h_d := h_quota e ⟨"D"⟩ (by decide)
    simp [e] at h_d
    norm_num at h_d
    grind
  have m_b_eq_1 : (rule e).val ⟨"B"⟩ = 1 := by
    have h_b := h_quota e ⟨"B"⟩ (by decide)
    simp [e] at h_b
    norm_num at h_b
    rcases h_b with (m_b_eq_0 | m_b_eq_1)
    · have m_a_eq_1 : (rule e).val ⟨"A"⟩ = 0 := by
        sorry -- need another assumption
      have : ∑ p ∈ e.parties, (rule e).val p ≤ 7 := by
        simp [e]
        linarith [m_a_eq_1, m_b_eq_0, m_c_le_2, m_d_le_5]
      have : ∑ p ∈ e.parties, (rule e).val p = 8 := by
        exact (rule e).property
      linarith
    · assumption

  let e' : Election := {
    parties := {⟨"A"⟩, ⟨"B"⟩, ⟨"C"⟩, ⟨"D"⟩},
    votes := fun
      | ⟨"A"⟩ => 680
      | ⟨"B"⟩ => 675
      | ⟨"C"⟩ => 700
      | ⟨"D"⟩ => 6200
      | _ => 0
    total_seats := 8
  }
  have m_d_ge_6' : (rule e').val ⟨"D"⟩ ≥ 6 := by
    have h_d' := h_quota e' ⟨"D"⟩ (by decide)
    simp [e', Election.total_voters] at h_d'
    norm_num at h_d'
    grind
  have m_b_eq_0' : (rule e').val ⟨"B"⟩ = 0 := by
    sorry

  by_contra h_population
  replace h_population := h_population e e' (by decide)
  have h_bd := h_population ⟨"B"⟩ (by decide) ⟨"D"⟩ (by decide)
  grind
