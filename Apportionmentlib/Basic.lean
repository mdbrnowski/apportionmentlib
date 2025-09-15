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

/-!
# Basic

We define basic notions related to apportionment methods, such as elections, apportionments,
apportionment rules, and properties of apportionment rules. We also prove the Balinski-Young
impossibility theorem.

Almost all definitions strictly follow the definitions given in the book by Pukelsheim
[Pukelsheim2017].

## Main definitions

* `Party`
* `Election`
* `Apportionment`
* `Rule`
* `IsAnonymous`
* `IsQuotaRule`
* `IsPopulationMonotone`
* `IsConcordant`

## Main statements

* `if_IsPopulationMonotone_then_IsConcordant`: anonymity and population monotonicity imply
  concordance.
* `balinski_young`: Balinski-Young impossibility theorem.

## References

* [F. Pukelsheim, *Proportional Representation*][Pukelsheim2017]

-/

open BigOperators

/-- Party (or candidate, state, etc.) in an election. They are identified by their name. -/
structure Party where
  name : String
  deriving DecidableEq

instance : Repr Party where
  reprPrec p _ := s!"{p.name} : Party"

/-- An election with a finite set of parties, a function giving the number of votes for each party,
and the total number of seats to be allocated. -/
structure Election where
  parties : Finset Party
  votes : Party → ℕ
  house_size : ℕ

@[simp]
def Election.total_voters (election : Election) : ℕ :=
  ∑ p ∈ election.parties, election.votes p

/-- An apportionment is a function from parties to the number of seats allocated to each party. -/
def Apportionment : Type := Party → ℕ

/-- An apportionment rule is a function that, given an election, returns an apportionment satisfying
the property called *house size feasibility*, i.e., the total number of seats allocated is equal to
the house size. -/
structure Rule where
  res : Election → Apportionment
  house_size_feasibility : ∀ election : Election,
    ∑ p ∈ election.parties, res election p = election.house_size

/-- A rule is *anonymous* if permuting the votes of the parties permutes the allocation of seats in
the same way. Informally, the names of the parties do not matter. -/
class IsAnonymous (rule : Rule) : Prop where
  anonymous : ∀ election : Election, ∀ σ : Party → Party,
    ∀ p ∈ election.parties, σ p ∈ election.parties →
      ∀ p ∈ election.parties, ∀ q ∈ election.parties, σ p = σ q → p = q →
        rule.res { parties := election.parties,
                   votes := fun p => election.votes (σ p),
                   house_size := election.house_size
                 } = fun p => rule.res election (σ p)

/-- A rule is a *quota rule* if the number of seats allocated to each party `p` is either the floor
or the ceiling of its Hare-quota. -/
class IsQuotaRule (rule : Rule) : Prop where
  quota_rule : ∀ election : Election,
    let num_voters := election.total_voters
    ∀ p ∈ election.parties,
      let quota := (election.votes p * election.house_size : ℚ) / (num_voters : ℚ)
      rule.res election p = ⌊quota⌋ ∨ rule.res election p = ⌈quota⌉

/-- A rule is *population monotone* (or *vote ratio monotone*) if population paradoxes do not occur.
Population paradox is a situation where support for party `p` increases and support for party `q`
decreases, but `p` loses a seat and `q` gains a seat. -/
class IsPopulationMonotone (rule : Rule) : Prop where
  population_monotonone : ∀ election₁ election₂ : Election,
    election₁.parties = election₂.parties ∧ election₁.house_size = election₂.house_size →
      ∀ p ∈ election₁.parties, ∀ q ∈ election₁.parties,
        election₁.votes p < election₂.votes p ∧ -- p get more votes
        election₁.votes q > election₂.votes q → -- q get less votes
          ¬(rule.res election₁ p > rule.res election₂ p ∧ -- p gets less seats
            rule.res election₁ q < rule.res election₂ q)  -- q gets more seats

/-- A rule is *concordant* if whenever party `p` has fewer votes than party `q`, then `p` is
allocated no more seats than `q`. -/
class IsConcordant (rule : Rule) : Prop where
  concordant : ∀ election : Election,
    ∀ p ∈ election.parties, ∀ q ∈ election.parties,
      election.votes p < election.votes q →
        rule.res election p ≤ rule.res election q

/-- If an anonymous rule is population monotone, then it is concordant. -/
lemma if_IsPopulationMonotone_then_IsConcordant (rule : Rule) [h_anon : IsAnonymous rule]
    [h_mono : IsPopulationMonotone rule] : IsConcordant rule := by
  constructor
  intro e p hp q hq h_votes

  let σ := fun r => -- swap parties p and q
    if r = p then q
    else if r = q then p
    else r

  set e' : Election := {
    parties := e.parties
    votes := fun p ↦ e.votes (σ p)
    house_size := e.house_size
  }

  replace h_mono := h_mono.population_monotonone e e' (by trivial) p hp q hq (by grind)
  replace h_anon := h_anon.anonymous e σ
  grind only [cases Or]

/-- Balinski-Young impossibility theorem: If an anonymous rule is a quota rule, then it is not
population monotone. Thus, no apportionment method can satisfy both properties simultaneously. -/
theorem balinski_young (rule : Rule) [IsAnonymous rule] [h_quota : IsQuotaRule rule] :
    ¬IsPopulationMonotone rule := by
  by_contra h_mono
  have h_concord := if_IsPopulationMonotone_then_IsConcordant rule

  let e : Election := {
    parties := {⟨"A"⟩, ⟨"B"⟩, ⟨"C"⟩, ⟨"D"⟩}
    votes := fun
      | ⟨"A"⟩ => 660
      | ⟨"B"⟩ => 670
      | ⟨"C"⟩ => 2450
      | ⟨"D"⟩ => 6220
      | _ => 0
    house_size := 8
  }
  have m_c_le_2 : rule.res e ⟨"C"⟩ ≤ 2 := by
    have h_c := h_quota.quota_rule e ⟨"C"⟩ (by decide)
    simp [e] at h_c
    norm_num at h_c
    grind
  have m_d_le_5 : rule.res e ⟨"D"⟩ ≤ 5 := by
    have h_d := h_quota.quota_rule e ⟨"D"⟩ (by decide)
    simp [e] at h_d
    norm_num at h_d
    grind
  have m_b_eq_1 : rule.res e ⟨"B"⟩ = 1 := by
    have h_b := h_quota.quota_rule e ⟨"B"⟩ (by decide)
    simp [e] at h_b
    norm_num at h_b
    rcases h_b with (m_b_eq_0 | m_b_eq_1)
    · have m_a_eq_1 : rule.res e ⟨"A"⟩ = 0 := by
        have m_a_le_m_b := h_concord.concordant e ⟨"A"⟩ (by decide) ⟨"B"⟩ (by decide) (by decide)
        linarith
      have : ∑ p ∈ e.parties, rule.res e p ≤ 7 := by
        simp [e]
        linarith [m_a_eq_1, m_b_eq_0, m_c_le_2, m_d_le_5]
      have : ∑ p ∈ e.parties, rule.res e p = 8 := by
        exact rule.house_size_feasibility e
      linarith
    · assumption

  let e' : Election := {
    parties := {⟨"A"⟩, ⟨"B"⟩, ⟨"C"⟩, ⟨"D"⟩}
    votes := fun
      | ⟨"A"⟩ => 680
      | ⟨"B"⟩ => 675
      | ⟨"C"⟩ => 700
      | ⟨"D"⟩ => 6200
      | _ => 0
    house_size := 8
  }
  have m_d_ge_6' : rule.res e' ⟨"D"⟩ ≥ 6 := by
    have h_d' := h_quota.quota_rule e' ⟨"D"⟩ (by decide)
    simp [e'] at h_d'
    norm_num at h_d'
    grind
  have m_b_eq_0' : rule.res e' ⟨"B"⟩ = 0 := by
    have h_b' := h_quota.quota_rule e' ⟨"B"⟩ (by decide)
    simp [e'] at h_b'
    norm_num at h_b'
    rcases h_b' with (m_b_eq_0' | m_b_eq_1')
    · assumption
    · have m_a_ge_1' : rule.res e' ⟨"A"⟩ ≥ 1 := by
        have m_b_ge_m_a' := h_concord.concordant e' ⟨"B"⟩ (by decide) ⟨"A"⟩ (by decide) (by decide)
        linarith
      have m_c_ge_1' : rule.res e' ⟨"C"⟩ ≥ 1 := by
        have m_c_ge_m_b' := h_concord.concordant e' ⟨"B"⟩ (by decide) ⟨"C"⟩ (by decide) (by decide)
        linarith
      have : ∑ p ∈ e'.parties, rule.res e' p ≥ 9 := by
        simp [e']
        linarith [m_a_ge_1', m_b_eq_1', m_c_ge_1', m_d_ge_6']
      have : ∑ p ∈ e'.parties, rule.res e' p = 8 := by
        exact rule.house_size_feasibility e'
      linarith
  replace h_mono := h_mono.population_monotonone e e' (by decide)
  have h_bd := h_mono ⟨"B"⟩ (by decide) ⟨"D"⟩ (by decide)
  grind
