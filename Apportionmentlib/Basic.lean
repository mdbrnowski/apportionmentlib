/-
Copyright (c) 2025 Michał Dobranowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michał Dobranowski
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Dist
import Mathlib.Data.Rat.Init
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.NormNum

/-!
# Basic

We define basic notions related to apportionment methods, such as elections, apportionments,
apportionment rules, and properties of apportionment rules. We also prove the Balinski-Young
impossibility theorem.

All definitions follow those given in a textbook by F. Pukelsheim [Pukelsheim2017].

## Main definitions

* `Party`
* `Election`
* `Apportionment`
* `Rule`
* `IsAnonymous`
* `IsBalanced`
* `IsConcordant`
* `IsQuotaRule`
* `IsPopulationMonotone`

## Main statements

* `if_IsPopulationMonotone_then_IsConcordant`: anonymity and population monotonicity imply
  concordance.
* `balinski_young`: Balinski-Young impossibility theorem.

## Implementation details

Formally, we should use `p ∈ election.parties` everywhere, in addition to simply writing
`p : Party`, in the definitions of `IsAnonymous`, `IsPopulationMonotone`, etc. We omit this for
simplicity, as for now, since it has not been needed in any proof so far. This is not surprising, as
we define `Election.votes` with `| _ => 0`, so parties outside `election.parties` have no votes.

## References

* [F. Pukelsheim, *Proportional Representation: Apportionment Methods and Their Applications*
  ][Pukelsheim2017]
* [M. L. Balinski, H. P. Young, *Fair Representation: Meeting the Ideal of One Man, One Vote*
  ][BalinskiYoung1982]

-/

open BigOperators

/-- Party (or candidate, state, etc.) in an election. They are identified by their name. -/
structure Party where
  name : String
  deriving DecidableEq

instance : Repr Party where
  reprPrec p _ := s!"{p.name} : Party"

variable [Fintype Party]

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
abbrev Apportionment : Type := Party → ℕ

/-- An apportionment rule is a function that, given an election, returns a set of apportionments
satisfying three properties:
1. *Non-emptiness*: there is at least one apportionment returned;
2. *Inheritance of zeros*: parties with zero votes are allocated zero seats;
3. *House size feasibility*: the total number of seats allocated is equal to the house size. -/
structure Rule where
  res : Election → Finset Apportionment
  non_emptiness (election : Election) : (res election).Nonempty
  inheritance_of_zeros (election : Election) (p : Party) :
    election.votes p = 0 → ∀ App ∈ res election, App p = 0
  house_size_feasibility (election : Election) :
    ∀ App ∈ res election,
      ∑ p ∈ election.parties, App p = election.house_size

/-- A rule is *anonymous* if permuting the votes of the parties permutes the allocation of seats in
the same way. Informally, the names of the parties do not matter. -/
class IsAnonymous (rule : Rule) : Prop where
  anonymous (election : Election) (σ : Party → Party) (p q : Party) :
    (σ p = σ q → p = q) →
      let election' : Election := { parties := election.parties,
                                    votes := election.votes ∘ σ,
                                    house_size := election.house_size
                                  }
      rule.res election' = (rule.res election).image (· ∘ σ)

/-- A rule is *balanced* if whenever two parties `p` and `q` have the same number of votes, then
the difference in the number of seats allocated to them is at most one. -/
class IsBalanced (rule : Rule) : Prop where
  balanced (election : Election) (p q : Party) :
    election.votes p = election.votes q →
      ∀ App ∈ rule.res election,
        (App p).dist (App q) ≤ 1

/-- A rule is *concordant* if whenever party `p` has fewer votes than party `q`, then `p` is
allocated no more seats than `q`. -/
class IsConcordant (rule : Rule) : Prop where
  concordant (election : Election) (p q : Party) :
    election.votes p < election.votes q →
      ∀ App ∈ rule.res election,
        App p ≤ App q

/-- A rule is a *quota rule* if the number of seats allocated to each party `p` is either the floor
or the ceiling of its Hare-quota. -/
class IsQuotaRule (rule : Rule) : Prop where
  quota_rule (election : Election) (p : Party) :
    let quota := (election.votes p * election.house_size : ℚ) / (election.total_voters : ℚ)
    ∀ App ∈ rule.res election,
      App p = ⌊quota⌋ ∨ App p = ⌈quota⌉

/-- A rule is *population monotone* (or *vote ratio monotone*) if population paradoxes do not occur.
A population paradox occurs when the support for party `p` increases at a faster rate than that for
party `q`, but `p` loses seats while `q` gains seats. -/
class IsPopulationMonotone (rule : Rule) : Prop where
  population_monotonone (election₁ election₂ : Election) (p q : Party) :
    election₁.parties = election₂.parties ∧ election₁.house_size = election₂.house_size →
      -- p' support grows faster than q's (multiplying crosswise to avoid ℚ)
      election₂.votes p * election₁.votes q > election₂.votes q * election₁.votes p →
        ∀ App₁ ∈ rule.res election₁, ∀ App₂ ∈ rule.res election₂,
          ¬(App₁ p > App₂ p ∧ App₁ q < App₂ q)  -- p gets less seats, q gets more seats

/-- If an anonymous rule is population monotone, then it is concordant. -/
lemma if_IsPopulationMonotone_then_IsConcordant (rule : Rule) [h_anon : IsAnonymous rule]
    [h_mono : IsPopulationMonotone rule] : IsConcordant rule := by
  constructor
  intro e p q h_votes App h_App

  let σ := fun r ↦ -- swap parties p and q
    if r = p then q
    else if r = q then p
    else r

  set e' : Election := {
    parties := e.parties
    votes := e.votes ∘ σ
    house_size := e.house_size
  }
  let App' := App ∘ σ
  replace h_anon := h_anon.anonymous e σ p q (by grind)
  replace h_mono := h_mono.population_monotonone e e' p q (by trivial)
  have h_App' : App' ∈ rule.res e' := by grind
  have h_p' : e'.votes p = e.votes q := by grind
  have h_q' : e'.votes q = e.votes p := by grind
  rw [h_p', h_q', ←pow_two, ←pow_two] at h_mono
  specialize h_mono (Nat.pow_lt_pow_left h_votes (by decide)) App h_App App' h_App'
  grind

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
  obtain ⟨App, h_App⟩ := rule.non_emptiness e

  have m_c_le_2 : App ⟨"C"⟩ ≤ 2 := by
    have h_c := h_quota.quota_rule e ⟨"C"⟩
    simp [e] at h_c
    norm_num at h_c
    grind
  have m_d_le_5 : App ⟨"D"⟩ ≤ 5 := by
    have h_d := h_quota.quota_rule e ⟨"D"⟩
    simp [e] at h_d
    norm_num at h_d
    grind
  have m_b_eq_1 : App ⟨"B"⟩ = 1 := by
    have h_b := h_quota.quota_rule e ⟨"B"⟩ App h_App
    simp [e] at h_b
    norm_num at h_b
    rcases h_b with (m_b_eq_0 | m_b_eq_1)
    · have m_a_eq_1 : App ⟨"A"⟩ = 0 := by
        have m_a_le_m_b := h_concord.concordant e ⟨"A"⟩ ⟨"B"⟩ (by decide) App h_App
        linarith
      have : ∑ p ∈ e.parties, App p ≤ 7 := by
        simp [e]
        linarith [m_a_eq_1, m_b_eq_0, m_c_le_2, m_d_le_5]
      have : ∑ p ∈ e.parties, App p = 8 := by
        exact rule.house_size_feasibility e App h_App
      linarith
    · assumption

  -- We give an even stronger counterexample than needed: not only does B's support increase at a
  -- faster rate than D's, but D's support decreases while B's support increases.
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
  obtain ⟨App', h_App'⟩ := rule.non_emptiness e'

  have m_d_ge_6' : App' ⟨"D"⟩ ≥ 6 := by
    have h_d' := h_quota.quota_rule e' ⟨"D"⟩
    simp [e'] at h_d'
    norm_num at h_d'
    grind
  have m_b_eq_0' : App' ⟨"B"⟩ = 0 := by
    have h_b' := h_quota.quota_rule e' ⟨"B"⟩ App' h_App'
    simp [e'] at h_b'
    norm_num at h_b'
    rcases h_b' with (m_b_eq_0' | m_b_eq_1')
    · assumption
    · have m_a_ge_1' : App' ⟨"A"⟩ ≥ 1 := by
        have m_b_ge_m_a' := h_concord.concordant e' ⟨"B"⟩ ⟨"A"⟩ (by decide) App' h_App'
        linarith
      have m_c_ge_1' : App' ⟨"C"⟩ ≥ 1 := by
        have m_c_ge_m_b' := h_concord.concordant e' ⟨"B"⟩ ⟨"C"⟩ (by decide) App' h_App'
        linarith
      have : ∑ p ∈ e'.parties, App' p ≥ 9 := by
        simp [e']
        linarith [m_a_ge_1', m_b_eq_1', m_c_ge_1', m_d_ge_6']
      have : ∑ p ∈ e'.parties, App' p = 8 := by
        exact rule.house_size_feasibility e' App' h_App'
      linarith

  replace h_mono := h_mono.population_monotonone e e' ⟨"B"⟩ ⟨"D"⟩ (by trivial) (by decide)
    App h_App App' h_App'
  grind
