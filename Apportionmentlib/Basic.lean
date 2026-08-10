/-
Copyright (c) 2025 Michał Dobranowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michał Dobranowski
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Dist
import Mathlib.Data.Rat.Floor
import ProofWidgets.Component.HtmlDisplay
import Apportionmentlib.Utils

/-!
# Basic

We define basic notions related to apportionment methods, such as elections, apportionments,
apportionment rules, and properties of apportionment rules. We also prove the Balinski-Young
impossibility theorem.

All definitions follow those given in a textbook by F. Pukelsheim [Pukelsheim2017]. Distinction
between weak and strong exactness is added, following [PalomaresPukelsheimRamirez2016].

## Main definitions

* `Election`
* `Election.quota`
* `Apportionment`
* `Rule`
* `IsAnonymous`
* `IsBalanced`
* `IsConcordant`
* `IsDecent`
* `IsExact`
* `IsQuotaRule`
* `IsPopulationMonotone`

## Main statements

* `Election.n_pos`: the number of parties in an election is positive.
* `IsConcordant_of_IsPopulationMonotone`: anonymity and population monotonicity imply concordance.
* `balinski_young`: Balinski-Young impossibility theorem, without anonymity (or any other property).

## References

* [M. L. Balinski, H. P. Young, *Fair Representation: Meeting the Ideal of One Man, One Vote*
  ][BalinskiYoung1982]
* [P. Gölz, D. Peters, A. D. Procaccia, *In This Apportionment Lottery, the House Always Wins*
  ][GoelzPetersProcaccia2025]
* [A. Palomares, F. Pukelsheim, J. A. Ramírez, *The whole and its parts: On the coherence theorem of
  Balinski and Young*][PalomaresPukelsheimRamirez2016]
* [F. Pukelsheim, *Proportional Representation: Apportionment Methods and Their Applications*
  ][Pukelsheim2017]

-/

open BigOperators ProofWidgets
open Lean (Json)

namespace Apportionmentlib

/-- An election with a vector of votes for `n` parties and the total number of seats to be
allocated. -/
structure Election (n : ℕ) where
  /-- The number of votes cast for each of the `n` parties, at the corresponding index. -/
  votes : Vector ℕ n
  /-- The number of seats to be allocated between the parties. -/
  houseSize : ℕ+
  /-- At least one vote is cast, so that the standard quotas are well defined. -/
  votes_sum_pos : 0 < votes.sum
  deriving DecidableEq

instance {n : ℕ} : Repr (Election n) where
  reprPrec e _ :=
    "[" ++ repr e.houseSize ++ "; " ++ repr e.votes.toList ++ "]"

/-- Notation for an election with a literal house size and vote distribution, as in
`election![8; [66, 67, 245, 622]]`. -/
macro "election![" seats:term ";" "[" votes:term,* "]" "]" : term =>
  `(Apportionmentlib.Election.mk #v[$votes,*] $seats (by decide))

/-- Party `i`'s standard (Hare) quota: its proportional share of the house size. -/
def Election.quota {n : ℕ} (e : Election n) (i : Fin n) : ℚ :=
  (e.votes[i] * e.houseSize : ℚ) / e.votes.sum

private def Election.toHtml {n : ℕ} (e : Election n) : Html :=
  let indices := List.range n
  let votesList := e.votes.toList
  let houseSize := e.houseSize
  let total := votesList.sum
  let thStyle := Json.mkObj [
    ("border", Json.str "1px solid"),
    ("padding", Json.str "6px"),
    ("textAlign", Json.str "center")
  ]
  let tdStyle := Json.mkObj [
    ("border", Json.str "1px solid"),
    ("padding", Json.str "6px"),
    ("textAlign", Json.str "center"),
    ("fontFamily", Json.str "monospace")
  ]
  let tableStyle := Json.mkObj [
    ("borderCollapse", Json.str "collapse"),
  ]
  let th (s : String) := Html.element "th" #[("style", thStyle)] #[Html.text s]
  let td (s : String) := Html.element "td" #[("style", tdStyle)] #[Html.text s]
  let row1 := Html.element "tr" #[] <|
    ([th "id"] ++ indices.map (fun i => th (toString i)) ++ [th "Σ"]).toArray
  let row2 := Html.element "tr" #[] <|
    ([th "votes"] ++ votesList.map (fun v => td (toString v)) ++ [td s!"{total}"]).toArray
  let row3 := Html.element "tr" #[] <|
    ([th "quota"] ++ (List.finRange n).map (fun i => td (formatRat4 (e.quota i))) ++
     [td s!"{houseSize.val}"]).toArray
  Html.element "table" #[("style", tableStyle)] #[Html.element "tbody" #[] #[row1, row2, row3]]

/-- This instance enables rendering of elections using the `#html` command. For example,
```lean
#html election![8; [66, 67, 245, 622]]
```
-/
instance {n : ℕ} : HtmlEval (Election n) where
  eval e := pure e.toHtml

/-- Create a new election by permuting the vote distribution of parties according to permutation
`σ`. -/
@[simp]
def Election.mkByPerm {n : ℕ} (election : Election n) (σ : Equiv.Perm (Fin n)) : Election n :=
  { votes := Vector.ofFn fun i => election.votes[σ i]
    houseSize := election.houseSize
    votes_sum_pos := by
      have := election.votes_sum_pos
      simp only [sum_pos_iff_exists_pos, Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta] at this ⊢
      obtain ⟨i, hi⟩ := this
      use σ.symm i
      simpa
  }

/-- Create a new election by scaling all votes by a positive constant `k`. -/
@[simp]
def Election.mkByScale {n : ℕ} (election : Election n) (k : ℕ+) : Election n :=
  { votes := Vector.ofFn fun i => k * election.votes[i]
    houseSize := election.houseSize
    votes_sum_pos := by
      have := election.votes_sum_pos
      simpa [sum_pos_iff_exists_pos]
  }

/-- The number of parties in an election is positive. -/
lemma Election.n_pos {n : ℕ} (election : Election n) : 0 < n := by
  have : n ≠ 0 := by
    by_contra hn
    rw [hn] at election
    simpa [Vector.eq_empty] using election.votes_sum_pos
  exact Nat.pos_of_ne_zero this

/-- An apportionment is a vector of natural numbers representing the number of seats allocated to
each party (at the corresponding index). -/
abbrev Apportionment (n : ℕ) : Type := Vector ℕ n

instance {n : ℕ} : Repr (Apportionment n) where
  reprPrec e _ := "#v" ++ repr e.toList

/-- An apportionment rule is a function that, given an election, returns a set of apportionments
satisfying three properties:
1. *Non-emptiness*: there is at least one apportionment returned;
2. *Inheritance of zeros*: parties with zero votes are allocated zero seats;
3. *House size feasibility*: the total number of seats allocated is equal to the house size. -/
structure Rule where
  /-- The set of apportionments that the rule returns for a given election. -/
  res : {n : ℕ} → Election n → Finset (Apportionment n)
  non_emptiness {n : ℕ} (election : Election n) : (res election).Nonempty
  inheritance_of_zeros {n : ℕ} (election : Election n) (i : Fin n) :
    election.votes[i] = 0 → ∀ App ∈ res election, App[i] = 0
  house_size_feasibility {n : ℕ} (election : Election n) :
    ∀ App ∈ res election, App.sum = election.houseSize

/-- A rule is *anonymous* if permuting the votes of the parties permutes the allocation of seats in
the same way. -/
class IsAnonymous (rule : Rule) : Prop where
  anonymous {n : ℕ} (election : Election n) (σ : Equiv.Perm (Fin n)) :
    let election' : Election n := election.mkByPerm σ
    ∀ App, App ∈ rule.res election' ↔
      ∃ App' ∈ rule.res election, ∀ i, App[i] = App'[σ i]

/-- A rule is *balanced* if whenever two parties have the same number of votes, then the difference
in the number of seats allocated to them is at most one. -/
class IsBalanced (rule : Rule) : Prop where
  balanced {n : ℕ} (election : Election n) (i j : Fin n) :
    election.votes[i] = election.votes[j] →
      ∀ App ∈ rule.res election, App[i].dist App[j] ≤ 1

/-- A rule is *concordant* if whenever one party has fewer votes than another, then it is allocated
no more seats than that other party. -/
class IsConcordant (rule : Rule) : Prop where
  concordant {n : ℕ} (election : Election n) (i j : Fin n) :
    election.votes[i] < election.votes[j] →
      ∀ App ∈ rule.res election, App[i] ≤ App[j]

/-- A rule is *decent* if scaling the number of votes for each party by the same positive integer
does not change the apportionment. -/
class IsDecent (rule : Rule) : Prop where
  decent {n : ℕ} (election : Election n) (k : ℕ+) :
    let election' : Election n := election.mkByScale k
    rule.res election' = rule.res election

/-- A rule is *weakly exact* if every `Apportionment`, when viewed as an input vote distribution
`Election.votes`, is reproduced as the unique solution. -/
class IsExact (rule : Rule) : Prop where
  exact {n : ℕ} (election : Election n) :
    -- ∀ App ∈ rule.res election
    ∀ App : Apportionment n, (hApp : App ∈ rule.res election) →
      let election' : Election n := {
        votes := App
        houseSize := election.houseSize
        votes_sum_pos := by
          rw [rule.house_size_feasibility (n := n) election App hApp]
          exact election.houseSize.pos
      }
      rule.res election' = {App}

/-- A rule is a *quota rule* if the number of seats allocated to each party is either the floor or
the ceiling of its Hare-quota. -/
class IsQuotaRule (rule : Rule) : Prop where
  quota_rule {n : ℕ} (election : Election n) (i : Fin n) :
    ∀ App ∈ rule.res election, App[i] = ⌊election.quota i⌋ ∨ App[i] = ⌈election.quota i⌉

/-- A quota rule allocates at most `m` seats to party `i` whenever its quota is at most `m`. -/
lemma Rule.seats_le (rule : Rule) [h_quota : IsQuotaRule rule] {n : ℕ} (election : Election n)
    (i : Fin n) (m : ℕ) (h : election.quota i ≤ m) :
    ∀ App ∈ rule.res election, App[i] ≤ m := by
  intro App h_App
  have h_quota := h_quota.quota_rule election i App h_App
  have h_ceil : ⌈election.quota i⌉ ≤ m := Int.ceil_le.mpr h
  have h_floor := Int.floor_le_ceil (election.quota i)
  rcases h_quota <;> omega

/-- A quota rule allocates at least `m` seats to party `i` whenever its quota is at least `m`. -/
lemma Rule.le_seats (rule : Rule) [h_quota : IsQuotaRule rule] {n : ℕ} (election : Election n)
    (i : Fin n) (m : ℕ) (h : (m : ℚ) ≤ election.quota i) :
    ∀ App ∈ rule.res election, m ≤ App[i] := by
  intro App h_App
  have h_quota := h_quota.quota_rule election i App h_App
  have h_floor : m ≤ ⌊election.quota i⌋ := Int.le_floor.mpr h
  have h_ceil := Int.floor_le_ceil (election.quota i)
  rcases h_quota <;> omega

/-- A rule is *population monotone* (or *vote ratio monotone*) if population paradoxes do not occur.
A population paradox occurs when the support for party `i` increases at a faster rate than that for
party `j`, but `i` loses seats while `j` gains seats. -/
class IsPopulationMonotone (rule : Rule) : Prop where
  population_monotone {n : ℕ} (election₁ election₂ : Election n) (i j : Fin n) :
    election₁.houseSize = election₂.houseSize →
      -- i's support grows faster than j's (multiplying crosswise to avoid ℚ)
      election₂.votes[i] * election₁.votes[j] > election₂.votes[j] * election₁.votes[i] →
        ∀ App₁ ∈ rule.res election₁, ∀ App₂ ∈ rule.res election₂,
          -- i gets less seats, j gets more seats
          ¬(App₁[i] > App₂[i] ∧ App₁[j] < App₂[j])

/-- If an anonymous rule is population monotone, then it is concordant. -/
lemma IsConcordant_of_IsPopulationMonotone (rule : Rule) [h_anon : IsAnonymous rule]
    [h_mono : IsPopulationMonotone rule] : IsConcordant rule := by
  constructor
  intro n e i j h_votes App h_App
  let σ : Equiv.Perm (Fin n) := Equiv.swap i j
  let e' : Election n := e.mkByPerm σ
  let App' := Vector.ofFn fun r => App[σ r]
  replace h_anon := h_anon.anonymous e σ App'
  have h_App' : App' ∈ rule.res e' := by
    rw [h_anon]
    use App
    exact ⟨h_App, by aesop⟩
  have h_p' : e'.votes[i] = e.votes[j] := by aesop
  have h_q' : e'.votes[j] = e.votes[i] := by aesop
  replace h_mono := h_mono.population_monotone e e' i j (by trivial)
  rw [h_p', h_q', ← pow_two, ← pow_two] at h_mono
  specialize h_mono (Nat.pow_lt_pow_left h_votes (by decide)) App h_App App' h_App'
  aesop

-- The witness for `balinski_young`, all of it private to that proof: a chain of eight elections
-- with four parties and twelve seats, in two regimes. Without anonymity the symmetric second case
section BalinskiYoung

-- The proof writes `App[0]`, ..., `App[3]` hundreds of times; discharging each index bound with
-- `decide` instead of the default tactic is way faster.
local macro_rules | `(tactic| get_elem_tactic_extensible) => `(tactic| decide)

variable (rule : Rule) {a b c : ℕ} {App : Apportionment 4}

/-- A *large* election: party `0` holds 72 of the 96 votes, the other three sharing `a + b + c = 24`
between them. Party `0`'s quota is then exactly `12 * 72 / 96 = 9`. -/
private def large (a b c : ℕ) : Election 4 :=
  { votes := #v[72, a, b, c], houseSize := 12, votes_sum_pos := by simp }

/-- A *small* election: party `0` holds 71 of the 85 votes, the other three sharing `a + b + c = 14`
between them. Party `0`'s quota is then `12 * 71 / 85 = 852 / 85`, between 10 and 11. -/
private def small (a b c : ℕ) : Election 4 :=
  { votes := #v[71, a, b, c], houseSize := 12, votes_sum_pos := by simp }

/-- The votes of a large election add up to 96. -/
private lemma large_votes_sum (h : a + b + c = 24) : (large a b c).votes.sum = 96 := by
  rw [Vector.sum_four]
  change 72 + a + b + c = 96
  omega

/-- The votes of a small election add up to 85. -/
private lemma small_votes_sum (h : a + b + c = 14) : (small a b c).votes.sum = 85 := by
  rw [Vector.sum_four]
  change 71 + a + b + c = 85
  omega

/-- The seats of the four parties add up 12. -/
private lemma seats_sum {e : Election 4} (h : (e.houseSize : ℕ) = 12)
    (h_App : App ∈ rule.res e) : App[0] + App[1] + App[2] + App[3] = 12 := by
  rw [← Vector.sum_four, rule.house_size_feasibility e App h_App, h]

variable [IsQuotaRule rule]

/-- Quota gives party `0` exactly 9 of the 12 seats of a large election, leaving 3 to be shared by
the other three parties. -/
private lemma large_seats (h_App : App ∈ rule.res (large a b c)) (h : a + b + c = 24 := by decide) :
    App[0] = 9 ∧ App[1] + App[2] + App[3] = 3 := by
  have h_le : App[0] ≤ 9 := rule.seats_le (large a b c) 0 9
    (by rw [Election.quota, large_votes_sum h]; norm_num [large]) App h_App
  have h_ge : 9 ≤ App[0] := rule.le_seats (large a b c) 0 9
    (by rw [Election.quota, large_votes_sum h]; norm_num [large]) App h_App
  have h_sum := seats_sum rule (e := large a b c) rfl h_App
  omega

/-- Quota gives party `0` at least 10 of the 12 seats of a small election, leaving at most 2 to be
shared by the other three parties. -/
private lemma small_seats (h_App : App ∈ rule.res (small a b c)) (h : a + b + c = 14 := by decide) :
    10 ≤ App[0] ∧ App[1] + App[2] + App[3] ≤ 2 := by
  have h_ge : 10 ≤ App[0] := rule.le_seats (small a b c) 0 10
    (by rw [Election.quota, small_votes_sum h]; norm_num [small]) App h_App
  have h_sum := seats_sum rule (e := small a b c) rfl h_App
  omega

/-- A party holding 16 of the 96 votes of a large election has quota exactly 2. -/
private lemma large_two_seats (i : Fin 4) (h_App : App ∈ rule.res (large a b c))
    (h : a + b + c = 24 := by decide) (h_votes : (large a b c).votes[i] = 16 := by decide) :
    App[i] = 2 := by
  have h_le := rule.seats_le (large a b c) i 2
    (by rw [Election.quota, h_votes, large_votes_sum h]; norm_num [large]) App h_App
  have h_ge := rule.le_seats (large a b c) i 2
    (by rw [Election.quota, h_votes, large_votes_sum h]; norm_num [large]) App h_App
  omega

/-- A party holding 8 of the 85 votes of a small election has quota `96 / 85 > 1`. -/
private lemma small_one_seat (i : Fin 4) (h_App : App ∈ rule.res (small a b c))
    (h : a + b + c = 14 := by decide) (h_votes : (small a b c).votes[i] = 8 := by decide) :
    1 ≤ App[i] :=
  rule.le_seats (small a b c) i 1
    (by rw [Election.quota, h_votes, small_votes_sum h]; norm_num [small]) App h_App

/-- Party `0` holds 9 seats in a large election but at least 10 in a small one, while its own votes
drop from 72 to 71. Population monotonicity then forbids a party whose votes do not drop from
losing a seat. -/
private lemma seats_le_of_votes_le (h_mono : IsPopulationMonotone rule) {a' b' c' : ℕ}
    {AppL AppS : Apportionment 4} (i : Fin 4) (h_AppL : AppL ∈ rule.res (large a b c))
    (h_AppS : AppS ∈ rule.res (small a' b' c'))
    (hl : a + b + c = 24 := by decide) (hs : a' + b' + c' = 14 := by decide)
    (h_pos : 0 < (small a' b' c').votes[i] := by decide)
    (h_votes : (large a b c).votes[i] ≤ (small a' b' c').votes[i] := by decide) :
    AppL[i] ≤ AppS[i] := by
  have h_ratio : (small a' b' c').votes[i] * (large a b c).votes[(0 : Fin 4)] >
      (small a' b' c').votes[(0 : Fin 4)] * (large a b c).votes[i] := by
    change (small a' b' c').votes[i] * 72 > 71 * (large a b c).votes[i]
    omega
  have h_par := h_mono.population_monotone (large a b c) (small a' b' c') i 0 rfl h_ratio
    AppL h_AppL AppS h_AppS
  have hL : AppL[(0 : Fin 4)] = 9 := (large_seats rule h_AppL hl).1
  have hS : 10 ≤ AppS[(0 : Fin 4)] := (small_seats rule h_AppS hs).1
  omega

/-- Balinski-Young impossibility theorem: a quota rule is never population monotone, so no
apportionment method can satisfy both properties simultaneously. Anonymity is not assumed (nor any
other property).

Gölz, Peters and Procaccia [GoelzPetersProcaccia2025] prove this for five or more parties, leaving
four open in this generality; the witness used here has only four parties, settling that case. -/
theorem balinski_young : ¬IsPopulationMonotone rule := by
  by_contra h_mono
  -- `A = (72, 16, 4, 4)`: parties 0 and 1 take 9 and 2 seats, so one of parties 2 and 3 takes the
  -- last one. The two chains refuting the two choices are mirror images in parties 2 and 3.
  obtain ⟨A, hA⟩ := rule.non_emptiness (large 16 4 4)
  have hA1 : A[1] = 2 := large_two_seats rule 1 hA
  have hA123 : A[1] + A[2] + A[3] = 3 := (large_seats rule hA).2
  rcases (show A[2] = 1 ∨ A[3] = 1 by omega) with hA2 | hA3
  · -- `P = (71, 2, 4, 8)`: party 2 keeps its seat, party 3's quota exceeds 1; party 1 gets none.
    obtain ⟨P, hP⟩ := rule.non_emptiness (small 2 4 8)
    have hP2 : A[2] ≤ P[2] := seats_le_of_votes_le rule h_mono 2 hA hP
    have hP3 : 1 ≤ P[3] := small_one_seat rule 3 hP
    have hP1 : P[1] = 0 := by have := (small_seats rule hP).2; omega
    -- `B = (72, 2, 16, 6)`: party 1 has nothing in `P`, party 2 has quota 2; party 3 takes one.
    obtain ⟨B, hB⟩ := rule.non_emptiness (large 2 16 6)
    have hB1 : B[1] ≤ P[1] := seats_le_of_votes_le rule h_mono 1 hB hP
    have hB2 : B[2] = 2 := large_two_seats rule 2 hB
    have hB3 : B[3] = 1 := by have := (large_seats rule hB).2; omega
    -- `Q = (71, 4, 4, 6)`: parties 2 and 3 keep the seats they hold in `A` and `B`.
    obtain ⟨Q, hQ⟩ := rule.non_emptiness (small 4 4 6)
    have hQ2 : A[2] ≤ Q[2] := seats_le_of_votes_le rule h_mono 2 hA hQ
    have hQ3 : B[3] ≤ Q[3] := seats_le_of_votes_le rule h_mono 3 hB hQ
    have hQ1 : Q[1] = 0 := by have := (small_seats rule hQ).2; omega
    -- `C = (72, 4, 16, 4)`: party 1 has nothing in `Q`, party 2 has quota 2; party 3 takes one.
    obtain ⟨C, hC⟩ := rule.non_emptiness (large 4 16 4)
    have hC1 : C[1] ≤ Q[1] := seats_le_of_votes_le rule h_mono 1 hC hQ
    have hC2 : C[2] = 2 := large_two_seats rule 2 hC
    have hC3 : C[3] = 1 := by have := (large_seats rule hC).2; omega
    -- `R = (71, 8, 2, 4)`: party 3 keeps its seat, party 1's quota exceeds 1; party 2 gets none.
    obtain ⟨R, hR⟩ := rule.non_emptiness (small 8 2 4)
    have hR3 : C[3] ≤ R[3] := seats_le_of_votes_le rule h_mono 3 hC hR
    have hR1 : 1 ≤ R[1] := small_one_seat rule 1 hR
    have hR2 : R[2] = 0 := by have := (small_seats rule hR).2; omega
    -- `D = (72, 6, 2, 16)`: party 2 has nothing in `R`, party 3 has quota 2; party 1 takes one.
    obtain ⟨D, hD⟩ := rule.non_emptiness (large 6 2 16)
    have hD2 : D[2] ≤ R[2] := seats_le_of_votes_le rule h_mono 2 hD hR
    have hD3 : D[3] = 2 := large_two_seats rule 3 hD
    have hD1 : D[1] = 1 := by have := (large_seats rule hD).2; omega
    -- `S = (71, 6, 4, 4)`: parties 3 and 1 keep the seats they hold in `C` and `D`.
    obtain ⟨S, hS⟩ := rule.non_emptiness (small 6 4 4)
    have hS3 : C[3] ≤ S[3] := seats_le_of_votes_le rule h_mono 3 hC hS
    have hS1 : D[1] ≤ S[1] := seats_le_of_votes_le rule h_mono 1 hD hS
    have hS2 : S[2] = 0 := by have := (small_seats rule hS).2; omega
    -- the contradiction
    have : A[2] ≤ S[2] := seats_le_of_votes_le rule h_mono 2 hA hS
    omega
  · -- The mirror image of the chain above, with parties 2 and 3 swapped throughout.
    obtain ⟨P, hP⟩ := rule.non_emptiness (small 2 8 4)
    have hP3 : A[3] ≤ P[3] := seats_le_of_votes_le rule h_mono 3 hA hP
    have hP2 : 1 ≤ P[2] := small_one_seat rule 2 hP
    have hP1 : P[1] = 0 := by have := (small_seats rule hP).2; omega
    obtain ⟨B, hB⟩ := rule.non_emptiness (large 2 6 16)
    have hB1 : B[1] ≤ P[1] := seats_le_of_votes_le rule h_mono 1 hB hP
    have hB3 : B[3] = 2 := large_two_seats rule 3 hB
    have hB2 : B[2] = 1 := by have := (large_seats rule hB).2; omega
    obtain ⟨Q, hQ⟩ := rule.non_emptiness (small 4 6 4)
    have hQ3 : A[3] ≤ Q[3] := seats_le_of_votes_le rule h_mono 3 hA hQ
    have hQ2 : B[2] ≤ Q[2] := seats_le_of_votes_le rule h_mono 2 hB hQ
    have hQ1 : Q[1] = 0 := by have := (small_seats rule hQ).2; omega
    obtain ⟨C, hC⟩ := rule.non_emptiness (large 4 4 16)
    have hC1 : C[1] ≤ Q[1] := seats_le_of_votes_le rule h_mono 1 hC hQ
    have hC3 : C[3] = 2 := large_two_seats rule 3 hC
    have hC2 : C[2] = 1 := by have := (large_seats rule hC).2; omega
    obtain ⟨R, hR⟩ := rule.non_emptiness (small 8 4 2)
    have hR2 : C[2] ≤ R[2] := seats_le_of_votes_le rule h_mono 2 hC hR
    have hR1 : 1 ≤ R[1] := small_one_seat rule 1 hR
    have hR3 : R[3] = 0 := by have := (small_seats rule hR).2; omega
    obtain ⟨D, hD⟩ := rule.non_emptiness (large 6 16 2)
    have hD3 : D[3] ≤ R[3] := seats_le_of_votes_le rule h_mono 3 hD hR
    have hD2 : D[2] = 2 := large_two_seats rule 2 hD
    have hD1 : D[1] = 1 := by have := (large_seats rule hD).2; omega
    obtain ⟨S, hS⟩ := rule.non_emptiness (small 6 4 4)
    have hS2 : C[2] ≤ S[2] := seats_le_of_votes_le rule h_mono 2 hC hS
    have hS1 : D[1] ≤ S[1] := seats_le_of_votes_le rule h_mono 1 hD hS
    have hS3 : S[3] = 0 := by have := (small_seats rule hS).2; omega
    have : A[3] ≤ S[3] := seats_le_of_votes_le rule h_mono 3 hA hS
    omega

end BalinskiYoung

end Apportionmentlib
