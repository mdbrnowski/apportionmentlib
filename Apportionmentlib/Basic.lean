/-
Copyright (c) 2025 Michał Dobranowski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michał Dobranowski
-/
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Rat.Init

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

def Election.total_voters (election : Election) : ℕ :=
  ∑ p ∈ election.parties, election.votes p

def Apportionment : Type := Party -> ℕ
def Rule : Type := Election -> Apportionment

/-- A rule `r` is a quota rule if the number of seats allocated to each party `p` is either the
floor of its quota or the ceiling of its quota. -/
def is_quota_rule (rule : Rule) : Prop :=
  ∀ election : Election,
    let num_voters := election.total_voters
    ∀ p ∈ election.parties,
      let quota := (election.votes p * election.total_seats : ℚ) / (num_voters : ℚ)
      rule election p = quota.floor ∨ rule election p = quota.ceil

/-- A rule `r` is population monotone if when the number of votes for a party `p` increases, but the
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


#eval Party.mk "A"
