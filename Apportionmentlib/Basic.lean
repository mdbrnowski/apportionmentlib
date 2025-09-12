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

def Apportionment : Type := Party -> ℕ
def Election : Type := Party -> ℕ
def Rule : Type := Election -> ℕ -> Apportionment

/-- A rule `r` is a quota rule if the number of seats allocated to each party `p` is either the
floor of its quota or the ceiling of its quota. -/
def is_quota_rule (r : Rule) (parties : Finset Party) (election : Election) (num_seats : ℕ)
    : Prop :=
  let num_voters := ∑ p ∈ parties, election p
  ∀ p ∈ parties,
    let quota := (election p * num_seats : ℚ) / (num_voters : ℚ)
    let num_party_seats := r election num_seats p
    quota.floor ≤ num_party_seats ∧ num_party_seats ≤ quota.floor


#eval Party.mk "A"
