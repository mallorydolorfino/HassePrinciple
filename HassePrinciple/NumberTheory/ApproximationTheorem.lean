/-
Copyright (c) 2026 Nirvana Coppola, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nirvana Coppola, María Inés de Frutos-Fernández
-/
module

public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.NumberTheory.PrimeCounting

/-! # Approximation theorem. -/

@[expose] public section


noncomputable section

namespace Rat


/-- TODO -/
local instance fact_prime_nth_prime (n : ℕ) : Fact (Nat.Prime (Nat.nth Nat.Prime n)) := by
  rw [fact_iff]
  exact Nat.prime_nth_prime n

open Padic

-- TODO: rename
/- Since the proof concerns with the case where ℝ is part of the product, we assume it here
from the beginning. We can also do a different version if needed. -/
/-- TODO -/
abbrev prodOverS (S : Finset ℕ) := ℝ × (Π n : S, ℚ_[Nat.nth Nat.Prime n])

-- I tried a concrete version without using topology. Can reformulate with sup if needed.
/-- TODO -/
theorem approximation' {S : Finset ℕ} {ε : ℝ} (hε : ε > 0) (y : prodOverS S) :
    ∃ x : ℚ, ‖y.1 - x‖ + Finset.sum (Finset.attach S) (fun n ↦ ‖y.2 n - x‖) < ε := by
  sorry

/-- TODO -/
def finiteEmbedding (S : Finset ℕ) (x : ℚ) : prodOverS S :=
  ⟨algebraMap ℚ ℝ x, fun n ↦ (algebraMap ℚ ℚ_[Nat.nth Nat.Prime n]) x⟩

theorem approximation (S : Finset ℕ) :
    Dense (Set.range (finiteEmbedding S)) := by
  sorry

end Rat
