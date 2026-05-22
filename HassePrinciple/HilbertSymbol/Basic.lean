/-
Copyright (c) 2026b Nirvana Coppola, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nirvana Coppola, María Inés de Frutos-Fernández
-/
module

public import HassePrinciple.Padics.Legendre
public import Mathlib.Algebra.QuadraticAlgebra.Basic
public import Mathlib.NumberTheory.PrimeCounting
public import Mathlib.NumberTheory.LSeries.PrimesInAP

@[expose] public section

noncomputable section

namespace HilbertSymbol

-- k is a field and typically will be either ℝ or ℚ_p, but we need less for the definition.
variable {k : Type*} [Field k] --[DecidableEq k] --[CharZero k]

/-- TODO -/
noncomputable def _root_.HilbertSymbol (a b : k) : ℤ := by
  classical exact if a = 0 ∨ b = 0 then 0 else if ∃ z x y : k, (z, x, y) ≠ (0, 0, 0) ∧
  z ^ 2 - a * x ^ 2 - b * y ^ 2 = 0 then 1 else -1

--If a and b are nonzero, then the Hilbert Symbol is nonzero.
/-- TODO -/
lemma nonzero_of_nonzero (a b : k) (ha : a ≠ 0) (hb : b ≠ 0) : HilbertSymbol a b ≠ 0 := by
  rw [HilbertSymbol]
  split_ifs
  all_goals try linarith
  exfalso
  tauto

/-- TODO -/
lemma well_defined_up_to_squares (a b a' b' : k) : HilbertSymbol a b = HilbertSymbol
    (a * a'^2) (b * b'^2) := by
  sorry

/-- TODO -/
lemma comm (a b : k) : HilbertSymbol a b = HilbertSymbol b a := by
  sorry

/-
# Basic properties of the Hilbert symbol
-/

/-- TODO -/
def kb (b : k) := QuadraticAlgebra k b 0

--may make sense to split in two lemmas, one for kb=k and the other for kb≠k.
/-- TODO -/
theorem eq_one_iff (a b : k) (ha : a ≠ 0) (hb : b ≠ 0) : HilbertSymbol a b = 1 ↔ ∃ t : kb b, a =
    QuadraticAlgebra.norm t := by
  sorry


/-- TODO -/
theorem one_of_square (a c : k) (ha : a ≠ 0) (hc : c ≠ 0) : HilbertSymbol a (c ^ 2) = 1 := by
  sorry

/-- TODO -/
@[simp]
theorem one_of_neg_self (a : k) (ha : a ≠ 0) : HilbertSymbol a (-a) = 1 := by
  sorry

/-- TODO -/
theorem one_of_one_minus_self (a : k) (ha0 : a ≠ 0) (ha1 : a ≠ 1) :
    HilbertSymbol a (1 - a) = 1 := by
  sorry

/-- TODO -/
theorem of_mul (a a' b : k) (ha' : a' ≠ 0) (hab : HilbertSymbol a b = 1) : HilbertSymbol (a * a') b =
    HilbertSymbol a' b := by
  sorry

/-- TODO -/
@[simp]
theorem of_neg_mul (a b : k) : HilbertSymbol a (- (a * b)) = HilbertSymbol a b := by
  sorry

/-- TODO -/
theorem of_minus_self_mul (a b : k) (ha : a ≠ 1) :
    HilbertSymbol a ((1 - a) * b) = HilbertSymbol a b := by
  sorry

/-
# Local Properties --Computation of the Hilbert symbol in the real and p-adic cases
-/

/-- TODO -/
theorem real (a b : ℝ) (ha : a ≠ 0) (hb : b ≠ 0) : HilbertSymbol a b = if (0 : ℝ) < a ∨ (0 : ℝ) < b then 1 else -1 := by
  sorry

open Padic

/-- epsilon(u) is the class modulo 2 of (u-1)/2. -/
def epsilon (u : (PadicInt 2)ˣ) : ℤ :=
  if (u.val).appr 2 % 4 = 1 then 0 else 1

/-- omega(u) is the class modulo 2 of (u^2-1)/8. -/
def omega (u : (PadicInt 2)ˣ) : ℤ :=
  let u_mod_8 := (u.val).appr 3 % 8
  if u_mod_8 = 1 ∨ u_mod_8 = 7 then 0 else 1

--better name?
/-- TODO -/
private lemma exists_nontrivial_zero {p : ℕ} [hp : Fact (Nat.Prime p)] (v : (ℚ_[p])ˣ) (z x y : ℚ_[p])
    (hnontriv : (x, y, z) ≠ (0, 0, 0)) (hsol : z ^ 2 - p * x ^ 2 - v * y ^ 2 = 0) : ∃ z' y' :
    (ℚ_[p])ˣ, ∃ x' : ℤ_[p], (z' : ℚ_[p])^2 - p * (x' : ℚ_[p])^2 - v * (y' : ℚ_[p])^2 = 0 := by
  sorry


/-- TODO -/
lemma padic_odd_p_case00 {p : ℕ} [hp : Fact (Nat.Prime p)] (hp2 : p ≠ 2) (x y : (ℚ_[p]))
    (hx : x ≠ 0) (hy : y ≠ 0) (hα0 : x.valuation = 0) (hβ0 : y.valuation = 0) :
    HilbertSymbol x y = Int.negOnePow (x.valuation * y.valuation * epsilon (p2 hp2)) *
    legendreSym' (padicUnitPart (Units.mk0 x hx)) * legendreSym' (padicUnitPart (Units.mk0 y hy)) := by
  sorry

/-- TODO -/
lemma padic_odd_p_case10 {p : ℕ} [hp : Fact (Nat.Prime p)] (hp2 : p ≠ 2) (x y : (ℚ_[p])) (hx : x ≠ 0) (hy : y ≠ 0)
    (hα0 : valuation (x : ℚ_[p]) = 1) (hβ0 : valuation (y : ℚ_[p]) = 0) : HilbertSymbol x y =
    Int.negOnePow (valuation (x : ℚ_[p]) * valuation (y : ℚ_[p]) * epsilon (p2 hp2)) *
    legendreSym' (padicUnitPart (Units.mk0 x hx)) * legendreSym' (padicUnitPart (Units.mk0 y hy)) := by
  sorry

/-- TODO -/
lemma padic_odd_p_case11 {p : ℕ} [hp : Fact (Nat.Prime p)] (hp2 : p ≠ 2) (x y : (ℚ_[p])) (hx : x ≠ 0) (hy : y ≠ 0)
    (hα0 : valuation (x : ℚ_[p]) = 1) (hβ0 : valuation (y : ℚ_[p]) = 1) : HilbertSymbol x y =
    Int.negOnePow (valuation (x : ℚ_[p]) * valuation (y : ℚ_[p]) * epsilon (p2 hp2)) *
    legendreSym' (padicUnitPart (Units.mk0 x hx)) * legendreSym' (padicUnitPart (Units.mk0 y hy)) := by
  sorry

/-- TODO -/
theorem padic_odd_p {p : ℕ} [hp : Fact (Nat.Prime p)] (hp2 : p ≠ 2) (x y : (ℚ_[p])) (hx : x ≠ 0) (hy : y ≠ 0) :
    HilbertSymbol x y =
    Int.negOnePow (valuation (x : ℚ_[p]) * valuation (y : ℚ_[p]) * epsilon (p2 hp2)) *
    legendreSym' (padicUnitPart (Units.mk0 x hx)) * legendreSym' (padicUnitPart (Units.mk0 y hy)) := by
  sorry

/-- TODO -/
lemma padic_2_case00 (x y : (ℚ_[2])) (hx : x ≠ 0) (hy : y ≠ 0) (hα0 : valuation (x : ℚ_[2]) = 0)
    (hβ0 : valuation (y : ℚ_[2]) = 0) : HilbertSymbol x y =
    Int.negOnePow (epsilon (padicUnitPart (Units.mk0 x hx)) * epsilon (padicUnitPart (Units.mk0 y hy)) + valuation (x : ℚ_[2]) *
    omega (padicUnitPart (Units.mk0 y hy)) + valuation (y : ℚ_[2]) * omega (padicUnitPart (Units.mk0 x hx))) := by
  sorry

/-- TODO -/
lemma padic_2_case10 (x y : (ℚ_[2])) (hx : x ≠ 0) (hy : y ≠ 0) (hα0 : valuation (x : ℚ_[2]) = 1)
    (hβ0 : valuation (y : ℚ_[2]) = 0) : HilbertSymbol x y =
    Int.negOnePow (epsilon (padicUnitPart (Units.mk0 x hx)) * epsilon (padicUnitPart (Units.mk0 y hy)) + valuation (x : ℚ_[2]) *
    omega (padicUnitPart (Units.mk0 y hy)) + valuation (y : ℚ_[2]) * omega (padicUnitPart (Units.mk0 x hx))) := by
  sorry

/-- TODO -/
lemma padic_2_case11 (x y : (ℚ_[2])) (hx : x ≠ 0) (hy : y ≠ 0) (hα0 : valuation (x : ℚ_[2]) = 1)
    (hβ0 : valuation (y : ℚ_[2]) = 1) : HilbertSymbol x y =
    Int.negOnePow (epsilon (padicUnitPart (Units.mk0 x hx)) * epsilon (padicUnitPart (Units.mk0 y hy)) + valuation (x : ℚ_[2]) *
    omega (padicUnitPart (Units.mk0 y hy)) + valuation (y : ℚ_[2]) * omega (padicUnitPart (Units.mk0 x hx))) := by
  sorry

/-- TODO -/
theorem padic_2 (x y : (ℚ_[2])) (hx : x ≠ 0) (hy : y ≠ 0) : HilbertSymbol x y =
    Int.negOnePow (epsilon (padicUnitPart (Units.mk0 x hx)) * epsilon (padicUnitPart (Units.mk0 y hy)) + valuation (x : ℚ_[2]) *
    omega (padicUnitPart (Units.mk0 y hy)) + valuation (y : ℚ_[2]) * omega (padicUnitPart (Units.mk0 x hx))) := by
  sorry


-- do we need the bilinear form property? (see Theorem 2 and Cor.)
/-
# Global properties of the Hilbert symbol
-/
open Nat

/-- For a, b in ℚ, and for all places of ℚ, we define the Hilbert symbol of a and b at that
place. -/
def at_p (a b : ℚ) (p : ℕ) [hp : Fact (Nat.Prime p)] : ℤ := HilbertSymbol (a : ℚ_[p]) (b : ℚ_[p])

/-- TODO -/
def at_infty (a b : ℚ) : ℤ := HilbertSymbol (a : ℝ) (b : ℝ)

/-- TODO -/
instance fact_prime_nth_prime (n : ℕ) : Fact (Nat.Prime (Nat.nth Nat.Prime n)) := by
  rw [fact_iff]
  exact prime_nth_prime n

-- For all but finitely many primes p, the Hilbert symbol of a and b at p is 1.
/-- TODO -/
theorem almost_all_one (a b : ℚˣ) :
    ∃ (S : Finset ℕ), ∀ n , n ∉ S →
    HilbertSymbol.at_p a b (Nat.nth Nat.Prime n) = 1 := by
  sorry

/-- TODO -/
def hilbertSym_fun (a b : ℚˣ) : ℕ → ℤ := fun n => at_p a b (Nat.nth Nat.Prime n)

/-- TODO -/
def hilbertSym_support (a b : ℚˣ) : Finset ℕ := (almost_all_one a b).choose

/-- TODO -/
theorem product_formula (a b : ℚˣ) : HilbertSymbol.at_infty a b * ∏ (n ∈ hilbertSym_support a b),
    hilbertSym_fun a b n  = 1 := by
  sorry

end HilbertSymbol
