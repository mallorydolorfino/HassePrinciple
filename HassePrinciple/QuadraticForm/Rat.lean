/-
Copyright (c) 2026 Nirvana Coppola, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nirvana Coppola, María Inés de Frutos-Fernández
-/
module

public import HassePrinciple.QuadraticForm.Basic
public import Mathlib.Algebra.CharP.Invertible
public import Mathlib.Analysis.RCLike.Basic
public import Mathlib.NumberTheory.Padics.PadicNumbers

/-! # Quadratic forms over ℚ -/

@[expose] public section

open QuadraticMap

namespace QuadraticForm

-- Let `V` be a `ℚ`-vector space.
variable {V : Type*} [AddCommGroup V] [Module ℚ V]

-- Let `Q` be a quadratic form on `V`.
variable (Q : QuadraticForm ℚ V)

/-- A quadratic form over `ℚ` is everywhere locally isotropic if it has nontrivial
`p`-adic points for all `p`, and real points. -/
def EverywhereLocallyIsotropic :=
  (∀ (p : ℕ) [Fact (p.Prime)], (Q.baseChange ℚ_[p]).Isotropic) ∧ (Q.baseChange ℝ).Isotropic

variable {Q}

-- The easy implication of the Hasse-Minkowski theorem.
theorem _root_.QuadraticMap.Isotropic.everywhereLocallyIsotropic (h : Q.Isotropic) :
    Q.EverywhereLocallyIsotropic := by
  obtain ⟨x, ⟨hx, hxne0⟩⟩ := represents_zero_iff_isotropic.mpr h
  refine ⟨fun _ _ => ?_, ?_⟩ <;>
  rw [← represents_zero_iff_isotropic] <;>
  exact ⟨1 ⊗ₜ x, ⟨by simp [hx], by simp [hxne0]⟩⟩

open QuadraticMap

/- Will follow from `QuadraticMap.nondegenerate_of_anisotropic` and
  `QuadraticMap.degenerate_baseChange`. -/
theorem HasseMinkowski_of_degenerate (Q : QuadraticForm ℚ V) (hQ : ¬ Q.Nondegenerate) :
    Q.Isotropic ↔ Q.EverywhereLocallyIsotropic := by
  have dQ := Q.nondegenerate_of_anisotropic.mt hQ
  have dR := ((Q.baseChange ℝ).nondegenerate_of_anisotropic).mt (degenerate_baseChange (A := ℝ) hQ)
  simp only [Isotropic, dQ, not_false_eq_true, EverywhereLocallyIsotropic, dR, and_true, true_iff]
  intro p hp
  exact ((Q.baseChange ℚ_[p]).nondegenerate_of_anisotropic).mt (degenerate_baseChange hQ)

namespace EverywhereLocallyIsotropic

lemma isotropic_of_rank_zero [Module.Finite ℚ V] (hr : Module.finrank ℚ V = 0) (_ : Q.Nondegenerate)
    (hQ' : Q.EverywhereLocallyIsotropic) :
    Q.Isotropic := by
  have h' := hQ'.2
  contrapose! h'
  exact QuadraticMap.anisotropic_of_rank_zero (by simp [hr])

lemma isotropic_of_rank_one (hr : Module.finrank ℚ V = 1) (_ : Q.Nondegenerate)
    (hQ' : Q.EverywhereLocallyIsotropic) :
    Q.Isotropic := by
  have QR_zero := (QuadraticMap.isotropic_iff_zero_of_rank_one (by simp [hr])).mp hQ'.2
  simp only [baseChange_ext_iff, baseChange_tmul, mul_one, Rat.smul_one_eq_cast,
    QuadraticMap.zero_apply, Rat.cast_eq_zero] at QR_zero
  exact (QuadraticMap.isotropic_iff_zero_of_rank_one hr).mpr (by simpa [Q.ext_iff] using QR_zero)

open Equivalent in
lemma isotropic_of_rank_two [FiniteDimensional ℚ V] [NeZero (Module.finrank ℚ V)]
    (hr : Module.finrank ℚ V = 2) (hQ : Q.Nondegenerate) (hQ' : Q.EverywhereLocallyIsotropic) :
    Q.Isotropic := by
  obtain ⟨w, hw⟩ := QuadraticForm.equivalent_weightedSumSquares Q
  obtain ⟨hQ'f, hQ'R⟩ := hQ'
  rw [← represents_zero_iff_isotropic] at *

  rw [represents_iff hw]
  rw [represents_iff
    ((baseChange ℝ hw).trans (QuadraticForm.baseChange_weightedSumSquares ℚ ℝ w))] at hQ'R
  obtain ⟨x, hx⟩ := hQ'R
  simp only [eq_ratCast, weightedSumSquares_apply, smul_eq_mul, ne_eq] at hx

  sorry

end EverywhereLocallyIsotropic

end QuadraticForm
