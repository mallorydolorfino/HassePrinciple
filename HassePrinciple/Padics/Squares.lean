/-
Copyright (c) 2026 Nirvana Coppola, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nirvana Coppola, María Inés de Frutos-Fernández
-/

module

public import Mathlib.NumberTheory.Padics.PadicNumbers
public import Mathlib.Topology.Algebra.OpenSubgroup

public import Mathlib.NumberTheory.Padics.RingHoms
public import Mathlib.Topology.Algebra.IsOpenUnits
public import Mathlib.Algebra.Group.Pointwise.Set.Scalar
public import Mathlib.Analysis.Normed.Module.Ball.Pointwise


/-! # Padic unit squares form an open subgroup. -/

@[expose] public section

namespace PadicInt

open Polynomial

/-- An element in ℤ_p (p odd) is a square if its reduction modulo p is a square. -/
lemma isSquare_of_zmod {p : ℕ} [Fact (Nat.Prime p)] (hodd : p ≠ 2) {m : ℤ_[p]}
    (hmod : IsSquare m.toZMod) : IsSquare m := by
  let F : ℤ_[p][X] := X ^ 2 - C m
  sorry

/-- An element in ℤ_2 is a square if its reduction modulo 8 is a square. -/
lemma isSquare_of_zmodPow {m : ℤ_[2]} (hmod : IsSquare (m.toZModPow 3)) : IsSquare m := by sorry

end PadicInt

namespace Padic

variable (p : ℕ) [Fact (Nat.Prime p)]

lemma isSquare_of_dist_one_lt_one {p : ℕ} [Fact (Nat.Prime p)] (hp : p ≠ 2) {x : ℚ_[p]}
    (hx : dist x 1 < 1) : IsSquare x := by
  let z : ℤ_[p] := ⟨x - 1, hx.le⟩
  have : ‖x - 1‖ = ‖z‖ := by simp [z]
  rw [dist_eq_norm, ← zpow_zero (p : ℝ), norm_lt_pow_iff_norm_le_pow_sub_one, this, zero_sub,
    ← Nat.cast_one, PadicInt.norm_le_pow_iff_mem_span_pow, pow_one, Ideal.mem_span_singleton] at hx
  have hz1 : IsSquare (z + 1) := by
    have hz0 : PadicInt.toZMod z = 0 := by
      rw [← RingHom.mem_ker, PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p]
      simp [Ideal.mem_span_singleton, hx]
    exact (z + 1).isSquare_of_zmod hp (by simp [hz0])
  obtain ⟨r, hr⟩ := hz1
  exact ⟨r, by simp [← PadicInt.coe_mul, ← hr, z]⟩

open Pointwise

lemma isOpen_squares_sdiff_zero : IsOpen ({x : ℚ_[p] | IsSquare x} \ {0}) := by
  refine isOpen_iff_forall_mem_open.mpr ?_
  intro x ⟨hx, hx0⟩
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff] at hx hx0
  by_cases hp : p = 2
  · sorry
  · use x • (Metric.ball (1 : ℚ_[p]) 1)
    refine ⟨?_, by simp [smul_ball hx0, Metric.isOpen_ball],
      Set.mem_smul_set.mpr ⟨1, by simp, by simp⟩⟩
    intro y hy
    simp only [← Set.image_smul, Set.mem_image, Metric.mem_ball, Set.mem_sdiff, Set.mem_setOf_eq,
      Set.mem_singleton_iff] at hy ⊢
    obtain ⟨u, hup, hu⟩ := hy
    simp only [← hu, smul_eq_mul, mul_eq_zero, not_or]
    refine ⟨hx.mul (isSquare_of_dist_one_lt_one hp hup), hx0, ?_⟩
    · sorry


--TODO: rename to unitSquares
-- Proven in section II.3.3.
/-- The open subgroup of `p`-adic unit squares inside `ℚ_[p]ˣ`. -/
def squares : OpenSubgroup ℚ_[p]ˣ where
  carrier              := {x : ℚ_[p]ˣ | IsSquare x}
  mul_mem' {x y} hx hy := IsSquare.mul hx hy
  one_mem'             := by simp
  inv_mem' {x} hx      := IsSquare.inv hx
  isOpen'              := by
    have h : (Units.val '' {x : ℚ_[p]ˣ | IsSquare x}) = {x : ℚ_[p] | IsSquare x} \ {0} := by
      ext x
      simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_sdiff, Set.mem_singleton_iff]
      refine ⟨fun ⟨u, hu2, hux⟩ ↦ ?_, fun ⟨hxs, hx0⟩ ↦ ?_⟩
      · simp only [← hux, Units.ne_zero, not_false_eq_true, and_true]
        obtain ⟨v, hv⟩ := hu2
        exact ⟨v, by simp [hv]⟩
      · obtain ⟨r, hr⟩ := hxs
        exact ⟨Units.mk0 x hx0, ⟨Units.mk0 r (by aesop), by simp [hr]⟩, by simp⟩
    rw [IsOpenUnits.isOpenEmbedding_unitsVal.isOpen_iff_image_isOpen, h]
    exact isOpen_squares_sdiff_zero p

end Padic
