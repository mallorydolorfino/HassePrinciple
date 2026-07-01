/-
Copyright (c) 2026 Nirvana Coppola, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nirvana Coppola, María Inés de Frutos-Fernández
-/
module

public import HassePrinciple.QuadraticForm.Basic
public import HassePrinciple.QuadraticForm.Chain
public import HassePrinciple.HilbertSymbol.Basic
public import HassePrinciple.HilbertSymbol.ExistenceTheorem
public import HassePrinciple.NumberTheory.ApproximationTheorem
public import Mathlib.LinearAlgebra.QuadraticForm.IsometryEquiv
public import Mathlib.Data.Fin.Basic

/-! # The Hasse-Minkowski invariant -/

@[expose] public section

section Prelim

lemma LinearMap.separatingLeft_of_equivalent {R M M' N : Type*} [CommRing R]
    [AddCommGroup M] [AddCommGroup M'] [Module R M] [Module R M'] [AddCommGroup N] [Module R N]
    [Invertible (2 : R)] {Q : QuadraticMap R M N} {Q' : QuadraticMap R M' N} (h : Q.Equivalent Q')
    (hQ : LinearMap.SeparatingLeft Q.associated) :
    LinearMap.SeparatingLeft Q'.associated := by
  sorry

end Prelim

namespace QuadraticForm

variable {k : Type*} [Field k] --[CharZero k]

-- Let `V` and `W` be `k`-vector spaces.
variable {V W : Type*} [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

-- Let `Q` be a quadratic form on `V`.
variable (Q : QuadraticForm k V)

/-- Auxiliary definition for `HasseMinkoskiInvariant`. -/
noncomputable def HasseMinkoskiInvariantAux {n : ℕ} (w : Fin n → kˣ) : ℤ :=
  ∏ p : Fin n × Fin n with p.1 < p.2, hilbertSym (w p.1 : k) (w p.2)

lemma HasseMinkoskiInvariantAux_def {n : ℕ} (w : Fin n → kˣ) :
    HasseMinkoskiInvariantAux w =
      ∏ p : Fin n × Fin n with p.1 < p.2, hilbertSym (w p.1 : k) (w p.2) := rfl

lemma HasseMinkoskiInvariantAux.eq_of_equivalent {n m : ℕ} {w : Fin n → kˣ} {w' : Fin m → kˣ}
    (h : (QuadraticMap.weightedSumSquares k w).Equivalent (QuadraticMap.weightedSumSquares k w')) :
    HasseMinkoskiInvariantAux w = HasseMinkoskiInvariantAux w' := by
  sorry

variable [Invertible (2 : k)] [FiniteDimensional k V] [FiniteDimensional k W]

/-- Let `Q` be a quadratic form on `V` such that `Q.associated` is `SeparatingLeft`, and
suppose that `Q` is equivalent to the diagonal quadratic form `a_1 X_1^2 + ⋯ + a_n X_n ^ 2`.
The Hasse-Minkowski invariant of `Q` is defined as the product `∏_{i < j} (a_i, a_j)`, where
`(·, ·)` denotes the Hilbert symbol.

This is denoted by `ε(Q)` in Serre's book. -/
noncomputable def HasseMinkoskiInvariant {Q : QuadraticForm k V}
    (hQ : LinearMap.SeparatingLeft Q.associated) : ℤ :=
  HasseMinkoskiInvariantAux (equivalent_weightedSumSquares_units_of_nondegenerate' Q hQ).choose

namespace HasseMinkoskiInvariant

open _root_.QuadraticMap

variable {Q : QuadraticForm k V} {Q' : QuadraticForm k W}
  (hQ : LinearMap.SeparatingLeft Q.associated)

lemma weightedSumSquares {n : ℕ} (w : Fin n → kˣ) :
    HasseMinkoskiInvariant
      (nondegenerate_associated_iff.mpr (nondegenerate_weightedSumSquares w)).1 =
      ∏ p : Fin n × Fin n with p.1 < p.2, hilbertSym (w p.1 : k) (w p.2) := by
  simp only [HasseMinkoskiInvariant, ← HasseMinkoskiInvariantAux_def w]
  exact HasseMinkoskiInvariantAux.eq_of_equivalent
    ((equivalent_weightedSumSquares_units_of_nondegenerate' (QuadraticMap.weightedSumSquares k w))
      (nondegenerate_associated_iff.mpr (nondegenerate_weightedSumSquares w)).1).choose_spec.symm

lemma weightedSumSquares_two (w : Fin 2 → kˣ) :
    HasseMinkoskiInvariant
      (nondegenerate_associated_iff.mpr (nondegenerate_weightedSumSquares w)).1 =
      hilbertSym (w 0 : k) (w 1) := by
  rw [HasseMinkoskiInvariant.weightedSumSquares, Finset.prod_eq_single (0, 1)
      (by grind) (fun h ↦ by simp at h)]

lemma weightedSumSquares_three (w : Fin 3 → kˣ) :
    HasseMinkoskiInvariant
      (nondegenerate_associated_iff.mpr (nondegenerate_weightedSumSquares w)).1 =
      hilbertSym (w 0 : k) (w 1) * hilbertSym (w 0 : k) (w 2) * hilbertSym (w 1 : k) (w 2) := by
  have h : ({p : Fin 3 × Fin 3 | p.1 < p.2} : Finset (Fin 3 × Fin 3)) =
      {(0, 1), (0, 2), (1, 2)} := by
    ext p
    refine ⟨fun hp ↦ ?_, fun hp ↦ by aesop⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.isValue, Finset.mem_insert,
        Finset.mem_singleton] at hp ⊢
      have h1 : p.1 = 0 ∨ p.1 = 1 ∨ p.1 = 2  := by omega
      have h2 : p.2 = 0 ∨ p.2 = 1 ∨ p.2 = 2  := by omega
      aesop
  rw [HasseMinkoskiInvariant.weightedSumSquares,
    Finset.prod_congr h (g := fun p ↦ hilbertSym (w p.1 : k) (w p.2)) (by simp)]
  simp [mul_assoc]

lemma eq_of_equivalent_weightedSumSquares {n : ℕ} {w : Fin n → kˣ}
    (h : Q.Equivalent (QuadraticMap.weightedSumSquares k w)) :
    HasseMinkoskiInvariant hQ =
      HasseMinkoskiInvariant (LinearMap.separatingLeft_of_equivalent h hQ) := by
  sorry

lemma eq_of_equivalent (h : Q.Equivalent Q') :
    HasseMinkoskiInvariant hQ =
      HasseMinkoskiInvariant (LinearMap.separatingLeft_of_equivalent h hQ) := by
  sorry

lemma eq_one_or_neg_one :
    HasseMinkoskiInvariant hQ = 1 ∨ HasseMinkoskiInvariant hQ = - 1 := sorry

open Module TensorProduct in
lemma of_baseChange_weightedSumSquares {R : Type*} (A : Type*) [Field R]
    [Invertible (2 : R)] [Field A] [Invertible (2 : A)] [Algebra R A] (w : Fin 2 → Rˣ) :
    HasseMinkoskiInvariant
      ((nondegenerate_associated_iff.mpr
        (nondegenerate_baseChange (A := A) (nondegenerate_weightedSumSquares w))).1) =
      hilbertSym (algebraMap R A (w ⟨0, by omega⟩)) ( algebraMap R A (w ⟨1, by omega⟩)) := by
  have h2 : finrank A (A ⊗[R] (Fin 2 → R)) = 2 := by simp
  rw [HasseMinkoskiInvariant.eq_of_equivalent_weightedSumSquares
    (w := ![Units.map (algebraMap R A) (w ⟨0, by omega⟩),
       Units.map (algebraMap R A) (w ⟨1, by omega⟩)]) _
    (((baseChange_weightedSumSquares _ _ _).trans (Equivalent.refl _))), weightedSumSquares_two]
  simp

end HasseMinkoskiInvariant
section Field

open Module _root_.QuadraticMap

variable {K V : Type*} [Field K] [CharZero K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} (hQ : Q.Nondegenerate)

-- TODO: move
/-- This generalizes Mathlib's `weightedSumSquaresCongr`. -/
def weightedSumSquaresCongr' {ι κ S R : Type*} [Fintype ι] [Fintype κ] [CommSemiring R]
    [Monoid S] [DistribMulAction S R] [SMulCommClass S R R]
    {w : ι → S} {w' : κ → S} (f : ι ≃ κ) (h : w = w'.comp f) :
    (weightedSumSquares R w).IsometryEquiv (weightedSumSquares R w') where
  toFun m k := m (f.symm k)
  map_add' m n  := by ext; simp
  map_smul' r m := by ext; simp
  invFun m i    := m (f i)
  left_inv m    := by simp
  right_inv m   := by simp
  map_app' m    := by
    simp only [weightedSumSquares_apply, h, Function.comp_apply]
    exact Finset.sum_equiv f.symm (by simp) (by simp)

-- TODO: move
lemma weightedSumSquaresCongr'_equivalent {ι κ S R : Type*} [Fintype ι] [Fintype κ] [CommSemiring R]
    [Monoid S] [DistribMulAction S R] [SMulCommClass S R R]
    {w : ι → S} {w' : κ → S} (f : ι ≃ κ) (h : w = w'.comp f) :
    (weightedSumSquares R w).Equivalent (weightedSumSquares R w') := ⟨weightedSumSquaresCongr' f h⟩

-- TODO: move
lemma weightedSumSquares_isotropic_iff_hilbertSym_eq_one' {R : Type*} [Field R] (a b : Rˣ) :
    (weightedSumSquares R ![a, b, 1]).Isotropic ↔ hilbertSym (-a : R) (-b) = 1 := by
  simp only [Nat.succ_eq_add_one, Nat.reduceAdd, ← represents_zero_iff_isotropic, represents,
    weightedSumSquares_apply, Units.smul_def, smul_eq_mul, Fin.sum_univ_three, Fin.isValue,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Units.val_one, one_mul, ne_eq,
    hilbertSym, neg_mul, neg_eq_zero, Units.ne_zero, or_self, ↓reduceIte, Prod.mk.injEq, not_and,
    sub_neg_eq_add, Int.reduceNeg, ite_eq_left_iff, not_exists, reduceCtorEq, imp_false,
    not_forall, not_not, pow_two]
  refine ⟨fun ⟨x, hx, hx0⟩ ↦ ⟨x 2, x 0, x 1, ?_, ?_⟩,
      fun ⟨x, y, z, h0, h⟩ ↦ ⟨![y, z, x], ?_, by aesop⟩⟩
  · intros h0 h1 h2
    simp only [funext_iff, Fin.forall_iff, Pi.zero_apply, not_forall] at hx0
    grind
  · simp only [← hx]
    ring
  · simp only [← h, Matrix.cons_val]
    ring

lemma weightedSumSquares_isotropic_iff_hilbertSym_eq_one {R : Type*} [Field R] (a b c : Rˣ) :
    (weightedSumSquares R ![a, b, c]).Isotropic ↔ hilbertSym (-c * a : R) (-c * b) = 1 := by
  let c' : Rˣˣ := ⟨c, c⁻¹, by simp, by simp⟩
  rw [mul_unit_isotropic_iff (a := c) (w' := ![c * a, c * b, c * c])
      (by simp [Fin.forall_fin_succ]),
    (weightedSumSquares_mul_squares_equivalent  (w' := ![c * a, c * b, 1]) ![1, 1, c']
      (by simp [Fin.forall_fin_succ, pow_two, c'])).isotropic_iff,
    weightedSumSquares_isotropic_iff_hilbertSym_eq_one']
  simp

lemma _root_.LinearEquiv.det_toMatrix_ne_zero {ι R M N : Type*} [DecidableEq ι] [Fintype ι]
    [CommRing R] [Nontrivial R] [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (b : Module.Basis ι R M) (b' : Module.Basis ι R N) (f : M ≃ₗ[R] N) :
    (LinearMap.toMatrix b b' f).det ≠ 0 := by
  exact Matrix.det_ne_zero_of_left_inverse (B := LinearMap.toMatrix b' b f.symm)
    (by simp [← LinearMap.toMatrix_comp])

theorem equivalent_weightedSumSquares_three_units_of_nondegenerate {K V : Type*}
    [Field K] [Invertible (2 : K)] [AddCommGroup V] [Module K V] (hr : finrank K V = 3)
    {Q : QuadraticForm K V} (hQ : LinearMap.SeparatingLeft (QuadraticMap.associated Q)) :
    ∃ (w : Fin 3 → Kˣ), QuadraticMap.Equivalent Q (QuadraticMap.weightedSumSquares K w) := by
  have : FiniteDimensional K V := finite_of_finrank_eq_succ hr
  obtain ⟨w, hw⟩ := Q.equivalent_weightedSumSquares_units_of_nondegenerate' hQ
  refine ⟨![w ⟨0, by omega⟩, w ⟨1, by omega⟩, w ⟨2, by omega⟩], ?_⟩
  apply hw.trans
  apply (weightedSumSquaresCongr'_equivalent (finCongr hr) ?_)
  ext n
  cases n with
  | mk n hn =>
    have hn : n = 0 ∨ n = 1 ∨ n = 2  := by omega
    aesop

omit [FiniteDimensional K V] in --TODO: reorganize
private lemma discr_three (b : Basis (Fin 3) K V) {w : Fin 3 → Kˣ}
    (fw : Q.IsometryEquiv (weightedSumSquares K w)) :
    discr b Q = w 0 * w 1 * w 2 *
      ((LinearMap.toMatrix b (Pi.basisFun K (Fin 3))) fw.toLinearEquiv).det ^ 2 := by
  rw [IsometryEquiv.discr (Equiv.refl _) b (Pi.basisFun K (Fin 3)) fw]
  simp [weightedSumSquares_discr, Units.smul_def, smul_eq_mul, mul_one, Fin.prod_univ_three]

private lemma represents_zero_iff_of_rank_three_aux (b : Basis (Fin 3) K V) (hQ : Q.Nondegenerate)
    {w : Fin 3 → Kˣ} (hw : Q.Equivalent (weightedSumSquares K w))
    (heq : hilbertSym (-w 2 * w 0 : K) (-w 2 * w 1) = hilbertSym (-1) (-Q.discr b) *
        HasseMinkoskiInvariant (Q.nondegenerate_associated_iff.mpr hQ).1) :
    Q.Isotropic ↔ hilbertSym (-1) (-Q.discr b) =
        HasseMinkoskiInvariant (Q.nondegenerate_associated_iff.mpr hQ).1 := by
  have hw' : w = ![w 0, w 1, w 2] := List.ofFn_inj.mp rfl
  set s := hilbertSym (-1) (-Q.discr b)
  set ε := HasseMinkoskiInvariant (Q.nondegenerate_associated_iff.mpr hQ).1 with hε_def
  have hs1 : s = 1 ∨ s = -1 := hilbertSym.eq_one_or_neg_one_of_ne_zero (by simp)
    (neg_ne_zero.mpr ((nondegenerate_iff_discr_ne_zero b).mp hQ))
  have hε1 : ε = 1 ∨ ε = -1 :=
    HasseMinkoskiInvariant.eq_one_or_neg_one (Q.nondegenerate_associated_iff.mpr hQ).1
  have hsε : s = ε ↔ s * ε = 1 := by
    rcases hs1 with hs1 | hs1 <;> rcases hε1 with hε1 | hε1 <;> simp [hs1, hε1]
  -- let ⟨fw⟩ := hw
  -- let u := ((LinearMap.toMatrix b (Pi.basisFun K (Fin 3))) ↑fw.toLinearEquiv).det
  -- have hu : discr b Q = w 0 * w 1 * w 2 * u ^ 2 := by
  --   rw [IsometryEquiv.discr (Equiv.refl _) b (Pi.basisFun K (Fin 3)) fw]
  --   simp only [weightedSumSquares_discr, Units.smul_def, smul_eq_mul, mul_one]
  --   simp [Fin.prod_univ_three, u]
  have hε : ε = hilbertSym (w 0 : K) (w 1) * hilbertSym (w 0 : K) (w 2) *
      hilbertSym (w 1 : K) (w 2) := by
    simp [ε, HasseMinkoskiInvariant.eq_of_equivalent _ hw,
      HasseMinkoskiInvariant.weightedSumSquares_three]
  rw [hw.isotropic_iff, hw', weightedSumSquares_isotropic_iff_hilbertSym_eq_one, hsε, heq]

namespace Real

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V] {Q : QuadraticForm ℝ V}
  (hQ : Q.Nondegenerate)

lemma represents_zero_iff_of_rank_three (b : Basis (Fin 3) ℝ V) :
    Q.Isotropic ↔
      hilbertSym (-1) (-Q.discr b) =
        HasseMinkoskiInvariant (Q.nondegenerate_associated_iff.mpr hQ).1 := by
  obtain ⟨w, hw⟩ := equivalent_weightedSumSquares_three_units_of_nondegenerate
    ( by simp [finrank_eq_card_basis b]) (Q.nondegenerate_associated_iff.mpr hQ).1
  -- Set up notation for readability
  let ⟨fw⟩ := hw
  let a₀ := w 0
  let a₁ := w 1
  let a₂ := w 2
  let u := ((LinearMap.toMatrix b (Pi.basisFun ℝ (Fin 3))) fw.toLinearEquiv).det
  set s := hilbertSym (-1) (-Q.discr b)
  set ε := HasseMinkoskiInvariant (Q.nondegenerate_associated_iff.mpr hQ).1 with hε_def
  have hε : ε = hilbertSym (a₀ : ℝ) a₁ * hilbertSym (a₀ : ℝ) a₂ * hilbertSym (a₁ : ℝ) a₂ := by
    simp [ε, HasseMinkoskiInvariant.eq_of_equivalent _ hw,
      HasseMinkoskiInvariant.weightedSumSquares_three, a₀, a₁, a₂]
  rw [represents_zero_iff_of_rank_three_aux b hQ hw]
  -- Computation using properties of the Hilbert Symbol
  calc hilbertSym (-a₂ * a₀ : ℝ) (-a₂ * a₁)
      _ = hilbertSym (-1 : ℝ) (- 1) * hilbertSym (-1 : ℝ) a₀ * hilbertSym (-1 : ℝ) a₁ *
          hilbertSym (a₂ : ℝ) a₂ *
          (hilbertSym (a₀ : ℝ) a₁ * hilbertSym (a₀ : ℝ) a₂ * hilbertSym (a₁ : ℝ) a₂) := by
          rw [← neg_one_mul (a₂ : ℝ)]
          simp only [hilbertSym.real_mul_right_eq, hilbertSym.real_mul_left_eq]
          rw [hilbertSym.comm (a := (a₂ : ℝ)) (b := -1), hilbertSym.comm (a := (a₀ : ℝ)) (b := -1),
            hilbertSym.comm (a := (a₂ : ℝ)) (b := a₁)]
          ring_nf
          rw [sq_eq_one_iff.mpr (hilbertSym.eq_one_or_neg_one_of_ne_zero (by simp) (by simp))]
          simp
      _ = hilbertSym (-1 : ℝ) (- 1) * hilbertSym (-1 : ℝ) a₀ * hilbertSym (-1 : ℝ) a₁ *
          hilbertSym (a₂ : ℝ) a₂ * ε := by simp [hε]
      _ = hilbertSym (-1 : ℝ) (- 1) * hilbertSym (-1 : ℝ) a₀ * hilbertSym (-1 : ℝ) a₁ *
          hilbertSym (-1 : ℝ) a₂ * ε := by
          congr 2
          rw [← hilbertSym.left_neg_mul (a := -1)]
          simp
      _ = hilbertSym (-1 : ℝ) (- 1) * hilbertSym (-1 : ℝ) (a₀ * a₁ * a₂) * ε := by
        rw [hilbertSym.real_mul_right_eq, hilbertSym.real_mul_right_eq]
        ring
      _ = hilbertSym (-1 : ℝ) (- (a₀ * a₁ * a₂)) * ε := by
        rw [← neg_one_mul (_ * _), hilbertSym.real_mul_right_eq (b := -1)]
      _ = hilbertSym (-1 : ℝ) (- (a₀ * a₁ * a₂ * u ^ 2)) * ε := by
        rw [← neg_mul _ ((u : ℝ) ^ 2), hilbertSym.mul_right_square_eq]
        exact LinearEquiv.det_toMatrix_ne_zero _ _ _
      _ = s * ε := by simp [s, discr_three b fw, u, a₀, a₁, a₂]

end Real


lemma represents_zero_iff_of_rank_three (b : Basis (Fin 3) K V) :
    Q.Isotropic ↔
      hilbertSym (-1) (-Q.discr b) =
        HasseMinkoskiInvariant (Q.nondegenerate_associated_iff.mpr hQ).1 := by
  have hr : finrank K V = 3 := by simp [finrank_eq_card_basis b]
  obtain ⟨w, hw⟩ := equivalent_weightedSumSquares_three_units_of_nondegenerate hr
    (QuadraticMap.nondegenerate_associated_iff.mpr hQ).1
  let a₀ := w 0
  let a₁ := w 1
  let a₂ := w 2
  have hw' : w = ![w 0, w 1, w 2] := List.ofFn_inj.mp rfl
  set s := hilbertSym (-1) (-Q.discr b)
  set ε := HasseMinkoskiInvariant (Q.nondegenerate_associated_iff.mpr hQ).1 with hε_def
  have hs1 : s = 1 ∨ s = -1 := hilbertSym.eq_one_or_neg_one_of_ne_zero (by simp)
    (neg_ne_zero.mpr ((nondegenerate_iff_discr_ne_zero b).mp hQ))
  have hε1 : ε = 1 ∨ ε = -1 :=
    HasseMinkoskiInvariant.eq_one_or_neg_one (Q.nondegenerate_associated_iff.mpr hQ).1
  have hi : Q.Isotropic ↔ hilbertSym (-a₂ * a₀ : K) (-a₂ * a₁) = 1 := by
    rw [hw.isotropic_iff, hw', weightedSumSquares_isotropic_iff_hilbertSym_eq_one]
  let ⟨fw⟩ := hw
  let u := ((LinearMap.toMatrix b (Pi.basisFun K (Fin 3))) ↑fw.toLinearEquiv).det
  have hu : discr b Q = a₀ * a₁ * a₂ * u ^ 2 := by
    rw [IsometryEquiv.discr (Equiv.refl _) b (Pi.basisFun K (Fin 3)) fw]
    simp only [weightedSumSquares_discr, Units.smul_def, smul_eq_mul, mul_one]
    simp [Fin.prod_univ_three, u, a₀, a₁, a₂]
  have hε : ε = hilbertSym (a₀ : K) a₁ * hilbertSym (a₀ : K) a₂ * hilbertSym (a₁ : K) a₂ := by
    simp [ε, HasseMinkoskiInvariant.eq_of_equivalent _ hw,
      HasseMinkoskiInvariant.weightedSumSquares_three, a₀, a₁, a₂]
  have heq : hilbertSym (-a₂ * a₀ : K) (-a₂ * a₁) = s * ε := by
    calc hilbertSym (-a₂ * a₀ : K) (-a₂ * a₁)
      _ = hilbertSym (-1 : K) (- (a₀ * a₁ * a₂)) *
          (hilbertSym (a₀ : K) a₁ * hilbertSym (a₀ : K) a₂ * hilbertSym (a₁ : K) a₂) := by sorry
      _ = hilbertSym (-1 : K) (- (a₀ * a₁ * a₂ * u ^ 2)) *
          (hilbertSym (a₀ : K) a₁ * hilbertSym (a₀ : K) a₂ * hilbertSym (a₁ : K) a₂) := by
        rw [← neg_mul _ ((u : K) ^ 2), hilbertSym.mul_right_square_eq]
        exact LinearEquiv.det_toMatrix_ne_zero _ _ _
      _ = s * ε := by simp [s, hε, hu]
  rw [hi, show s = ε ↔ s * ε = 1 by sorry, heq]


lemma represents_zero_iff_of_rank_three' (b : Basis (Fin 3) K V) :
    Q.Isotropic ↔
      hilbertSym (-1) (-Q.discr b) =
        HasseMinkoskiInvariant (Q.nondegenerate_associated_iff.mpr hQ).1 := by
  have hr : finrank K V = 3 := by simp [finrank_eq_card_basis b]
  obtain ⟨w, hw⟩ := Q.equivalent_weightedSumSquares_units_of_nondegenerate'
    (QuadraticMap.nondegenerate_associated_iff.mpr hQ).1
  let a₀ := w ⟨0, by omega⟩
  let a₁ := w ⟨1, by omega⟩
  let a₂ := w ⟨2, by omega⟩
  have hw' : Q.Equivalent (weightedSumSquares K ![a₀, a₁, a₂]) := by
    apply hw.trans
    apply (weightedSumSquaresCongr'_equivalent (finCongr hr) ?_)
    ext n
    cases n with
    | mk n hn =>
      have hn : n = 0 ∨ n = 1 ∨ n = 2  := by omega
      aesop
  set s := hilbertSym (-1) (-Q.discr b)
  set ε := HasseMinkoskiInvariant (Q.nondegenerate_associated_iff.mpr hQ).1 with hε_def
  have hs1 : s = 1 ∨ s = -1 := hilbertSym.eq_one_or_neg_one_of_ne_zero (by simp)
    (neg_ne_zero.mpr ((nondegenerate_iff_discr_ne_zero b).mp hQ))
  have hε1 : ε = 1 ∨ ε = -1 :=
    HasseMinkoskiInvariant.eq_one_or_neg_one (Q.nondegenerate_associated_iff.mpr hQ).1
  have hi : Q.Isotropic ↔ hilbertSym (-a₂ * a₀ : K) (-a₂ * a₁) = 1 := by
    rw [hw'.isotropic_iff, weightedSumSquares_isotropic_iff_hilbertSym_eq_one]
  let ⟨fw⟩ := hw
  let u := (fw.toLinearEquiv.toMatrix (b.reindex (finCongr hr.symm))
      (Pi.basisFun K (Fin (finrank K V)))).det
  have hu : discr b Q = a₀ * a₁ * a₂ * u ^ 2 := by
    rw [IsometryEquiv.discr (finCongr hr.symm) b (Pi.basisFun K (Fin (finrank K V))) fw]
    congr
    simp only [weightedSumSquares_discr, Units.smul_def, smul_eq_mul, mul_one]
    rw [Finset.prod_equiv (finCongr hr) (s := Finset.univ) (t := Finset.univ)
      (g := ![(a₀ : K), a₁, a₂]) (by aesop)]
    · simp [Fin.prod_univ_three]
    · intro n _;
      cases n with
      | mk n hn =>
        have hn : n = 0 ∨ n = 1 ∨ n = 2 := by omega
        aesop
  have hε : ε = hilbertSym (a₀ : K) a₁ * hilbertSym (a₀ : K) a₂ * hilbertSym (a₁ : K) a₂ := by
    simp [ε, HasseMinkoskiInvariant.eq_of_equivalent _ hw',
      HasseMinkoskiInvariant.weightedSumSquares_three]
  have heq : hilbertSym (-a₂ * a₀ : K) (-a₂ * a₁) = s * ε := by
    calc hilbertSym (-a₂ * a₀ : K) (-a₂ * a₁)
      _ = hilbertSym (-1 : K) (- (a₀ * a₁ * a₂)) *
          (hilbertSym (a₀ : K) a₁ * hilbertSym (a₀ : K) a₂ * hilbertSym (a₁ : K) a₂) := by sorry
      _ = hilbertSym (-1 : K) (- (a₀ * a₁ * a₂ * u ^ 2)) *
          (hilbertSym (a₀ : K) a₁ * hilbertSym (a₀ : K) a₂ * hilbertSym (a₁ : K) a₂) := by
        rw [← neg_mul _ ((u : K) ^ 2), hilbertSym.mul_right_square_eq]
        exact LinearEquiv.det_toMatrix_ne_zero (b.reindex (finCongr hr.symm))
          (Pi.basisFun K (Fin (finrank K V))) _
      _ = s * ε := by simp [s, hε, hu]
  rw [hi, show s = ε ↔ s * ε = 1 by aesop, heq]

lemma represents_iff_of_rank_two (b : Basis (Fin 2) K V) (a : K) :
    Q.represents a ↔
      hilbertSym a (-Q.discr b) =
        HasseMinkoskiInvariant (Q.nondegenerate_associated_iff.mpr hQ).1 := by
  sorry

end Field

end QuadraticForm
