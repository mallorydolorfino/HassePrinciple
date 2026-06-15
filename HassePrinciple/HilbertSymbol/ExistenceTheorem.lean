/-
Copyright (c) 2026 Nirvana Coppola, María Inés de Frutos-Fernández. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nirvana Coppola, María Inés de Frutos-Fernández
-/
module

public import HassePrinciple.HilbertSymbol.Basic
public import HassePrinciple.NumberTheory.ApproximationTheorem

/-!
# Existence theorem
-/
@[expose] public section

namespace hilbertSym

/-- Given a finite set of rational numbers `{a_i}_{i ∈ I}` and numbers `e_{i,v} ∈ {± 1}`,
there exists a rational number `x` such that the Hilbert symbols `(x,a_i)_v` at each place `v`
is equal to `e_{i,v}` if and only if
1) for all `i`, almost all `e_{i,v}` are 1
2) for all `i`, the product of all `e_{i,v}` is 1
3) for each place `v`, there is some `x_v ∈ Q_v` with `(x,a_i)_v = e_{i,v}`. -/
theorem exists_rat_with_prescribed_hilbert_symbols_at_finitely_many_places
    {I : Type*} [Finite I] (a : I → ℚˣ) (efin : I × Nat.Primes → ℤ) (einf : I → ℤ)
    (hefinpm1 : ∀ i : I, ∀ p : Nat.Primes, efin (i, p) = 1 ∨ efin (i, p) = -1)
    (heinfpm1 : ∀ i : I, einf i = 1 ∨ einf i = -1) :
      (∃ x : ℚˣ, ∀ i : I, (∀ p : Nat.Primes, efin (i, p) = atP x (a i) p) ∧
        einf i = atInfty x (a i)) ↔
        ∀ i : I, (∀ᶠ (p : Nat.Primes) in Filter.cofinite, efin (i, p) = 1) ∧
          (einf i * ∏ᶠ (p : Nat.Primes), efin (i, p) = 1) ∧
          ((∀ (p : Nat.Primes), ∃ xp : ℚ_[p], efin (i, p) = hilbertSym xp (a i)) ∧
            ∃ xr : ℝ, einf i = hilbertSym xr (a i)) := by
  constructor
  · intro ⟨x, hx⟩ i
    specialize hx i
    constructor
    · suffices {(p : Nat.Primes) | ¬atP x (a i) p = 1} = {(p : Nat.Primes) | ¬efin (i, p) = 1} by
        simp only [Filter.eventually_cofinite]
        rw [← this]
        exact almost_all_one x (a i : ℚˣ)
      ext n
      simp only [Set.mem_setOf_eq, ← hx.1]
    · constructor
      · rw [← prod_eq_one x (a i), ← hx.2]
        simp only [mul_eq_mul_left_iff]
        left
        congr
        simp only [hx]
      · constructor
        · intro n
          use x
          rw [hx.1 n]
        · use x
          rw [hx.2]
  · revert a
    suffices ∀ (a : I → ℚˣ), (∀ i : I, ∃ bi : ℤ, (a i).val = bi) → (∀ (i : I),
      (∀ᶠ (p : Nat.Primes) in Filter.cofinite, efin (i, p) = 1) ∧
        einf i * ∏ᶠ (p : Nat.Primes), efin (i, p) = 1 ∧
          (∀ (p : Nat.Primes), ∃ xp, efin (i, p) = hilbertSym xp (a i).val) ∧
            ∃ xr, einf i = hilbertSym xr (a i).val) →
              ∃ x, ∀ (i : I), (∀ (p : Nat.Primes), efin (i, p) = atP x (a i) p) ∧
                einf i = atInfty x (a i) by
      intro a
      have int_repr : ∀ (i : I), ∃ (bi ci : ℤ), (a i).val * ci^2 = bi := by
        intro i
        use (a i).val.num * (a i).val.den
        use (a i).val.den
        nth_rw 1 [← Rat.num_div_den (a i).val]
        field_simp
        simp only [Int.cast_natCast, Int.cast_mul]
        ring_nf

      sorry
    sorry


    -- have int_repr : ∀ (i : I), ∃ (bi ci : ℤ), (a i).val * ci^2 = bi := by
    --   intro i
    --   use (a i).val.num * (a i).val.den
    --   use (a i).val.den
    --   nth_rw 1 [← Rat.num_div_den (a i).val]
    --   field_simp
    --   simp only [Int.cast_natCast, Int.cast_mul]
    --   ring_nf
    -- have padic_red_to_int (p : Nat.Primes) : ∀ x : ℚ_[p], ∀ (i : I), ∃ (bi ci : ℤ),
    --     hilbertSym x (a i) = hilbertSym x bi := by
    --   intro x i
    --   have ⟨bi, ci, repi⟩ := int_repr i
    --   use bi
    --   use ci
    --   have : hilbertSym x ((a i).val * ci^2) = hilbertSym x (a i).val := by
    --     nth_rw 1 [(by ring_nf : x = x * 1^2), mul_square_eq]
    --   rw [← this]
    --   congr
    --   exact_mod_cast repi
    -- have real_red_to_int : ∀ x : ℝ, ∀ (i : I), ∃ (bi ci : ℤ),
    --     hilbertSym x (a i) = hilbertSym x bi := by
    --   intro x i
    --   have ⟨bi, ci, repi⟩ := int_repr i
    --   use bi
    --   use ci
    --   have : hilbertSym x ((a i).val * ci^2) = hilbertSym x (a i).val := by
    --     nth_rw 1 [(by ring_nf : x = x * 1^2), mul_square_eq]
    --   rw [← this]
    --   congr
    --   exact_mod_cast repi
    -- intro h

    -- sorry

end hilbertSym
