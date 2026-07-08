import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Data.Matrix.Reflection

namespace ALG1.Cwi11

open Matrix Polynomial

theorem Zad1a : !![1, 2; 2, 1].charpoly = (X ^ 2 - 2 * X - 3 : ℤ[X]) := by
  simp [charpoly, det_fin_two]; ring

theorem Zad1b : !![0, 1, 0; 1, 0, 1; 0, 1, 0].charpoly = (X ^ 3 - 2 * X : ℤ[X]) := by
  simp [charpoly, det_fin_three]; ring

theorem _root_.Matrix.charpoly_smul [Field K] [Fintype n] [DecidableEq n] (M : Matrix n n K)
    {c : K} (hc : c ≠ 0) : (c • M).charpoly = c ^ Fintype.card n • M.charpoly.comp (C c⁻¹ * X) := by
  simp [charpoly, charmatrix, Matrix.map_smul]
  convert_to (c • (c⁻¹ • scalar n X - M.map C)).det = _
  · simp [-det_smul_of_tower, smul_sub, smul_smul, mul_inv_cancel₀ hc]
  simp; rw [← coe_compRingHom_apply, RingHom.map_det]; simp [Matrix.map_sub]; congr
  · ext1 i j; simp [diagonal_apply, smul_eq_C_mul]
  · ext1 x; simp

theorem Zad2b [CommRing R] [Fintype n] [DecidableEq n] {A : Matrix n n R}
    (h : A.charpoly = X ^ 3 - 4 * X ^ 2 - 2 * X + 1) :
    (A + 2)ᵀ.charpoly = X ^ 3 - 10 * X ^ 2 + 26 * X - 19 := by
  rw [charpoly_transpose]
  convert ← A.charpoly_sub_scalar (-2) using 1
  · simp [← diagonal_neg, diagonal_ofNat]
  rw [h]; simp [C_ofNat]; ring

theorem Zad2c [CommRing R] [Nontrivial R] [Fintype n] [DecidableEq n] {A : Matrix n n R}
    (h : A.charpoly = X ^ 3 - 4 * X ^ 2 - 2 * X + 1) (h' : IsUnit A) :
    A⁻¹.charpoly = X ^ 3 - 2 * X ^ 2 - 4 * X + 1 := by
  simp [A.charpoly_inv h', ← reverse_charpoly, det_eq_sign_charpoly_coeff, h, ← Ring.inverse_pow,
    Ring.inverse_of_isUnit isUnit_neg_one, IsUnit.unit, ← pow_add]
  have : (X ^ 3 - 4 * X ^ 2 - 2 * X + 1 : R[X]).natDegree = 3 := by compute_degree!
  simp [reverse, this]; rw [← C_ofNat, ← C_ofNat, ← pow_one X]
  simp [-pow_one, ← pow_mul]; simp [C_ofNat]; ring

lemma Zad3_isUnit : IsUnit (!![1, 2, 2; 2, 1, -2; 2, -2, 1] : Matrix _ _ ℚ) := by
  simp [isUnit_iff_isUnit_det, det_fin_three]; norm_num

/-- The column vectors `![1, 2, 2]`, `![2, 1, -2]`, and `![2, -2, 1]` are the matrix's eigenvectors. -/
theorem Zad3a : (!![2, -2, 0; -2, 1, -2; 0, -2, 0] : Matrix _ _ ℚ) =
    !![1, 2, 2; 2, 1, -2; 2, -2, 1] * diagonal ![-2, 1, 4] * !![1, 2, 2; 2, 1, -2; 2, -2, 1]⁻¹ := by
  have := Zad3_isUnit.invertible
  symm; rw [mul_inv_eq_iff_eq_mul_of_invertible]
  ext i j; fin_cases i <;> fin_cases j <;> norm_num

theorem _root_.Matrix.conj_pow [CommRing R] [Fintype n] [DecidableEq n]
    {M : Matrix n n R} (h : IsUnit M) (N : Matrix n n R) (n : ℕ) :
    (M * N * M⁻¹) ^ n = M * N ^ n * M⁻¹ := by
  have := h.invertible
  induction n with simp [pow_add, *, ← mul_assoc]

theorem Zad3b (n : ℕ) : (!![2, -2, 0; -2, 1, -2; 0, -2, 0] : Matrix _ _ ℚ) ^ n = (9⁻¹ : ℚ) •
    !![4 * 4 ^ n +     (-2) ^ n + 4, -4 * 4 ^ n + 2 * (-2) ^ n + 2,  2 * 4 ^ n + 2 * (-2) ^ n - 4;
      -4 * 4 ^ n + 2 * (-2) ^ n + 2,  4 * 4 ^ n + 4 * (-2) ^ n + 1, -2 * 4 ^ n + 4 * (-2) ^ n - 2;
       2 * 4 ^ n + 2 * (-2) ^ n - 4, -2 * 4 ^ n + 4 * (-2) ^ n - 2,      4 ^ n + 4 * (-2) ^ n + 4] := by
  rw [Zad3a, Matrix.conj_pow Zad3_isUnit, diagonal_pow]
  simp [inv_def, det_fin_three, ← vecMulᵣ_eq, vecHead, vecTail, vecMulᵣ]; norm_num
  and_intros <;> ring
