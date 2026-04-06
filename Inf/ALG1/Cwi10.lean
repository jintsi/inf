import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Analysis.Complex.Basic

namespace ALG1

open Matrix

theorem Zad10_1a : !![0, 1, 1; 1, 0, 1; 1, 1, 0].det = (2 : ℤ) := rfl

theorem Zad10_1b : !![1, 0, 0, 1; 0, 2, 0, 1; 1, 0, 1, 1; 1, 1, 0, 1].det = -1 := rfl

open Complex in
theorem Zad10_1c : !![1, 0, 1+I; 0, 1, I; 1-I, -I, 1].det = -2 := by
  simp [det_fin_three, ← sq_sub_sq]; norm_num

/-- 5x5 already reaches the recursion limit when trying to prove it with just `rfl` -/
theorem Zad10_1d : !![1, 2, 3, 4, 5;
                      2, 2, 3, 4, 5;
                      3, 3, 3, 4, 5;
                      4, 4, 4, 4, 5;
                      5, 5, 5, 5, 5].det = (5 : ℤ) := by
  simp [det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]

theorem Zad10_1e : !![1, 1, 1, 1, 1;
                      1, 2, 2, 2, 2;
                      1, 2, 3, 3, 3;
                      1, 2, 3, 4, 5;
                      1, 2, 3, 4, 5].det = (0 : ℤ) :=
  det_zero_of_row_eq (show 3 ≠ 4 by simp) rfl

theorem Zad10_1f : !![2,  1,  2, 3,  1;
                      3, -2,  5, 4,  3;
                      4,  2,  1, 0,  2;
                      1,  3, -1, 3, -1;
                      2,  1,  4, 3,  2].det = 12 := by
  simp [det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]

theorem Zad10_1g [CommRing R] (x y z t : R) :
    !![2, 1, 1, x; 1, 2, 1, y; 1, 1, 2, z; 1, 1, 1, t].det = 4 * t - x - y - z := by
  rw [det_succ_column _ 3]; simp [Fin.sum_univ_four, det_fin_three, Fin.succAbove]; ring

theorem Zad10_1h [CommRing R] (x y z : R) :
    !![0, x, y, z; x, 0, z, y; y, z, 0, x; z, y, x, 0].det =
    x ^ 4 + y ^ 4 + z ^ 4 - 2 * (x ^ 2 * y ^ 2 + x ^ 2 * z ^ 2 + y ^ 2 * z ^ 2) := by
  simp [det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]; ring

theorem Zad10_2 : !![1,  1,  1, 0,  0,  0;
                     2,  3,  4, 0,  0,  0;
                     3,  6, 10, 0,  0,  0;
                     4,  9, 14, 1,  1,  1;
                     5, 15, 24, 1,  5,  9;
                     0, 24, 38, 1, 25, 81].det = (128 : ℤ) := by
  rw [twoBlockTriangular_det' _ (· < 3)]
  · rfl
  · intro i hi j hj; fin_cases i <;> fin_cases j <;> simp_all

theorem Zad10_4a {x y z t : ℝ} (h1 : x + 2 * y + 3 * z + 4 * t = 11)
    (h2 : 2 * x + 3 * y + 4 * z + t = 12) (h3 : 3 * x + 4 * y + z + 2 * t = 13)
    (h4 : 4 * x + y + 2 * z + 3 * t = 14) : t = 1 := by grind

theorem Zad10_4b {x y z t : ℝ} (h1 : 2 * x + 3 * y + 5 * z + 11 * t = 2)
    (h2 : x + y + 2 * z + 5 * t = 1) (h3 : 2 * x + y + 2 * z + 3 * t = -3)
    (h4 : x + y + 4 * z + 3 * t = -3) : t = 1 := by grind

open Finset

theorem Zad10_D1 [DecidableEq n] [Fintype n] [CommRing R] [DecidableEq R] {A : Matrix n n R}
    (h : Fintype.card n ^ 2 - Fintype.card n < #{(i, j) | A i j = 0}) : A.det = 0 := by
  have : #{(i, j) | A i j ≠ 0} < Fintype.card n := by
    simp_rw [Ne, ← compl_filter, card_compl]; rw [tsub_lt_iff_tsub_lt (card_le_univ _)]
    · convert h; simp [sq]
    · simpa using Nat.le_mul_self _
  have : #{i | ∃ j, A i j ≠ 0} < Fintype.card n := by
    apply this.trans_le'; convert card_image_le (β := n) (f := Prod.fst)
    ext i; simp
  have ⟨i, hi⟩ : ∃ i, ∀ j, A i j = 0 := by simpa using exists_mem_notMem_of_card_lt_card this
  exact det_eq_zero_of_row_eq_zero i hi

theorem Zad10_D2 [DecidableEq n] [Fintype n] (A : Matrix n n ℤ) : IsUnit A ↔ (A.det = 1 ∨ A.det = -1) :=
  A.isUnit_iff_isUnit_det.trans A.det.isUnit_iff

theorem Zad10_D3a : (!![1, 2, 0, 0; 2, 3, 0, 0; 1, -1, 1, 3; 0, 1, 0, 2]⁻¹ : Matrix _ _ ℚ) =
    !![-3, 2, 0, 0; 2, -1, 0, 0; 8, -(9 / 2), 1, -(3 / 2); -1, 1 / 2, 0, 1 / 2] := by
  apply inv_eq_left_inv; norm_num
  ext i j; fin_cases i <;> fin_cases j <;> rfl

open Complex in
theorem Zad10_D3b : !![1+I, I, 1-I; I, I, 0; 1, 0, 4]⁻¹ =
    (10⁻¹ : ℂ) • !![12 - 4 * I, -12 + 4 * I, -2 + 4 * I;
                    -12 + 4 * I, 12 - 14 * I, 2 - 4 * I;
                    -3 + I, 3 - I, 3 - I] := by
  apply inv_eq_left_inv; norm_num; ring_nf; norm_num [← one_fin_three]

theorem Zad10_D4 [DecidableEq n] [Fintype n] {A : Matrix n n ℂ} (hA : A.IsHermitian) : A.det.im = 0 := by
  apply A.det.im_eq_zero_iff_isSelfAdjoint.mpr
  rw [IsSelfAdjoint, ← det_conjTranspose, hA]
