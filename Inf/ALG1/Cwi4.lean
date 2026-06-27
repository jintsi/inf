import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.Nat.EvenOddRec
import Mathlib.LinearAlgebra.Matrix.Block

namespace ALG1.Cwi4

theorem Zad1a : !![3, -2; 5, -4] * !![3, 4; 2, 5] = !![5, 2; 7, 0] := by simp

theorem Zad1b : !![3, 4; 2, 5] * !![3, -2; 5, -5] = !![29, -26; 31, -29] := by simp

theorem Zad1c : !![3, 1, 1; 2, 1, 2; 1, 2, 3] * !![1, 1, -1; 2, -1, 1; 1, 0, 1] =
    !![6, 2, -1; 6, 1, 1; 8, -1, 4] := by simp

theorem Zad1d (a b c : ℕ) : !![a, b, c; c, b, a; 1, 1, 1] * !![1, a, c; 1, b, b; 1, c, a] =
    !![a + b + c, a ^ 2 + b ^ 2 + c ^ 2, a * c + b ^ 2 + c * a;
       a + b + c, a * c + b ^ 2 + c * a, a ^ 2 + b ^ 2 + c ^ 2;
       3,         a + b + c,             a + b + c] := by
  simp [add_assoc, sq, mul_comm, add_comm, add_rotate']

theorem Zad1e : !![2, 1; 1, 3] ^ 3 = !![15, 20; 20, 35] := by simp [pow_succ]

open Real in
theorem Zad1f (α β : ℝ) : !![cos α, -sin α; sin α, cos α] * !![cos β, -sin β; sin β, cos β] =
    !![cos (α + β), -sin (α + β); sin (α + β), cos (α + β)] := by
  simp [sin_add, cos_add, sub_eq_add_neg, add_comm]

theorem Zad2a (n : ℕ) : !![0, 1; 1, 1] ^ (n + 1) =
    !![Nat.fib n, Nat.fib (n + 1); Nat.fib (n + 1), Nat.fib (n + 2)] := by
  induction n with simp_all [pow_succ, Nat.fib_add_two]

theorem Zad2b (L n : ℕ) : !![1, L, 0; 0, 1, L; 0, 0, 1] ^ n =
    !![1, n * L, (n.choose 2) * L ^ 2; 0, 1, n * L; 0, 0, 1] := by
  induction n with
    simp_all [Matrix.one_fin_three, pow_succ, add_mul, add_comm, Nat.choose_succ_succ', mul_assoc]

open Real in
theorem Zad2c (α : Real) (n : Nat) : !![cos α, -sin α; sin α, cos α] ^ n =
    !![cos (n * α), -sin (n * α); sin (n * α), cos (n * α)] := by
  induction n with
  | zero => simpa using Matrix.one_fin_two
  | succ n ih => rw [pow_succ, ih, Zad1f, Nat.cast_add_one, add_one_mul]

theorem Zad3 : !![1, 0, 0, 0, 0, 0, 0, 1;
                  0, 1, 0, 0, 0, 0, 1, 0;
                  0, 0, 1, 0, 0, 1, 0, 0;
                  0, 0, 0, 1, 1, 0, 0, 0;
                  0, 0, 0, 0, 2, 1, 0, 0;
                  0, 0, 0, 0, 0, 2, 0, 0;
                  0, 0, 0, 0, 0, 0, 3, 1;
                  0, 0, 0, 0, 0, 0, 0, 3] ^ 2 = !![1, 0, 0, 0, 0, 0, 0, 4;
                                                   0, 1, 0, 0, 0, 0, 4, 1;
                                                   0, 0, 1, 0, 0, 3, 0, 0;
                                                   0, 0, 0, 1, 3, 1, 0, 0;
                                                   0, 0, 0, 0, 4, 4, 0, 0;
                                                   0, 0, 0, 0, 0, 4, 0, 0;
                                                   0, 0, 0, 0, 0, 0, 9, 6;
                                                   0, 0, 0, 0, 0, 0, 0, 9] := by simp [sq]

theorem Zad4a : !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 2, 0; 0, 0, 0, 1] *
                !![1, 0,-1, 2; 2, 0, 0, 2; 1,-1, 3, 0; 0, 1, 1, 0] =
                !![1, 0,-1, 2; 2, 0, 0, 2; 2,-2, 6, 0; 0, 1, 1, 0] := by simp

theorem Zad4b : !![0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1] *
                !![1, 0,-1, 2; 2, 0, 0, 2; 1,-1, 3, 0; 0, 1, 1, 0] =
                !![1,-1, 3, 0; 2, 0, 0, 2; 1, 0,-1, 2; 0, 1, 1, 0] := by simp

theorem Zad4c : !![1, 0, 0, 0; 0, 1, 0, 3; 0, 0, 1, 0; 0, 0, 0, 1] *
                !![1, 0,-1, 2; 2, 0, 0, 2; 1,-1, 3, 0; 0, 1, 1, 0] =
                !![1, 0,-1, 2; 2, 3, 3, 2; 1,-1, 3, 0; 0, 1, 1, 0] := by simp

theorem Zad5a : (!![2, -2, 1; 2, 1, -2; 1, 2, 2]⁻¹ : Matrix _ _ ℚ) =
    !![2/9, 2/9, 1/9; -2/9, 1/9, 2/9; 1/9, -2/9, 2/9] :=
  Matrix.inv_eq_right_inv (by norm_num [← Matrix.one_fin_three])

theorem Zad5b : (!![1, 1, 1, 1; 1, 1, -1, -1; 1, -1, 1, -1; 1, -1, -1, 1]⁻¹ : Matrix _ _ ℚ) =
    !![1/4, 1/4, 1/4, 1/4; 1/4, 1/4, -1/4, -1/4; 1/4, -1/4, 1/4, -1/4; 1/4, -1/4, -1/4, 1/4] := by
  apply Matrix.inv_eq_right_inv; norm_num
  ext i j; fin_cases i <;> fin_cases j <;> rfl

theorem Zad5c : (!![2, 1, 0, 0, 0;
                    0, 2, 1, 0, 0;
                    0, 0, 2, 1, 0;
                    0, 0, 0, 0, 1;
                    0, 0, 0, 1, 0]⁻¹) = (!![1/2, -1/4,  1/8, 0, -1/8;
                                            0,    1/2, -1/4, 0,  1/4;
                                            0,    0,    1/2, 0, -1/2;
                                            0,    0,    0,   0,  1;
                                            0,    0,    0,   1,  0] : Matrix _ _ ℚ) := by
  apply Matrix.inv_eq_right_inv; norm_num
  ext i j; fin_cases i <;> fin_cases j <;> rfl

theorem Zad6a : ¬∃ X : Matrix _ _ ℚ, !![2, 4; -3, -6] * X = !![3, 2; 5, 4] := by
  simp; intro X hr1
  have hr2 := Matrix.smul_vecMul (-3/2 : ℚ) ![2, 4] X; norm_num at hr2
  rw [hr2, hr1]; norm_num

theorem Zad6b (y : Fin 3 → ℚ) : !![3, -1, 2; 4, -3 , 3; 1, 3, 0] *
    (!![8/5, 16/5, 14/5; 9/5, 3/5, 7/5; 0, 0, 0] + Matrix.of ![-3 • y, y, 5 • y]) =
    !![3, 9, 7; 1, 11, 7; 7, 5, 7] := by simp [Matrix.vecHead, Matrix.vecTail]; and_intros <;> ring

theorem Zad6c : (!![5, -6, 4; 3, -3, 2; 4, -5, 2] : Matrix _ _ ℚ)
    * (!![2; 3/2; 3/4] : Matrix _ _ ℚ) = !![4; 3; 2] := by norm_num

theorem Zad6d : !![2, 1; 3, 2] * !![24, 13; -34, -18] * !![-3, 2; 5, -3]
    = !![-2, 4; 3, -1] := by simp

theorem ZadD1a : !![2, 1, 1; 3, 0, 1] * !![3, 1; 2, 1; 1, 0] = !![9, 3; 10, 3] := by simp

theorem ZadD1a' : !![3, 1; 2, 1; 1, 0] * !![2, 1, 1; 3, 0, 1] = !![9, 3, 4; 7, 2, 3; 2, 1, 1] := by simp

theorem ZadD1b : !![3, 2, 1; 0, 1, 2] * !![1; 2; 3] = !![10; 8] := by simp

theorem ZadD1c : !![2; 1; 3] * !![1, 2, 3] = !![2, 4, 6; 1, 2, 3; 3, 6, 9] := by simp

theorem ZadD1c' : !![1, 2, 3] * !![2; 1; 3] = !![13] := by simp

theorem ZadD2a : !![0, a, b, c; a, 0, d, e; b, d, 0, f; c, e, f, 0] *
                 !![0, f, e, d; f, 0, c, b; e, c, 0, a; d, b, a, 0] =
                 !![a * f + b * e + c * d, 2 * b * c, 2 * a * c, 2 * a * b;
                    2 * d * e, a * f + d * c + e * b, 2 * a * e, 2 * a * d;
                    2 * d * f, 2 * b * f, b * e + d * c + f * a, 2 * b * d;
                    2 * e * f, 2 * c * f, 2 * c * e, c * d + e * b + f * a] := by simp; ring_nf; simp

theorem ZadD2b : !![3, 2; -4, -2] ^ 5 = !![3, -2; 4, 8] := by simp [pow_succ]

theorem ZadD2c : !![2, -2, 4; 1, -1, 2] * !![1, 0, 1, 2; 2, -1, 1, 3; 4, 1, 0, -3]
    = !![14, 6, 0, -14; 7, 3, 0, -7] := by simp

theorem ZadD2d : !![3; 5; (7 : ℤ)] * !![(213 : ℤ), 510, 128] * !![3; -1; -1] * !![(1 : ℤ), 2, 1]
    = !![3, 6, 3; 5, 10, 5; 7, 14, 7] := by simp

theorem ZadD3a (n : ℕ) : !![2, -1; 3, -2] ^ n = (if 2 ∣ n then 1 else !![2, -1; 3, -2]) := by
  induction n using Nat.twoStepInduction with simp_all [pow_add, sq, Matrix.one_fin_two]

theorem ZadD3b (n : ℕ) : !![2, 1, 0; 0, 2, 0; 0, 0, -3] ^ n =
    (!![2 ^ n, n * 2 ^ (n - 1), 0; 0, 2 ^ n, 0; 0, 0, (-3) ^ n] : Matrix _ _ ℤ) := by
  induction n with
  | zero => simp [Matrix.one_fin_three]
  | succ n ih => simp [pow_succ, ih]; cases n <;> simp; ring

alias ZadD4a := Matrix.diagonal_mul_diagonal

/-! `M.BlockTriangular id` is the way of stating that `M` is upper triangular,
`M.BlockTriangular OrderDual.toDual` gives lower triangular. -/

alias ZadD4bc := Matrix.BlockTriangular.mul
