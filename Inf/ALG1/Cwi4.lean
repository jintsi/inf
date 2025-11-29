import Mathlib.Tactic
import Mathlib.Data.Nat.EvenOddRec

namespace ALG1

theorem Zad4_1a : !![3, -2; 5, -4] * !![3, 4; 2, 5] = !![5, 2; 7, 0] := by simp
theorem Zad4_1b : !![3, 4; 2, 5] * !![3, -2; 5, -5] = !![29, -26; 31, -29] := by simp
theorem Zad4_1c : !![3, 1, 1; 2, 1, 2; 1, 2, 3] * !![1, 1, -1; 2, -1, 1; 1, 0, 1] =
    !![6, 2, -1; 6, 1, 1; 8, -1, 4] := by simp
theorem Zad4_1d (a b c : ℕ) : !![a, b, c; c, b, a; 1, 1, 1] * !![1, a, c; 1, b, b; 1, c, a] =
    !![a + b + c, a ^ 2 + b ^ 2 + c ^ 2, a * c + b ^ 2 + c * a;
       a + b + c, a * c + b ^ 2 + c * a, a ^ 2 + b ^ 2 + c ^ 2;
       3,         a + b + c,             a + b + c] := by
  simp; grind
theorem Zad4_1e : !![2, 1; 1, 3] ^ 3 = !![15, 20; 20, 35] := by simp [pow_succ]

open Real in
theorem Zad4_1f (α β : ℝ) : !![cos α, -sin α; sin α, cos α] * !![cos β, -sin β; sin β, cos β] =
    !![cos (α + β), -sin (α + β); sin (α + β), cos (α + β)] := by simp [sin_add, cos_add]; grind

theorem Zad4_2a (n : ℕ) : !![0, 1; 1, 1] ^ (n + 1) = !![Nat.fib n, Nat.fib (n + 1); Nat.fib (n + 1), Nat.fib (n + 2)] := by
  induction n
  case zero => simp
  case succ n ih =>
    rw [pow_succ, ih]
    simp [Nat.fib_add_two]

theorem Zad4_2b (L n : ℕ) : !![1, L, 0; 0, 1, L; 0, 0, 1] ^ n = !![1, n * L, (n.choose 2) * L ^ 2; 0, 1, n * L; 0, 0, 1] := by
  induction n
  case zero => simp; exact Matrix.one_fin_three
  case succ n ih =>
    simp [pow_succ, ih]; and_intros
    · exact (succ_nsmul' L n).symm
    · rw [mul_assoc, ← add_mul, Nat.choose_two_right, Nat.choose_two_right, Nat.triangle_succ, add_comm]
    · exact (succ_nsmul' L n).symm

open Real in
theorem Zad4_2c (α : Real) (n : Nat) : !![cos α, -sin α; sin α, cos α] ^ n =
    !![cos (n * α), -sin (n * α); sin (n * α), cos (n * α)] := by
  induction n
  case zero => simp; exact Matrix.one_fin_two
  case succ n ih => rw [pow_succ, ih, Zad4_1f]; grind

theorem Zad4_3 : !![1, 0, 0, 0, 0, 0, 0, 1;
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
                                                     0, 0, 0, 0, 0, 0, 0, 9] := by simp [pow_succ]

theorem Zad4_4a : !![1, 0, 0, 0; 0, 1, 0, 0; 0, 0, 2, 0; 0, 0, 0, 1] *
                  !![1, 0,-1, 2; 2, 0, 0, 2; 1,-1, 3, 0; 0, 1, 1, 0] =
                  !![1, 0,-1, 2; 2, 0, 0, 2; 2,-2, 6, 0; 0, 1, 1, 0] := by simp

theorem Zad4_4b : !![0, 0, 1, 0; 0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1] *
                  !![1, 0,-1, 2; 2, 0, 0, 2; 1,-1, 3, 0; 0, 1, 1, 0] =
                  !![1,-1, 3, 0; 2, 0, 0, 2; 1, 0,-1, 2; 0, 1, 1, 0] := by simp

theorem Zad4_4c : !![1, 0, 0, 0; 0, 1, 0, 3; 0, 0, 1, 0; 0, 0, 0, 1] *
                  !![1, 0,-1, 2; 2, 0, 0, 2; 1,-1, 3, 0; 0, 1, 1, 0] =
                  !![1, 0,-1, 2; 2, 3, 3, 2; 1,-1, 3, 0; 0, 1, 1, 0] := by simp

theorem Zad4_5a : (!![2, -2, 1; 2, 1, -2; 1, 2, 2]⁻¹ : Matrix _ _ ℚ) = !![2/9, 2/9, 1/9; -2/9, 1/9, 2/9; 1/9, -2/9, 2/9] := by
  apply Matrix.inv_eq_right_inv; norm_num; exact Matrix.one_fin_three.symm

theorem Zad4_5b : (!![1, 1, 1, 1; 1, 1, -1, -1; 1, -1, 1, -1; 1, -1, -1, 1]⁻¹ : Matrix _ _ ℚ) =
    !![1/4, 1/4, 1/4, 1/4; 1/4, 1/4, -1/4, -1/4; 1/4, -1/4, 1/4, -1/4; 1/4, -1/4, -1/4, 1/4] := by
  apply Matrix.inv_eq_right_inv; norm_num
  ext i j; fin_cases i <;> fin_cases j <;> rfl

theorem Zad4_5c : (!![2, 1, 0, 0, 0; 0, 2, 1, 0, 0; 0, 0, 2, 1, 0; 0, 0, 0, 0, 1; 0, 0, 0, 1, 0]⁻¹ : Matrix _ _ ℚ) =
    !![1/2, -1/4, 1/8, 0, -1/8; 0, 1/2, -1/4, 0, 1/4; 0, 0, 1/2, 0, -1/2; 0, 0, 0, 0, 1; 0, 0, 0, 1, 0] := by
  apply Matrix.inv_eq_right_inv; norm_num
  ext i j; fin_cases i <;> fin_cases j <;> rfl

theorem Zad4_6a : ¬∃ X : Matrix _ _ ℚ, !![2, 4; -3, -6] * X = !![3, 2; 5, 4] := by
  simp; intro X hr1
  have hr2 := Matrix.smul_vecMul (-3/2 : ℚ) ![2, 4] X; norm_num at hr2
  rw [hr2, hr1]; norm_num

theorem Zad4_6b (y : Fin 3 → ℚ) : !![3, -1, 2; 4, -3 , 3; 1, 3, 0] *
    (!![8/5, 16/5, 14/5; 9/5, 3/5, 7/5; 0, 0, 0] + Matrix.of ![-3 • y, y, 5 • y]) =
    !![3, 9, 7; 1, 11, 7; 7, 5, 7] := by simp [Matrix.vecHead, Matrix.vecTail]; and_intros <;> ring

theorem Zad4_6c : (!![5, -6, 4; 3, -3, 2; 4, -5, 2] : Matrix _ _ ℚ) * (!![2; 3/2; 3/4] : Matrix _ _ ℚ) =
    !![4; 3; 2] := by norm_num

theorem Zad4_6d : !![2, 1; 3, 2] * !![24, 13; -34, -18] * !![-3, 2; 5, -3] = !![-2, 4; 3, -1] := by simp

theorem Zad4_D3a (n : ℕ) : !![2, -1; 3, -2] ^ n = (if 2 ∣ n then 1 else !![2, -1; 3, -2]) := by
  induction n using Nat.evenOddRec
  case h0 => simp
  case h_even n ih => split at ih <;> (rw [pow_mul', ih, pow_two]; simp [Matrix.one_fin_two])
  case h_odd n ih => split at ih <;> (rw [pow_succ, pow_mul', ih, pow_two]; simp [Matrix.one_fin_two])

theorem Zad4_D3b (n : ℕ) : !![2, 1, 0; 0, 2, 0; 0, 0, -3] ^ n =
    (!![2 ^ n, n * 2 ^ (n - 1), 0; 0, 2 ^ n, 0; 0, 0, (-3) ^ n] : Matrix _ _ ℤ) := by
  induction n
  case zero => simp [Matrix.one_fin_three]
  case succ n ih =>
    rw [pow_succ, ih]; simp; and_intros <;> ring_nf
    simp; cases n <;> simp [pow_succ, mul_assoc]

theorem Zad4_D4a [Field α] (d₁ d₂ : Fin n → α) :
    Matrix.diagonal d₁ * Matrix.diagonal d₂ = Matrix.diagonal (d₁ * d₂) := Matrix.diagonal_mul_diagonal d₁ d₂

/-- Predicate `Matrix.BlockTriangular M id` is the way of stating that M is upper triangular. -/
theorem Zad4_D4b [Field α] {M N : Matrix (Fin n) (Fin n) α} (hM : M.BlockTriangular id) (hN : N.BlockTriangular id) :
    (M * N).BlockTriangular id := Matrix.BlockTriangular.mul hM hN

/-- Predicate `Matrix.BlockTriangular M Neg.neg`, or more generally `Matrix.BlockTriangular M OrderDual.toDual`
(`Neg.neg` only works here because `Fin` has it defined as negation modulo `n`) is the way of stating that M is lower triangular. -/
theorem Zad4_D4c [Field α] {M N : Matrix (Fin n) (Fin n) α} (hM : M.BlockTriangular Neg.neg) (hN : N.BlockTriangular Neg.neg) :
    (M * N).BlockTriangular Neg.neg := Matrix.BlockTriangular.mul hM hN
