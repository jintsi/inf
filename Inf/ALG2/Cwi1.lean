import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Inf.ALG1.Cwi11
import Mathlib.LinearAlgebra.Matrix.Stochastic

open Matrix

namespace ALG2

alias Zad1_1 := det_eq_prod_roots_charpoly

theorem Zad1_2 [Fintype n] [DecidableEq n] [Field K] (A : Matrix n n K) [Invertible A] (d : n → K) :
    (A * diagonal d * A⁻¹).trace = (A * diagonal d * A⁻¹).charpoly.roots.sum := by
  apply trace_eq_sum_roots_charpoly_of_splits
  have := charpoly_units_conj (unitOfInvertible A) (diagonal d); simp_all [charpoly_diagonal]

theorem Zad1_3 [CommSemiring R] [DecidableEq n] [Fintype n] {M : Matrix n n R} {v : n → R}
    {μ : R} (h : M *ᵥ v = μ • v) (P : Polynomial R) : P.aeval M *ᵥ v = P.eval μ • v := by
  induction P using Polynomial.induction_on
  case C a => simp [algebraMap_eq_diagonal, Pi.algebraMap_def]
  case add p q ihp ihq => simp [add_mulVec, add_smul, ihp, ihq]
  case monomial n a ih =>
    simp [← Algebra.smul_def, smul_mulVec, ← smul_smul] at ⊢ ih
    simp [pow_add, ← mulVec_mulVec, h, mulVec_smul, mul_comm, ← smul_smul]
    rw [smul_comm, ih, smul_comm]

alias Zad1_4 := aeval_self_charpoly

theorem Zad1_5 : !![(1 : ℚ), 2; 2, 1] ^ 2021 =
    (2⁻¹ : ℚ) • !![3 ^ 2021 - 1, 3 ^ 2021 + 1; 3 ^ 2021 + 1, 3 ^ 2021 - 1] := by
  rw [show !![(1 : ℚ), 2; 2, 1] = !![1, 1; -1, 1] * diagonal ![-1, 3] * !![1, 1; -1, 1]⁻¹ by
      norm_num [inv_def, diagonal, vecHead, vecTail],
    Matrix.conj_pow (by simp [isUnit_iff_isUnit_det]), diagonal_pow]
  simp [← vecMulᵣ_eq, vecMulᵣ, vecHead, vecTail, inv_def]; norm_num; grind => ring

theorem Zad1_6 : !![(0 : ℤ), 1; 2, 1] ^ 2023 - !![0, 1; 2, 1] ^ 2022 - 2 • !![0, 1; 2, 1] ^ 2021 = 0 := calc
  !![(0 : ℤ), 1; 2, 1] ^ 2023 - !![0, 1; 2, 1] ^ 2022 - 2 • !![0, 1; 2, 1] ^ 2021
  _ = !![0, 1; 2, 1] ^ 2021 * (!![0, 1; 2, 1] ^ 2 - !![0, 1; 2, 1] - 2) := by grind only
  _ = !![0, 1; 2, 1] ^ 2021 * 0 := by congr; ext i j; fin_cases i <;> fin_cases j <;> simp [sq, ofNat_apply]
  _ = 0 := by simp

theorem Zad1_7 [CommRing R] [Nontrivial R] [Fintype n] [DecidableEq n] [Nontrivial n]
    (M : Matrix n n R) : ¬LinearIndepOn R (fun i => M ^ i) (Finset.range (Fintype.card n ^ 2)) := by
  rw [not_linearIndepOn_finset_iff]; exists fun i => M.charpoly.coeff i; and_intros
  · rw [← Polynomial.aeval_eq_sum_range', Zad1_4]
    rw [charpoly_natDegree_eq_dim]; exact lt_self_pow₀ Fintype.one_lt_card one_lt_two
  · simp; use Fintype.card n, lt_self_pow₀ Fintype.one_lt_card one_lt_two
    apply Polynomial.coeff_ne_zero_of_eq_degree; simp

/-- Specialization of `IsUnit.mul_right_eq_zero`. -/
theorem Zad1_8 [Semiring R] [Fintype n] [DecidableEq n] {M N : Matrix n n R} (h : IsUnit M) :
    M * N = 0 ↔ N = 0 := h.mul_right_eq_zero

theorem Zad1_D1 [Semiring R] [PartialOrder R] [IsOrderedRing R] [Fintype n] [DecidableEq n]
    (A B : Matrix n n R) : A ∈ rowStochastic R n → B ∈ rowStochastic R n → A * B ∈ rowStochastic R n :=
  (rowStochastic R n).mul_mem

alias Zad1_D6 := Zad1_3

theorem Zad1_D7 [CommRing R] [IsReduced R] [DecidableEq n] [Fintype n] {M : Matrix n n R}
    (hM : IsNilpotent M) : M.charpoly = Polynomial.X ^ Fintype.card n := by
  have := isNilpotent_charpoly_sub_pow_of_isNilpotent hM
  simp_rw [Polynomial.isNilpotent_iff, isNilpotent_iff_eq_zero] at this
  rw [← sub_eq_zero]; ext i; simp only [Polynomial.coeff_zero, this]

alias Zad1_D9 := det_one_add_mul_comm
