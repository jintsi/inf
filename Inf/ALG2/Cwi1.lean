import Mathlib.LinearAlgebra.Matrix.Charpoly.Eigs
import Inf.ALG1.Cwi11
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
import Mathlib.LinearAlgebra.Matrix.Stochastic

open Matrix

namespace ALG2.Cwi1

alias Zad1 := det_eq_prod_roots_charpoly

theorem Zad2 [Fintype n] [DecidableEq n] [Field K] (A : Matrix n n K) [Invertible A] (d : n → K) :
    (A * diagonal d * A⁻¹).trace = (A * diagonal d * A⁻¹).charpoly.roots.sum := by
  apply trace_eq_sum_roots_charpoly_of_splits
  have := charpoly_units_conj (unitOfInvertible A) (diagonal d); simp_all [charpoly_diagonal]

theorem Zad3 [CommSemiring R] [DecidableEq n] [Fintype n] {M : Matrix n n R} {v : n → R}
    {μ : R} (h : M *ᵥ v = μ • v) (P : Polynomial R) : P.aeval M *ᵥ v = P.eval μ • v := by
  induction P using Polynomial.induction_on
  case C a => simp [algebraMap_eq_diagonal, Pi.algebraMap_def]
  case add p q ihp ihq => simp [add_mulVec, add_smul, ihp, ihq]
  case monomial n a ih =>
    simp [← Algebra.smul_def, smul_mulVec, ← smul_smul] at ⊢ ih
    simp [pow_add, ← mulVec_mulVec, h, mulVec_smul, mul_comm, ← smul_smul]
    rw [smul_comm, ih, smul_comm]

alias Zad4 := aeval_self_charpoly

set_option backward.isDefEq.respectTransparency.types false in
theorem Zad5 : !![(1 : ℚ), 2; 2, 1] ^ 2021 =
    (2⁻¹ : ℚ) • !![3 ^ 2021 - 1, 3 ^ 2021 + 1; 3 ^ 2021 + 1, 3 ^ 2021 - 1] := by
  rw [show !![(1 : ℚ), 2; 2, 1] = !![1, 1; -1, 1] * diagonal ![-1, 3] * !![1, 1; -1, 1]⁻¹ by
      norm_num [inv_def, diagonal, vecHead, vecTail],
    Matrix.conj_pow (by simp [isUnit_iff_isUnit_det]), diagonal_pow]
  simp [← vecMulᵣ_eq, vecMulᵣ, vecHead, vecTail, inv_def]; norm_num; grind => ring

theorem Zad6 : !![(0 : ℤ), 1; 2, 1] ^ 2023 - !![0, 1; 2, 1] ^ 2022 - 2 • !![0, 1; 2, 1] ^ 2021 = 0 := calc
  !![(0 : ℤ), 1; 2, 1] ^ 2023 - !![0, 1; 2, 1] ^ 2022 - 2 • !![0, 1; 2, 1] ^ 2021
  _ = !![0, 1; 2, 1] ^ 2021 * (!![0, 1; 2, 1] ^ 2 - !![0, 1; 2, 1] - 2) := by grind only
  _ = !![0, 1; 2, 1] ^ 2021 * 0 := by congr; ext i j; fin_cases i <;> fin_cases j <;> simp [sq, ofNat_apply]
  _ = 0 := by simp

theorem Zad7 [CommRing R] [Nontrivial R] [Fintype n] [DecidableEq n] [Nontrivial n]
    (M : Matrix n n R) : ¬LinearIndepOn R (fun i => M ^ i) (Finset.range (Fintype.card n ^ 2)) := by
  rw [not_linearIndepOn_finset_iff]; exists fun i => M.charpoly.coeff i; and_intros
  · rw [← Polynomial.aeval_eq_sum_range', Zad4]
    rw [charpoly_natDegree_eq_dim]; exact lt_self_pow₀ Fintype.one_lt_card one_lt_two
  · simp; use Fintype.card n, lt_self_pow₀ Fintype.one_lt_card one_lt_two
    apply Polynomial.coeff_ne_zero_of_eq_degree; simp

/-- Specialization of `IsUnit.mul_right_eq_zero`. -/
theorem Zad8 [Semiring R] [Fintype n] [DecidableEq n] {M N : Matrix n n R} (h : IsUnit M) :
    M * N = 0 ↔ N = 0 := h.mul_right_eq_zero

set_option backward.isDefEq.respectTransparency.types false in
theorem Zad9 [CommRing R] [IsDomain R] [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (h : Fintype.card n < Fintype.card m) (A : Matrix m n R)
    (B : Matrix n m R) : (A * B).det = 0 := by
  apply det_eq_zero_of_not_linearIndependent_rows
  rw [linearIndependent_iff_card_le_finrank_span, not_le]
  grw [← h]; classical trans Set.finrank R (Finset.image B Finset.univ : Set (m → R))
  · simp [Set.finrank]; apply Submodule.finrank_mono
    simp [Submodule.span_le, Set.subset_def, Submodule.mem_span_range_iff_exists_fun]
    intro i; use A i; ext j; simp [mul_apply]
  · simpa using finrank_range_le_card B

theorem Zad10 [CommRing R] [Fintype n] [DecidableEq n] (A B : Matrix n n R) :
    (fromBlocks A B B A).det = (A + B).det * (A - B).det := by
  trans (fromBlocks 1 0 (-1) 1 * fromBlocks (A - B) B 0 (A + B) * fromBlocks 1 0 1 1).det
  · simp [fromBlocks_multiply]
  · simp [mul_comm]

theorem ZadD1 [Semiring R] [PartialOrder R] [IsOrderedRing R] [Fintype n] [DecidableEq n]
    (A B : Matrix n n R) : A ∈ rowStochastic R n → B ∈ rowStochastic R n → A * B ∈ rowStochastic R n :=
  (rowStochastic R n).mul_mem

theorem ZadD4 [CommRing R] [Fintype n] [DecidableEq n] [Nonempty n] {M : Matrix n n R}
    (h : ∀ i j, Odd (M i j)) : 2 ^ (Fintype.card n - 1) ∣ M.det := by
  revert n; apply Fintype.induction_empty_option
  · intro n' n _ e ih _ _ M h
    specialize @ih e.decidableEq e.nonempty (M.submatrix e e) fun i j => h (e i) (e j)
    let := Fintype.ofEquiv n e.symm
    simpa [Fintype.card_congr e] using ih
  · simp
  rintro n _ - _ _ M h; choose M' h using h; change Matrix _ _ R at M'
  have : DecidableEq n := fun i j => decidable_of_iff (some i = some j) Option.some_inj
  have : M = (of fun i j => j.elim 1 fun j => if i = j then 2 else 0) *
             (of fun i => i.elim (M none) fun i => M' (some i) - M' none) := by
    ext i j; rcases i with _ | i <;> simp [mul_apply, h]; ring
  rw [this, det_mul]; apply dvd_mul_of_dvd_left
  rw [BlockTriangular.det_fintype (b := Option.isNone)]
  · simp [toSquareBlock_def]; apply dvd_mul_of_dvd_right; convert dvd_rfl
    convert det_diagonal (d := fun _ => (2 : R))
    · ext ⟨i, hi⟩ ⟨j, hj⟩; rcases i with _ | i; contradiction; rcases j with _ | j; contradiction
      simp [diagonal]
    · simp [Fintype.card_congr (Equiv.optionIsSomeEquiv n)]
    · infer_instance
    · infer_instance
  · simp +contextual [BlockTriangular, Bool.lt_iff, Option.isSome_iff_exists]

alias ZadD6 := Zad3

theorem ZadD7 [CommRing R] [IsReduced R] [DecidableEq n] [Fintype n] {M : Matrix n n R}
    (hM : IsNilpotent M) : M.charpoly = Polynomial.X ^ Fintype.card n := by
  have := isNilpotent_charpoly_sub_pow_of_isNilpotent hM
  simp_rw [Polynomial.isNilpotent_iff, isNilpotent_iff_eq_zero] at this
  rw [← sub_eq_zero]; ext i; simp only [Polynomial.coeff_zero, this]

alias ZadD9 := det_one_add_mul_comm
