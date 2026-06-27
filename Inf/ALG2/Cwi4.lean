import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Inf.ALG2.Sylvester
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.RingTheory.Polynomial.DegreeLT

open Matrix ComplexOrder Module Polynomial

theorem Orientation.volumeForm_sq_eq_det_gram [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {n : ℕ} [_i : Fact (finrank ℝ V = n)] (o : Orientation ℝ V (Fin n)) (v : Fin n → V) :
    o.volumeForm v ^ 2 = (gram ℝ v).det := by
  rcases n with _ | n
  · simp [o.volumeForm_def, Or.by_cases]; split <;> simp
  have := FiniteDimensional.of_finrank_eq_succ _i.elim
  have b := stdOrthonormalBasis ℝ V; rw [_i.elim] at b
  simp [gram_eq_conjTranspose_mul b, ← sq, sq_eq_sq_iff_abs_eq_abs, o.volumeForm_robust' b]; rfl

open MeasureTheory in
attribute [local instance] Measure.Subtype.measureSpace in
/-- This is, as far as I know, the best way to notate n-dimensional volume within an arbitrary
n-dimensional subspace. -/
theorem LinearIndependent.measure_parallelepiped_eq_sqrt_det_gram [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MeasurableSpace V] [BorelSpace V] {n : ℕ} {v : Fin n → V}
    (h : LinearIndependent ℝ v) (_i : Fact (finrank ℝ ↥(Submodule.span ℝ (Set.range v)) = n) := by
      simp [fact_iff, finrank_span_eq_card])
    (fd := FiniteDimensional.span_of_finite ℝ (Set.finite_range v)) :
    (Basis.span h).orientation.volumeForm.measure (parallelepiped fun i => ⟨v i,
      Submodule.mem_span_of_mem ⟨i, rfl⟩⟩) = ENNReal.ofReal √(gram ℝ v).det := by
  rw [AlternatingMap.measure_parallelepiped]; congr; symm; rw [Real.sqrt_eq_cases]; left
  simp [← sq, Orientation.volumeForm_sq_eq_det_gram]; congr 1

namespace ALG2.Cwi4

theorem Zad1 [RCLike K] {A : Matrix (Fin n) (Fin n) K} (hA : A.IsHermitian) :
    (∀ x ≠ 0, star x ⬝ᵥ A *ᵥ x < 0) ↔
    ∀ i : Fin n, 0 < (-1) ^ (i.val + 1) * (A.submatrix (Fin.castLE i.isLt) (Fin.castLE i.isLt)).det := by
  simpa [posDef_iff_dotProduct_mulVec, hA.neg, neg_mulVec, submatrix_neg, det_neg]
    using posDef_sylvester hA.neg

theorem Zad2 : !![(1 : ℝ), 1, -1; 1, 2, 1; -1, 1, 6].PosDef := by
  simp [IsSymm.ext_iff]; norm_num

lemma Zad4a_li : LinearIndependent ℝ ![!₂[(1 : ℝ), 1, 1], !₂[0, 1, 1]] := by
  simp [LinearIndependent.pair_iff', PiLp.ext_iff]

set_option linter.defProp false in
def Zad4a := (Zad4a_li.measure_parallelepiped_eq_sqrt_det_gram (by
  simp [fact_iff, finrank_span_eq_card Zad4a_li])).trans (by
  simp [det_fin_two, PiLp.norm_sq_eq_of_L2, PiLp.inner_apply, Fin.sum_univ_three]; norm_num; rfl)

theorem Zad4b : MeasureTheory.volume (parallelepiped
    ![!₂[(1 : ℝ), 0, 0], !₂[1, 1, 0], !₂[1, 1, 1]]) = 1 := by
  have _i : Fact (finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3) := by simp [fact_iff]
  rw [← Orientation.measure_eq_volume (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation,
    AlternatingMap.measure_parallelepiped, Orientation.volumeForm_robust]
  case hb => rfl
  simp [Basis.det, det_fin_three, Basis.toMatrix]

/-- Basis `B = ![1 + X, 1 - 2 * X]`. -/
noncomputable def Zad5.B : Basis (Fin 2) ℝ ℝ[X]_2 := by
  apply basisOfLinearIndependentOfCardEqFinrank
    (b := ![⟨1 + X, by rw [mem_degreeLT]; compute_degree!⟩,
    ⟨1 - 2 * X, by rw [mem_degreeLT]; compute_degree!⟩])
  · rw [LinearIndependent.pair_iff' (by simp [Polynomial.ext_iff]; exists 0; simp)]
    simp only [ne_eq, (degreeLT.basis ℝ 2).ext_elem_iff]; norm_num [coeff_one]
  · exact (finrank_eq_card_basis (degreeLT.basis ℝ 2)).symm

theorem Zad5.B_eq : (B i).val = ![1 + X, 1 - 2 * X] i := by fin_cases i <;> simp [B]

/-- Basis `C = ![3 - X, 2 + X]`. -/
noncomputable def Zad5.C : Basis (Fin 2) ℝ ℝ[X]_2 := by
  apply basisOfLinearIndependentOfCardEqFinrank
    (b := ![⟨3 - X, by rw [mem_degreeLT]; compute_degree!⟩,
    ⟨2 + X, by rw [mem_degreeLT]; compute_degree!⟩])
  · rw [LinearIndependent.pair_iff' (by simp [Polynomial.ext_iff]; exists 0; simp)]
    simp only [ne_eq, (degreeLT.basis ℝ 2).ext_elem_iff]; norm_num; grind
  · exact (finrank_eq_card_basis (degreeLT.basis ℝ 2)).symm

theorem Zad5.C_eq : (C i).val = ![3 - X, 2 + X] i := by fin_cases i <;> simp [C]

theorem Zad5 : Zad5.B.orientation = -Zad5.C.orientation := by
  trans -(degreeLT.basis ℝ 2).orientation
  · rw [← Basis.orientation_ne_iff_eq_neg]; symm
    norm_num [Basis.orientation_eq_iff_det_pos, Basis.det, det_fin_two,
      Basis.toMatrix_apply, Zad5.B, coeff_one]
  · congr 1; norm_num [Basis.orientation_eq_iff_det_pos, Basis.det, det_fin_two,
      Basis.toMatrix_apply, Zad5.C]

theorem Zad6 [Field K] [LinearOrder K] [IsStrictOrderedRing K] [AddCommGroup V]
    [Module K V] (b : Basis (Fin 2) K V) (f : V ≃ₗ[K] V) (hf : f.toMatrix b b = !![1, 2; -1, 0])
    (x : Orientation K V (Fin 2)) : x.map _ f = x := by
  have := b.finiteDimensional_of_finite
  simp [Orientation.map_eq_iff_det_pos x f (finrank_eq_card_basis b).symm,
    ← LinearMap.det_toMatrix b, hf]
