import Inf.ALG2.Sylvester
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.RingTheory.Polynomial.DegreeLT

open Matrix ComplexOrder Module Polynomial

namespace ALG2

theorem Zad4_1 [RCLike K] {A : Matrix (Fin n) (Fin n) K} (hA : A.IsHermitian) :
    (∀ x ≠ 0, star x ⬝ᵥ A *ᵥ x < 0) ↔
    ∀ i : Fin n, 0 < (-1) ^ (i.val + 1) * (A.submatrix (Fin.castLE i.isLt) (Fin.castLE i.isLt)).det := by
  simpa [posDef_iff_dotProduct_mulVec, hA.neg, neg_mulVec, submatrix_neg, det_neg]
    using posDef_sylvester hA.neg

theorem Zad4_2 : !![(1 : ℝ), 1, -1; 1, 2, 1; -1, 1, 6].PosDef := by
  simp [IsHermitian.ext_iff]; norm_num

theorem Zad4_4b : MeasureTheory.volume (parallelepiped
    ![!₂[(1 : ℝ), 0, 0], !₂[1, 1, 0], !₂[1, 1, 1]]) = 1 := by
  have _i : Fact (finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 3) := by simp [fact_iff]
  rw [← Orientation.measure_eq_volume (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation,
    AlternatingMap.measure_parallelepiped, Orientation.volumeForm_robust]
  case hb => rfl
  simp [Basis.det, det_fin_three, Basis.toMatrix]

/-- Basis `B = ![1 + X, 1 - 2 * X]`. -/
noncomputable def Zad4_5.B : Basis (Fin 2) ℝ ℝ[X]_2 := by
  apply basisOfLinearIndependentOfCardEqFinrank
    (b := ![⟨1 + X, by rw [mem_degreeLT]; compute_degree!⟩,
    ⟨1 - 2 * X, by rw [mem_degreeLT]; compute_degree!⟩])
  · rw [LinearIndependent.pair_iff' (by simp [Polynomial.ext_iff]; exists 0; simp)]
    simp only [ne_eq, (degreeLT.basis ℝ 2).ext_elem_iff]; norm_num [coeff_one]
  · exact (finrank_eq_card_basis (degreeLT.basis ℝ 2)).symm

theorem Zad4_5.B_eq : (B i).val = ![1 + X, 1 - 2 * X] i := by fin_cases i <;> simp [B]

/-- Basis `C = ![3 - X, 2 + X]`. -/
noncomputable def Zad4_5.C : Basis (Fin 2) ℝ ℝ[X]_2 := by
  apply basisOfLinearIndependentOfCardEqFinrank
    (b := ![⟨3 - X, by rw [mem_degreeLT]; compute_degree!⟩,
    ⟨2 + X, by rw [mem_degreeLT]; compute_degree!⟩])
  · rw [LinearIndependent.pair_iff' (by simp [Polynomial.ext_iff]; exists 0; simp)]
    simp only [ne_eq, (degreeLT.basis ℝ 2).ext_elem_iff]; norm_num; grind
  · exact (finrank_eq_card_basis (degreeLT.basis ℝ 2)).symm

theorem Zad4_5.C_eq : (C i).val = ![3 - X, 2 + X] i := by fin_cases i <;> simp [C]

theorem Zad4_5 : Zad4_5.B.orientation = -Zad4_5.C.orientation := by
  trans -(degreeLT.basis ℝ 2).orientation
  · rw [← Basis.orientation_ne_iff_eq_neg]; symm
    norm_num [Basis.orientation_eq_iff_det_pos, Basis.det, det_fin_two,
      Basis.toMatrix_apply, Zad4_5.B, coeff_one]
  · congr 1; norm_num [Basis.orientation_eq_iff_det_pos, Basis.det, det_fin_two,
      Basis.toMatrix_apply, Zad4_5.C]

theorem Zad4_6 [Field K] [LinearOrder K] [IsStrictOrderedRing K] [AddCommGroup V]
    [Module K V] (b : Basis (Fin 2) K V) (f : V ≃ₗ[K] V) (hf : f.toMatrix b b = !![1, 2; -1, 0])
    (x : Orientation K V (Fin 2)) : x.map _ f = x := by
  have := b.finiteDimensional_of_finite
  simp [Orientation.map_eq_iff_det_pos x f (finrank_eq_card_basis b).symm,
    ← LinearMap.det_toMatrix b, hf]
