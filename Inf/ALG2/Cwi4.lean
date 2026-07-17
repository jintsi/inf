import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Inf.ALG2.Sylvester
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Inf.ALG1.Cwi9
import Mathlib.LinearAlgebra.CrossProduct

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

noncomputable def Zad5.B := (degreeLT.basis ℝ 2).ofDetNeZero
  ![⟨1 + X, by rw [mem_degreeLT]; compute_degree!⟩, ⟨1 - 2 * X, by rw [mem_degreeLT]; compute_degree!⟩]
  (by norm_num [det_fin_two, Basis.toMatrix_apply, coeff_one])

theorem Zad5.B_eq : (B i).val = ![1 + X, 1 - 2 * X] i := by revert i; simp [B]

/-- Basis `C = ![3 - X, 2 + X]`. -/
noncomputable def Zad5.C := (degreeLT.basis ℝ 2).ofDetNeZero
  ![⟨3 - X, by rw [mem_degreeLT]; compute_degree!⟩, ⟨2 + X, by rw [mem_degreeLT]; compute_degree!⟩]
  (by norm_num [det_fin_two, Basis.toMatrix_apply])

theorem Zad5.C_eq : (C i).val = ![3 - X, 2 + X] i := by revert i; simp [C]

theorem Zad5 : Zad5.B.orientation = -Zad5.C.orientation := by
  trans -(degreeLT.basis ℝ 2).orientation
  · rw [← Basis.orientation_ne_iff_eq_neg]; symm
    norm_num [Basis.orientation_eq_iff_det_pos, Basis.det, det_fin_two,
      Basis.toMatrix_apply, Zad5.B_eq, coeff_one]
  · congr 1; norm_num [Basis.orientation_eq_iff_det_pos, Basis.det, det_fin_two,
      Basis.toMatrix_apply, Zad5.C]

theorem Zad6 [Field K] [LinearOrder K] [IsStrictOrderedRing K] [AddCommGroup V]
    [Module K V] (b : Basis (Fin 2) K V) (f : V ≃ₗ[K] V) (hf : f.toMatrix b b = !![1, 2; -1, 0])
    (x : Orientation K V (Fin 2)) : x.map _ f = x := by
  have := b.finiteDimensional_of_finite
  simp [Orientation.map_eq_iff_det_pos x f (finrank_eq_card_basis b).symm,
    ← LinearMap.det_toMatrix b, hf]

end ALG2.Cwi4

/-! # Generalized cross product -/

/-- Given an alternating map `f` in `n+1` variables, split the last variable to obtain an
alternating map in `n` variables taking values in linear maps, given by `m ↦ (x ↦ f (snoc m x))`.

This is the `AlternatingMap` version of `MultilinearMap.curryRight`. TODO: this really should
rather belong in `Mathlib.LinearAlgebra.Alternating.Curry`. -/
@[simps!]
def AlternatingMap.curryRight [CommSemiring R] [AddCommMonoid M] [Module R M] [AddCommMonoid N]
    [Module R N] (f : M [⋀^Fin n.succ]→ₗ[R] N) : M [⋀^Fin n]→ₗ[R] (M →ₗ[R] N) where
  toMultilinearMap := f.toMultilinearMap.curryRight
  map_eq_zero_of_eq' v i j h hne := by
    ext x; apply f.map_eq_zero_of_eq (i := i.castSucc) (j := j.castSucc) <;> simpa

section CrossProduct

open InnerProductSpace RealInnerProductSpace

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [_i : Fact (finrank ℝ E = .succ n)] (o : Orientation ℝ E (Fin n.succ))

/-- `n`-ary cross product (or "external product") in an oriented `n+1`-dimensional real inner
product space, with `Orientation.mixed_product_apply` as its defining equation. -/
noncomputable def Orientation.crossProduct : E [⋀^Fin n]→ₗ[ℝ] E :=
  LinearMap.compAlternatingMap ((toDual ℝ E).symm.toLinearMap ∘ₗ
    LinearMap.toContinuousLinearMap.toLinearMap) (AlternatingMap.curryRight o.volumeForm)

theorem Orientation.mixed_product_apply : ⟪o.crossProduct v, w⟫ = o.volumeForm (Fin.snoc v w) := by
  simp [crossProduct]

theorem Orientation.mixed_product_eq_det (b : OrthonormalBasis (Fin n.succ) ℝ E)
    (hb : b.toBasis.orientation = o) {v w} : ⟪o.crossProduct v, w⟫ = b.toBasis.det (Fin.snoc v w) := by
  rwa [mixed_product_apply, volumeForm_robust]

theorem Orientation.repr_crossProduct_apply (b : OrthonormalBasis (Fin n.succ) ℝ E)
    (hb : b.toBasis.orientation = o) {v i} : b.repr (o.crossProduct v) i =
    (-1) ^ (n + i) * ((b.toBasis.toMatrix v).submatrix i.succAbove id).det := by
  rw [b.repr_apply_apply, real_inner_comm, o.mixed_product_eq_det b hb, Basis.det_apply,
    det_succ_column _ (Fin.last n)]; simp [Basis.toMatrix_apply]
  rw [add_comm]; congr 2; ext r c; simp [Basis.toMatrix_apply]

noncomputable instance EuclideanSpace.oriented [RCLike 𝕜] [Fintype ι] [DecidableEq ι] :
    Module.Oriented 𝕜 (EuclideanSpace 𝕜 ι) ι where
  positiveOrientation := (basisFun ι 𝕜).toBasis.orientation

open WithLp in
/-- In `EuclideanSpace ℝ (Fin 3)`, `Orientation.crossProduct` gives the same result as
`crossProduct`. -/
@[simp]
theorem EuclideanSpace.crossProduct_eq_cross {v w : EuclideanSpace ℝ (Fin 3)} :
    positiveOrientation.crossProduct ![v, w] = toLp 2 (crossProduct v w) := by
  ext i; rw [← basisFun_repr, Orientation.repr_crossProduct_apply]
  case hb => rfl
  fin_cases i <;>
    (simp [det_fin_two, Basis.toMatrix_apply, Fin.succAbove, cross_apply]; norm_num [mul_comm])

end CrossProduct

namespace ALG2.Cwi4

open EuclideanSpace in
theorem Zad7 : positiveOrientation.crossProduct ![!₂[(1 : ℝ), 1, 2], !₂[2, 1, -1]] = !₂[-3, 5, -1] := by
  simp [cross_apply]; norm_num
