import Inf.ALG2.Sylvester
import Inf.ALG2.Cwi2
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Inf.ALG1.Cwi9
import Mathlib.MeasureTheory.Function.L2Space

open Real Matrix InnerProductSpace RealInnerProductSpace

namespace ALG2.Cwi3.Zad1

lemma posDef : !![1, 0, 1; 0, 2, 0; 1, 0, (3 : ℝ)].PosDef := by simp [IsSymm.ext_iff]

noncomputable scoped instance normedAddCommGroup : NormedAddCommGroup (Fin 3 → ℝ) :=
  toNormedAddCommGroup _ posDef

noncomputable scoped instance innerProductSpace :
    @InnerProductSpace ℝ (Fin 3 → ℝ) _ normedAddCommGroup.toSeminormedAddCommGroup :=
  toInnerProductSpace _ posDef.posSemidef

@[simp]
theorem inner_def {x y : Fin 3 → ℝ} :
    ⟪x, y⟫ = x 0 * y 0 + 2 * x 1 * y 1 + 3 * x 2 * y 2 + x 0 * y 2 + x 2 * y 0 := by
  simp [inner, vecHead, vecTail]; ring

end Zad1

open Zad1 in
theorem Zad1a : (ℝ ∙ ![1, 1, (1 : ℝ)])ᗮ = Submodule.span ℝ {![1, 1, -1], ![1, -1, 0]} := by
  ext v; simp [Submodule.mem_orthogonal_singleton_iff_inner_right, Submodule.mem_span_pair]; constructor
  · intro h; exists -v 2, v 0 + v 2; apply funext; simp; linarith
  · rintro ⟨a, b, rfl⟩; simp; ring

open Zad1 in
theorem Zad1b : (Submodule.span ℝ {![1, 1, 0], ![0, 1, (1 : ℝ)]})ᗮ = ℝ ∙ ![2, -1, 0] := by
  ext v; simp [Submodule.mem_orthogonal, Submodule.mem_span_pair, Submodule.mem_span_singleton]
  constructor
  · intro h; use -v 1; ext i; fin_cases i <;> simp
    · specialize h ![3, 2, -1] 3 (-1) (by norm_num); simp at h; linarith
    · specialize h ![1, 0, -1] 1 (-1) (by simp); simp at h; linarith
  · rintro ⟨a, rfl⟩ _ x z rfl; simp; ring

open Cwi2.Zad3 in
theorem Zad2 [Fintype n] [DecidableEq n] : SymmMatrix n ℝ ⟂ SkewSymmMatrix n ℝ := by
  rw [Submodule.isOrtho_iff_inner_eq]; simp [SymmMatrix, SkewSymmMatrix, Matrix.IsSymm]
  intro A hA B hB; nth_rw 1 [← self_eq_neg, ← add_eq_zero_iff_eq_neg, ← trace_transpose_mul,
    hA, hB, mul_neg, trace_neg, neg_add_cancel]

alias Zad3 := parallelogram_law_with_norm
alias Zad5 := sq_sum_le_card_mul_sum_sq

theorem Zad4 [CommSemiring α] [LinearOrder α] [IsStrictOrderedRing α] [ExistsAddOfLE α] (a b c : α) :
    a * b + b * c + c * a ≤ a ^ 2 + b ^ 2 + c ^ 2 := by
  apply le_of_mul_le_mul_left; case a0 => exact two_pos
  apply le_of_add_le_add_left (a := a ^ 2 + b ^ 2 + c ^ 2)
  convert Zad5 (s := .univ) (f := ![a, b, c]) using 1 <;> simp [Fin.sum_univ_three] <;> ring

namespace Zad6

open Polynomial

@[implicit_reducible]
noncomputable def core : Core ℝ ℝ[X] where
  inner p q := ∫ x in 0..1, p.eval x * q.eval x
  conj_inner_symm p q := by simp [mul_comm]
  re_inner_nonneg p := by simpa [← sq] using intervalIntegral.integral_nonneg zero_le_one (by bound)
  add_left p q r := by simp [add_mul]; apply intervalIntegral.integral_add <;>
    apply ContinuousOn.intervalIntegrable <;> fun_prop
  smul_left p q c := by simp [mul_assoc]
  definite p := by
    simp [← sq]; rw [intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae zero_le_one]
    · intro h; have := MeasureTheory.Measure.eqOn_Ioc_of_ae_eq _ h (by fun_prop) (by fun_prop)
      apply eq_zero_of_infinite_isRoot; apply (Set.Ioc_infinite one_pos).mono
      simp_all [Set.EqOn, Set.subset_def]
    · filter_upwards; simp; bound
    · apply ContinuousOn.intervalIntegrable; fun_prop

noncomputable scoped instance normedAddCommGroup : NormedAddCommGroup ℝ[X] :=
  core.toNormedAddCommGroup

noncomputable scoped instance innerProductSpace : InnerProductSpace ℝ ℝ[X] :=
  ofCore core.toCore

lemma inner_eq_integral {p q : ℝ[X]} :
    ⟪p, q⟫ = ∫ x in 0..1, p.eval x * q.eval x := rfl

@[simp]
lemma inner_degreeLT_eq {p q : ℝ[X]_n} : ⟪p, q⟫ =
    ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, p.val.coeff i * q.val.coeff j / (i + j + 1) := by
  simp [inner_eq_integral, eval_eq_sum_degreeLTEquiv p.property, eval_eq_sum_degreeLTEquiv q.property,
    degreeLTEquiv, Fin.sum_univ_eq_sum_range fun i => _ * _, Finset.sum_mul_sum]
  rw [intervalIntegral.integral_finsetSum fun i hi => ContinuousOn.intervalIntegrable (by fun_prop)]
  congr! with i hi
  rw [intervalIntegral.integral_finsetSum fun j hj => ContinuousOn.intervalIntegrable (by fun_prop)]
  congr! with j hj; simp [mul_assoc, ← mul_left_comm (q.val.coeff j), ← pow_add]; ring

theorem first : (gramSchmidt ℝ (degreeLT.basis ℝ 3) 0).val = 1 := by
  rw [gramSchmidt_def, ← Fintype.sum_ite_mem]; simp

theorem second : (gramSchmidt ℝ (degreeLT.basis ℝ 3) 1).val = X - C 2⁻¹ := by
  rw [gramSchmidt_def, ← Fintype.sum_ite_mem]
  norm_num [Submodule.starProjection_singleton, ← real_inner_self_eq_norm_sq, -inner_self_eq_norm_sq_to_K,
    first, Finset.sum_range_succ, coeff_one, coeff_X, smul_eq_C_mul, -Submodule.coe_inner, -Submodule.coe_norm]

theorem third : (gramSchmidt ℝ (degreeLT.basis ℝ 3) 2).val = X ^ 2 - X + C 6⁻¹ := by
  rw [gramSchmidt_def, ← Fintype.sum_ite_mem]
  norm_num [Submodule.starProjection_singleton, ← real_inner_self_eq_norm_sq, -inner_self_eq_norm_sq_to_K,
    Fin.sum_univ_succ, Fin.lt_def, first, second, Finset.sum_range_succ, coeff_one, coeff_X, smul_eq_C_mul,
    -Submodule.coe_inner, -Submodule.coe_norm]
  rw [show C (1 / 6 : ℝ) = C 2⁻¹ - C 3⁻¹ by norm_num [← C_sub]]; ring_nf

end Zad6

/-- Subspace `{(x, y, z) | x + 2 * y - z = 0}` of `EuclideanSpace ℝ (Fin 3)` -/
def Zad7.X : Submodule ℝ (EuclideanSpace ℝ (Fin 3)) :=
  .span ℝ {!₂[1, 0, 1], !₂[0, 1, 2]}

@[simp]
lemma Zad7.mem_X : x ∈ X ↔ x 0 + 2 * x 1 - x 2 = 0 := by
  simp [X, Submodule.mem_span_pair, PiLp.ext_iff, sub_eq_zero, mul_comm]

noncomputable def Zad7.basis : OrthonormalBasis (Fin 2) ℝ X :=
  gramSchmidtOrthonormalBasis (by
    rw [X, finrank_span_set_eq_card]; · simp
    apply linearIndepOn_id_pair (by simp); simp [PiLp.ext_iff]
  ) ![⟨!₂[1, 0, 1], by simp⟩, ⟨!₂[-1, 1, 1], by simp; norm_num⟩]

theorem Zad7a : Zad7.basis i = ![!₂[(√2)⁻¹, 0, (√2)⁻¹], !₂[-(√3)⁻¹, (√3)⁻¹, (√3)⁻¹]] i := by
  rw [Zad7.basis, gramSchmidtOrthonormalBasis_apply_of_orthogonal]
  case hf => simp [Pairwise, inner, Fin.sum_univ_three]
  all_goals fin_cases i <;> simp [PiLp.norm_eq_of_L2, Fin.sum_univ_three, ← WithLp.toLp_smul]
    <;> norm_num

theorem Zad7b : Zad7.X.starProjection !₂[x, y, z] =
    !₂[5 / 6 * x - y / 3 + z / 6, -(x / 3) + y / 3 + z / 3, x / 6 + y / 3 + 5 / 6 * z] := by
  simp [Zad7.basis.starProjection_eq_sum_rankOne, Zad7a, inner, Fin.sum_univ_three,
    PiLp.ext_iff, add_mul, mul_assoc, ← mul_inv]; ring_nf; trivial

theorem Zad8 : !![2024, 1; -1, 0] =
    ∑ i, ![-2024, 0, -1, 0] i • ![!![-1, 0; 0, 0], !![0, 2; 2, 1], !![0, -1; 1, 0], !![0, 1; -1, 4]] i := by
  simp [Fin.sum_univ_four, -zsmul_eq_mul]

end ALG2.Cwi3

theorem Module.Basis.isCompl_span_image [Semiring R] [AddCommMonoid M] [Module R M]
    (b : Basis ι R M) (s : Set ι) :
    IsCompl (Submodule.span R (b '' s)) (Submodule.span R (b '' sᶜ)) where
  disjoint := by
    simp_rw [Submodule.disjoint_def, mem_span_image, ← and_imp, ← Set.subset_inter_iff]; simp
  codisjoint := by
    simp [Submodule.codisjoint_iff_exists_add_eq, mem_span_image]; intro z; classical
    use b.repr.symm ((b.repr z).filter (· ∈ s)), by simp [Set.subset_def],
        b.repr.symm ((b.repr z).filter (· ∉ s)), by simp [Set.subset_def]
    rw [← map_add, Finsupp.filter_add_filter_not, LinearEquiv.symm_apply_apply]

theorem Module.Basis.toMatrix_projection_span_image [CommRing R] [AddCommGroup M] [Module R M]
    [Fintype ι] [DecidableEq ι] (b : Basis ι R M) (s : Set ι) [DecidablePred (· ∈ s)] :
    LinearMap.toMatrix b b (Submodule.projection _ _ (b.isCompl_span_image s))
    = diagonal (s.indicator 1) := by
  ext i j; simp [diagonal_apply, Set.indicator_apply, LinearMap.toMatrix_apply]
  by_cases h : j ∈ s
  · rw [Submodule.projection_apply_of_mem_left]; · split <;> simp [*]
    simp [mem_span_image]; grw [Finsupp.support_single_subset]; simpa
  · rw [Submodule.projection_apply_of_mem_right]; · simp +contextual [h]
    simp [mem_span_image]; grw [Finsupp.support_single_subset]; simpa

theorem LinearMap.toMatrix_of_toMatrix_map_left [CommSemiring R] [AddCommMonoid M₁] [Module R M₁]
    [AddCommMonoid M₂] [Module R M₂] [Fintype n] [DecidableEq n] [Finite m]
    (b₁ : Module.Basis n R M₁) (b₂ : Module.Basis m R M₂) (f : M₁ →ₗ[R] M₂) (g : M₁ ≃ₗ[R] M₁) :
    toMatrix b₁ b₂ f = toMatrix (b₁.map g) b₂ f * toMatrix b₁ b₁ g.symm := by
  simp [toMatrix_map_left, ← toMatrix_comp, comp_assoc]

theorem LinearMap.toMatrix_of_toMatrix_map_right [CommSemiring R] [AddCommMonoid M₁] [Module R M₁]
    [AddCommMonoid M₂] [Module R M₂] [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    (b₁ : Module.Basis n R M₁) (b₂ : Module.Basis m R M₂) (f : M₁ →ₗ[R] M₂) (g : M₂ ≃ₗ[R] M₂) :
    toMatrix b₁ b₂ f = toMatrix b₂ b₂ g * toMatrix b₁ (b₂.map g) f := by
  simp [toMatrix_map_right, ← toMatrix_comp]

@[simp]
theorem Matrix.toLinearEquiv_toLinearMap [CommRing R] [AddCommGroup M] [Module R M] [Fintype n]
    [DecidableEq n] (b : Module.Basis n R M) (A : Matrix n n R) (hA : IsUnit A.det) :
    toLinearEquiv b A hA = toLin b b A := rfl

@[simp]
theorem Matrix.toLinearEquiv_symm_toLinearMap [CommRing R] [AddCommGroup M] [Module R M] [Fintype n]
    [DecidableEq n] (b : Module.Basis n R M) (A : Matrix n n R) (hA : IsUnit A.det) :
    (toLinearEquiv b A hA).symm = toLin b b A⁻¹ := rfl

namespace ALG2.Cwi3.Zad9

open Polynomial

noncomputable def basis (R : Type*) [CommRing R] := (degreeLT.basis R 3).map
  (toLinearEquiv (degreeLT.basis R 3) !![1, 3, 1; -2, -5, -1; 3, 11, 4]
    (by simp [det_fin_three]; norm_num))

theorem basis_apply [CommRing R] (i : Fin 3) : (basis R i).val =
    ![1 - 2 * X + 3 * X ^ 2, 3 - 5 * X + 11 * X ^ 2, 1 - X + 4 * X ^ 2] i := by
  simp [basis, Fin.sum_univ_three]; fin_cases i <;> simp [smul_eq_C_mul, C_ofNat, sub_eq_add_neg]

noncomputable def P [CommRing R] := Submodule.projection _ _ ((basis R).isCompl_span_image {2})

theorem ker_P [CommRing R] : P.ker = Submodule.span R {basis R 0, basis R 1} := by
  simp [P]; suffices ({2}ᶜ : Set (Fin 3)) = {0, 1} by simp [this, Set.image_pair]
  ext i; fin_cases i <;> simp

theorem range_P [CommRing R] : P.range = R ∙ basis R 2 := by simp [P]

theorem toMatrix_P [CommRing R] : LinearMap.toMatrix (degreeLT.basis R 3) (degreeLT.basis R 3) P
    = !![7, 2, -1; -7, -2, 1; 28, 8, -4] := by
  have : LinearMap.toMatrix (basis R) (basis R) P = !![0, 0, 0; 0, 0, 0; 0, 0, 1] := by
    rw [P]; convert (basis R).toMatrix_projection_span_image {2}
    ext i j; fin_cases i <;> fin_cases j <;> simp
  rw [basis] at this
  rw [LinearMap.toMatrix_of_toMatrix_map_left, LinearMap.toMatrix_of_toMatrix_map_right, this]
  simp [inv_def, det_fin_three]; norm_num

end Zad9

alias Zad13a := Submodule.reflection_apply

theorem ZadD1 [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fintype n] [Nonempty n]
    (b : Module.Basis n ℝ V) : 0 < ∑ i, ∑ j, Matrix.gram ℝ b i j := calc
  0 < ⟪∑ i, (1 : n → ℝ) i • b i, ∑ i, (1 : n → ℝ) i • b i⟫ := by
    rw [real_inner_self_pos, ← Module.Basis.equivFun_symm_apply, LinearEquiv.map_ne_zero_iff]; simp
  _ = 1 ⬝ᵥ gram ℝ b *ᵥ 1 := (star_dotProduct_gram_mulVec b 1 1).symm
  _ = ∑ i, ∑ j, Matrix.gram ℝ b i j := by simp [dot_mulVec_eq_sum_sum, real_inner_comm]

lemma _root_.Finset.sum_vsub_centroid_id [DivisionRing k] [CharZero k] [AddCommGroup V]
    [Module k V] [AddTorsor V P] (s : Finset P) : ∑ a ∈ s, (a -ᵥ s.centroid k id) = 0 := by
  by_cases! h : s.Nonempty
  case neg => simp [h]
  have p := Classical.arbitrary P
  simp_rw [← vsub_sub_vsub_cancel_right _ (s.centroid k id) p, s.sum_sub_distrib, s.sum_const,
    s.centroid_def k, ← s.sum_smul_vsub_const_eq_affineCombination_vsub _ id p
      (s.sum_centroidWeights_eq_one_of_nonempty k h), id, Finset.centroidWeights_apply,
    ← s.smul_sum, ← Nat.cast_smul_eq_nsmul k, smul_smul]
  rw [mul_inv_cancel₀ (by simp [h.ne_empty]), one_smul, sub_self]

abbrev _root_.Finset.moment [Dist α] (s : Finset α) (x : α) := ∑ a ∈ s, (dist a x) ^ 2

theorem ZadD7 [SeminormedAddCommGroup V] [InnerProductSpace ℝ V] [PseudoMetricSpace P]
    [NormedAddTorsor V P] (s : Finset P) (x : P) : s.moment (s.centroid ℝ id) ≤ s.moment x := by
  rw [← vsub_vadd x (s.centroid ℝ id)]; generalize x -ᵥ Finset.centroid ℝ s id = v; clear x
  simp_rw [Finset.moment, dist_eq_norm_vsub, vsub_vadd_eq_vsub_sub, norm_sub_sq_real, add_comm_sub,
    s.sum_add_distrib, le_add_iff_nonneg_right, s.sum_sub_distrib, sub_nonneg, ← s.mul_sum,
    ← sum_inner, s.sum_vsub_centroid_id, inner_zero_left, mul_zero]; positivity

theorem ZadD8 [SeminormedAddCommGroup V] [InnerProductSpace ℝ V] (x y : V) :
    [⟪x, y⟫ = 0, ‖x + y‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2, ‖x + y‖ = ‖x - y‖].TFAE := by
  tfae_have 2 ↔ 1 := by
    convert norm_add_sq_eq_norm_sq_add_norm_sq_iff_real_inner_eq_zero x y <;> apply sq
  tfae_have 1 → 3 := fun h => (norm_sub_eq_norm_add (real_inner_comm x y ▸ h)).symm
  tfae_have 3 → 2 := by intro h; have := parallelogram_law_with_norm ℝ x y; grind only
  tfae_finish

alias ZadD9 := Finset.sum_mul_sq_le_sq_mul_sq

open MeasureTheory in
attribute [local instance] Measure.Subtype.measureSpace in
theorem ZadD10 {f g : ℝ → ℝ} (hab : a ≤ b) (hf : ContinuousOn f (Set.Icc a b))
    (hg : ContinuousOn g (Set.Icc a b)) :
    (∫ x in a..b, f x * g x) ^ 2 ≤ (∫ x in a..b, f x ^ 2) * ∫ x in a..b, g x ^ 2 := by
  let f' : C(Set.Icc a b, ℝ) := ⟨_, hf.restrict⟩
  let g' : C(Set.Icc a b, ℝ) := ⟨_, hg.restrict⟩
  simp_rw [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc,
    ← integral_subtype measurableSet_Icc, ← Set.restrict_apply]
  change (∫ x, f' x * g' x) ^ 2 ≤ (∫ x, f' x ^ 2) * ∫ x, g' x ^ 2
  convert real_inner_mul_inner_self_le (ContinuousMap.toLp 2 volume ℝ f') (ContinuousMap.toLp 2 volume ℝ g')
   <;> simp [← sq, ContinuousMap.inner_toLp, -inner_self_eq_norm_sq_to_K, mul_comm]

section variable [Semifield R] [LinearOrder R] [IsStrictOrderedRing R] [ExistsAddOfLE R]

theorem ZadD11 (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hd : 0 < d) (h : a + b + c + d = (1 : R)) :
    1 / 2 ≤ a ^ 2 / (a + b) + b ^ 2 / (b + c) + c ^ 2 / (c + d) + d ^ 2 / (d + a) := by
  convert Finset.univ.sq_sum_div_le_sum_sq_div ![a, b, c, d] (g := ![a + b, b + c, c + d, d + a])
    (by simp [Fin.forall_fin_succ]; and_intros <;> positivity)
  · simp [Fin.sum_univ_four, h]
  · simp [Fin.sum_univ_four]; ring_nf; simpa [← add_mul]
  · simp [Fin.sum_univ_four]

open Polynomial in
theorem ZadD12 {p : R[X]} (hp : ∀ n, 0 ≤ p.coeff n) (h : 1 ≤ p.eval 1) :
    ∀ x > 0, (p.eval x)⁻¹ ≤ p.eval x⁻¹ := by
  intro x hx; rw [gt_iff_lt] at hx; simp [eval_eq_sum, sum_def] at ⊢ h
  calc (∑ n ∈ p.support, p.coeff n * x ^ n)⁻¹
  _ ≤ (∑ n ∈ p.support, p.coeff n) ^ 2 / ∑ n ∈ p.support, p.coeff n * x ^ n := by
    rw [← one_div]; exact div_le_div_of_nonneg_right (one_le_pow₀ h)
      (Finset.sum_nonneg fun n _ => mul_nonneg (hp n) (pow_pos hx n).le)
  _ ≤ ∑ n ∈ p.support, p.coeff n ^ 2 / (p.coeff n * x ^ n) :=
    p.support.sq_sum_div_le_sum_sq_div _ fun n hn =>
      mul_pos ((hp n).lt_of_ne' (mem_support_iff.mp hn)) (pow_pos hx n)
  _ = ∑ n ∈ p.support, p.coeff n * (x ^ n)⁻¹ := by field_simp

theorem ZadD14 {a b c : R} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    3 / 2 ≤ a / (b + c) + b / (c + a) + c / (a + b) := by
  rw [← add_le_add_iff_right 3, ← div_le_div_iff_of_pos_right (add_pos (add_pos ha hb) hc)]
  convert Finset.univ.sq_sum_div_le_sum_sq_div ![1, 1, 1] (g := ![b + c, c + a, a + b])
   (by simp; and_intros <;> apply add_pos <;> assumption) using 1
   <;> (simp [Fin.sum_univ_three]; field)

end

alias ZadD17 := Orthonormal.sum_inner_products_le

alias ZadD18 := IsStarProjection.one_sub
