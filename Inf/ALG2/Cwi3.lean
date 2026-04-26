import Inf.ALG2.Cwi2
import Inf.ALG1.Cwi7
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.InnerProductSpace.GramSchmidtOrtho
import Mathlib.RingTheory.Polynomial.DegreeLT

open Real Matrix InnerProductSpace RealInnerProductSpace

namespace ALG2.Zad3_1

lemma posDef : !![1, 0, 1; 0, 2, 0; 1, 0, (3 : ℝ)].PosDef := by
  apply PosDef.of_dotProduct_mulVec_pos (by simp [IsHermitian.ext_iff, Fin.forall_fin_succ])
  simp [← FinVec.forall_iff, FinVec.Forall, -not_and]; intro x y z h
  convert_to 0 < (x + z) ^ 2 + 2 * y ^ 2 + 2 * z ^ 2; · ring
  have : ¬(x + z = 0 ∧ y = 0 ∧ z = 0) := by grind only
  contrapose! this; and_intros <;> nlinarith

noncomputable scoped instance normedAddCommGroup : NormedAddCommGroup (Fin 3 → ℝ) :=
  toNormedAddCommGroup _ posDef

noncomputable scoped instance seminormedAddCommGroup : SeminormedAddCommGroup (Fin 3 → ℝ) :=
  toSeminormedAddCommGroup _ posDef.posSemidef

noncomputable scoped instance innerProductSpace : InnerProductSpace ℝ (Fin 3 → ℝ) :=
  toInnerProductSpace _ posDef.posSemidef

@[simp]
theorem inner_def {x y : Fin 3 → ℝ} :
    ⟪x, y⟫ = x 0 * y 0 + 2 * x 1 * y 1 + 3 * x 2 * y 2 + x 0 * y 2 + x 2 * y 0 := by
  simp [inner, vecHead, vecTail]; ring

end Zad3_1

open Zad3_1 in
theorem Zad3_1a : (ℝ ∙ ![1, 1, (1 : ℝ)]).orthogonal = Submodule.span ℝ {![1, 1, -1], ![1, -1, 0]} := by
  ext v; simp [Submodule.mem_orthogonal_singleton_iff_inner_right, Submodule.mem_span_pair]; constructor
  · intro h; exists -v 2, v 0 + v 2; apply funext; simp [Fin.forall_fin_succ]; linarith
  · rintro ⟨a, b, rfl⟩; simp; ring

open Zad3_1 in
theorem Zad3_1b : (Submodule.span ℝ {![1, 1, 0], ![0, 1, (1 : ℝ)]}).orthogonal = ℝ ∙ ![2, -1, 0] := by
  ext v; simp [Submodule.mem_orthogonal, Submodule.mem_span_pair, Submodule.mem_span_singleton]
  constructor
  · intro h; use -v 1; ext i; fin_cases i <;> simp
    · specialize h ![3, 2, -1] 3 (-1) (by norm_num); simp at h; linarith
    · specialize h ![1, 0, -1] 1 (-1) (by simp); simp at h; linarith
  · rintro ⟨a, rfl⟩ _ x z rfl; simp; ring

open Zad2_3 in
theorem Zad3_2 [Fintype n] [DecidableEq n] : ALG1.SymmMatrix n ℝ ⟂ ALG1.SkewSymmMatrix n ℝ := by
  rw [Submodule.isOrtho_iff_inner_eq]; simp [ALG1.SymmMatrix, ALG1.SkewSymmMatrix, Matrix.IsSymm]
  intro A hA B hB; nth_rw 1 [← self_eq_neg, ← add_eq_zero_iff_eq_neg, ← trace_transpose_mul,
    hA, hB, mul_neg, trace_neg, neg_add_cancel]

alias Zad3_3 := parallelogram_law_with_norm

alias Zad3_5 := sq_sum_le_card_mul_sum_sq

theorem Zad3_4 [CommSemiring α] [LinearOrder α] [IsStrictOrderedRing α] [ExistsAddOfLE α] (a b c : α) :
    a * b + b * c + c * a ≤ a ^ 2 + b ^ 2 + c ^ 2 := by
  apply le_of_mul_le_mul_left; case a0 => exact two_pos
  apply le_of_add_le_add_left (a := a ^ 2 + b ^ 2 + c ^ 2)
  convert Zad3_5 (s := .univ) (f := ![a, b, c]) using 1 <;> simp [Fin.sum_univ_three] <;> ring

namespace Zad3_6

open Polynomial

@[implicit_reducible]
noncomputable def core : Core ℝ (Polynomial.degreeLT ℝ n) where
  inner p q := ∫ x in 0..1, p.val.eval x * q.val.eval x
  conj_inner_symm p q := by simp [mul_comm]
  re_inner_nonneg p := by simpa [← sq] using intervalIntegral.integral_nonneg zero_le_one (by bound)
  add_left p q r := by simp [add_mul]; apply intervalIntegral.integral_add <;>
    apply ContinuousOn.intervalIntegrable <;> fun_prop
  smul_left p q c := by simp [mul_assoc]
  definite p := by
    simp [← sq]; rw [intervalIntegral.integral_eq_zero_iff_of_le_of_nonneg_ae zero_le_one]
    · intro h; have := MeasureTheory.Measure.eqOn_Ioc_of_ae_eq _ h (by fun_prop) (by fun_prop)
      ext1; apply eq_zero_of_infinite_isRoot; apply (Set.Ioc_infinite one_pos).mono
      simp_all [Set.EqOn, Set.subset_def]
    · filter_upwards; simp; bound
    · apply ContinuousOn.intervalIntegrable; fun_prop

noncomputable scoped instance normedAddCommGroup : NormedAddCommGroup (Polynomial.degreeLT ℝ n) :=
  core.toNormedAddCommGroup

noncomputable scoped instance innerProductSpace : InnerProductSpace ℝ (Polynomial.degreeLT ℝ n) :=
  ofCore core.toCore

lemma inner_eq_integral {p q : degreeLT ℝ n} :
    ⟪p, q⟫ = ∫ x in 0..1, p.val.eval x * q.val.eval x := rfl

@[simp]
lemma inner_eq {p q : degreeLT ℝ n} : ⟪p, q⟫ =
    ∑ i ∈ Finset.range n, ∑ j ∈ Finset.range n, p.val.coeff i * q.val.coeff j / (i + j + 1) := by
  simp [inner_eq_integral, eval_eq_sum_degreeLTEquiv p.property, eval_eq_sum_degreeLTEquiv q.property,
    degreeLTEquiv, Fin.sum_univ_eq_sum_range fun i => _ * _, Finset.sum_mul_sum]
  rw [intervalIntegral.integral_finset_sum fun i hi => ContinuousOn.intervalIntegrable (by fun_prop)]
  congr! with i hi
  rw [intervalIntegral.integral_finset_sum fun j hj => ContinuousOn.intervalIntegrable (by fun_prop)]
  congr! with j hj; simp [mul_assoc, ← mul_left_comm (q.val.coeff j), ← pow_add]; ring

theorem first : (gramSchmidt ℝ (degreeLT.basis ℝ 3) 0).val = 1 := by
  rw [gramSchmidt_def, ← Fintype.sum_ite_mem]; simp

theorem second : (gramSchmidt ℝ (degreeLT.basis ℝ 3) 1).val = X - C 2⁻¹ := by
  rw [gramSchmidt_def, ← Fintype.sum_ite_mem]
  norm_num [Submodule.starProjection_singleton, ← real_inner_self_eq_norm_sq, -inner_self_eq_norm_sq_to_K,
    first, Finset.sum_range_succ, coeff_one, coeff_X, smul_eq_C_mul]

theorem third : (gramSchmidt ℝ (degreeLT.basis ℝ 3) 2).val = X ^ 2 - X + C 6⁻¹ := by
  rw [gramSchmidt_def, ← Fintype.sum_ite_mem]
  norm_num [Submodule.starProjection_singleton, ← real_inner_self_eq_norm_sq, -inner_self_eq_norm_sq_to_K,
    Fin.sum_univ_succ, Fin.lt_def, first, second, Finset.sum_range_succ, coeff_one, coeff_X, smul_eq_C_mul]
  rw [show C (1 / 6 : ℝ) = C 2⁻¹ - C 3⁻¹ by norm_num [← C_sub]]; ring_nf

end Zad3_6

noncomputable def Zad3_7.V : Submodule ℝ (EuclideanSpace ℝ (Fin 3)) :=
  .span ℝ {!₂[1, 0, 1], !₂[0, 1, 2]}

@[simp]
lemma Zad3_7.mem_V : x ∈ V ↔ x.ofLp 0 + 2 * x.ofLp 1 - x.ofLp 2 = 0 := by
  simp [V, Submodule.mem_span_pair, PiLp.ext_iff, Fin.forall_fin_succ, sub_eq_zero, mul_comm]

noncomputable def Zad3_7.basis : OrthonormalBasis (Fin 2) ℝ V :=
  gramSchmidtOrthonormalBasis (by
    simp only [V]; convert finrank_span_set_eq_card ?_
    · simp
    · infer_instance
    · infer_instance
    apply linearIndepOn_id_pair (by simp); simp [PiLp.ext_iff, Fin.exists_fin_succ]
  ) ![⟨!₂[1, 0, 1], by simp⟩, ⟨!₂[-1, 1, 1], by simp; norm_num⟩]

theorem Zad3_7a : Zad3_7.basis i = ![!₂[(√2)⁻¹, 0, (√2)⁻¹], !₂[-(√3)⁻¹, (√3)⁻¹, (√3)⁻¹]] i := by
  rw [Zad3_7.basis, gramSchmidtOrthonormalBasis_apply_of_orthogonal]
  case hf => simp [Pairwise, inner, Fin.sum_univ_three]
  all_goals fin_cases i <;> simp [PiLp.norm_eq_of_L2, Fin.sum_univ_three, ← WithLp.toLp_smul] <;> norm_num

theorem Zad3_7b : Zad3_7.V.starProjection !₂[x, y, z] =
    !₂[5 / 6 * x - y / 3 + z / 6, -(x / 3) + y / 3 + z / 3, x / 6 + y / 3 + 5 / 6 * z] := by
  simp [Zad3_7.basis.starProjection_eq_sum_rankOne, Zad3_7a, inner, Fin.sum_univ_three,
    PiLp.ext_iff, Fin.forall_fin_succ, add_mul, mul_assoc, ← mul_inv]; ring_nf; trivial

theorem Zad3_8 : !![2024, 1; -1, 0] =
    ∑ i, ![-2024, 0, -1, 0] i • ![!![-1, 0; 0, 0], !![0, 2; 2, 1], !![0, -1; 1, 0], !![0, 1; -1, 4]] i := by
  simp [Fin.sum_univ_four, -zsmul_eq_mul]
