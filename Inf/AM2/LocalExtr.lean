import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Inf.ALG2.Sylvester
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.Deriv.Shift

/-! # Second partial derivative test -/

open Module Matrix Topology Filter

variable [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The Hessian matrix of second-order partial derivatives of `f` with respect to basis vectors in
`b`. -/
noncomputable def hessian (b : Basis ι ℝ E) (f : E → ℝ) (a : E) : Matrix ι ι ℝ :=
  of fun i j => fderiv ℝ (fun x => fderiv ℝ f x) a (b i) (b j)

/-- Symmetry of partial derivatives: the Hessian matrix of a `C^2` function is symmetric. -/
theorem isSymm_hessian {f : E → ℝ} (hf : ContDiffAt ℝ 2 f a) : (hessian b f a).IsSymm := by
  simp [IsSymm.ext_iff, hessian]; intro i j; apply ContDiffAt.isSymmSndFDerivAt hf; simp

section variable [Fintype ι] (b : Basis ι ℝ E) {f : E → ℝ} {a : E} (hf : ContDiffAt ℝ 2 f a)
include hf

theorem deriv_deriv_eq_hessian :
    deriv (deriv fun x => f (a + x • v)) (0 : ℝ) = b.repr v ⬝ᵥ hessian b f a *ᵥ b.repr v := calc
  deriv (deriv fun x => f (a + x • v)) (0 : ℝ)
  _ = deriv (fun x => fderiv ℝ f _ (deriv (a + · • v) x)) _ := by
    have : Tendsto (fun x : ℝ => a + x • v) (𝓝 0) (𝓝 a) := by
      apply Continuous.tendsto'; fun_prop; simp
    apply EventuallyEq.deriv_eq
    filter_upwards [this.eventually (hf.eventually (by simp))] with x hx
    apply fderiv_comp_deriv x (hx.differentiableAt two_ne_zero); fun_prop
  _ = deriv (fun x => fderiv ℝ f (a + x • v) v) (0 : ℝ) := by simp [deriv_smul_const]
  _ = deriv (fderiv ℝ f ∘ (a + · • v)) (0 : ℝ) v := by
    rw [deriv_clm_apply] <;> try simp <;> rfl
    change DifferentiableAt ℝ (fderiv ℝ f ∘ (a + · • v)) 0; apply DifferentiableAt.comp
    · simpa using hf.fderiv_right_succ.differentiableAt_one
    · fun_prop
  _ = fderiv ℝ (fderiv ℝ f) a v v := by
    rw [fderiv_comp_deriv]
    · simp [deriv_smul_const]
    · simpa using hf.fderiv_right_succ.differentiableAt_one
    · fun_prop
  _ = b.repr v ⬝ᵥ hessian b f a *ᵥ b.repr v := by
    rw [← ContinuousLinearMap.toLinearMap₁₂_apply, ← LinearMap.sum_repr_mul_repr_mul b b,
      Finsupp.sum_fintype _ _ (by simp)]
    simp [hessian, mulVec_eq_sum, dotProduct]; congr; ext x
    rw [Finsupp.sum_fintype _ _ (by simp)]; simp [Finset.mul_sum]

/-- If the Hessian matrix is positive-definite, it is positive-definite on a neighborhood. -/
theorem eventually_posDef_hessian (h : (hessian b f a).PosDef) :
    ∀ᶠ x in 𝓝 a, (hessian b f x).PosDef := by
  have ei := Fintype.equivFin ι
  revert b; suffices ∀ (b : Basis (Fin (Fintype.card ι)) ℝ E), (hessian b f a).PosDef
      → ∀ᶠ (x : E) in 𝓝 a, (hessian b f x).PosDef by
    intro b h; specialize this (b.reindex ei)
    have posDef_reindex_iff v : (hessian b f v).PosDef ↔ (hessian (b.reindex ei) f v).PosDef := by
      rw [posDef_iff_dotProduct_mulVec, posDef_iff_dotProduct_mulVec]; apply and_congr
      · simp [IsHermitian.ext_iff]; refine ei.forall_congr fun _ => ei.forall_congr fun _ => ?_
        simp [hessian]
      apply (ei.piCongrLeft fun _ => ℝ).forall_congr; intro x; congr!
      · simp [funext_iff]; apply ei.forall_congr; simp
      simp [mulVec_eq_sum, dotProduct]; apply Fintype.sum_bijective ei ei.bijective
      congr!; simp; apply Fintype.sum_bijective ei ei.bijective; congr! <;> simp [hessian]
    simp [← posDef_reindex_iff] at this; exact this h
  intro b h; simp [posDef_sylvester_iff] at ⊢ h; constructor
  · filter_upwards [hf.eventually (by simp)] with v using isSymm_hessian
  intro i; refine continuousAt_const.eventually_lt ?_ (h.2 i)
  apply continuous_id.matrixOf.matrix_det.continuousAt.comp; simp [continuousAt_pi]; intro j k
  repeat refine ContinuousAt.clm_apply ?_ continuousAt_const
  exact hf.fderiv_right_succ.continuousAt_fderiv one_ne_zero

/-- The **second partial derivative test**, minimum version: if the Hessian matrix is
positive-definite at a stationary point, then it is a local minimum. -/
theorem isLocalMin_of_hessian (ha : fderiv ℝ f a = 0) (h : (hessian b f a).PosDef) :
    IsLocalMin f a := by
  obtain ⟨s, hs, hcs, h⟩ : ∃ s ∈ 𝓝 a, Convex ℝ s ∧ ∀ x ∈ s,
      ContDiffAt ℝ 2 f x ∧ (hessian b f x).PosDef :=
    (locallyConvexSpace_iff_exists_convex_subset ℝ E).mp inferInstance a _
      ((hf.eventually (by simp)).and (eventually_posDef_hessian b hf h))
  filter_upwards [hs] with v hv
  have ⟨c, hc, ht⟩ := taylor_mean_remainder_lagrange_iteratedDeriv
      (f := f ∘ (a + · • (v - a))) (n := 1) zero_ne_one ?_; swap
  · norm_num; intro x hx; refine ((h _ ?_).1.comp x (by fun_prop)).contDiffWithinAt
    exact hcs.add_smul_sub_mem (mem_of_mem_nhds hs) hv hx
  simp [iteratedDeriv_succ] at ht; rw [add_eq_left.mpr] at ht; swap
  · rw [← fderivWithin_derivWithin, fderivWithin_eq_fderiv, fderiv_comp]
    · simp [ha]
    · simpa using hf.differentiableAt
    · fun_prop
    · exact uniqueDiffOn_Icc_zero_one 0 (by simp)
    · exact DifferentiableAt.comp 0 (by simpa using hf.differentiableAt) (by fun_prop)
  rw [← sub_nonneg, ht]; field_simp; simp
  nth_rw 1 [← add_zero c, ← deriv_comp_const_add]
  simp [← deriv_comp_const_add, add_smul, ← add_assoc]
  have hc : a + c • (v - a) ∈ s := hcs.add_smul_sub_mem (mem_of_mem_nhds hs) hv
      (by simpa using (Set.uIoo_subset_uIcc_self hc))
  rw [deriv_deriv_eq_hessian b (h _ hc).1]; exact (h _ hc).2.posSemidef.dotProduct_mulVec_nonneg _

/-- The **second partial derivative test**, maximum version: if the Hessian matrix is
negative-definite at a stationary point, then it is a local maximum. -/
theorem isLocalMax_of_hessian (ha : fderiv ℝ f a = 0) (h : (-hessian b f a).PosDef) :
    IsLocalMax f a := by
  rw [← neg_neg f]; apply IsLocalMin.neg
  apply isLocalMin_of_hessian b hf.neg (by simpa)
  convert h; simp [hessian, Pi.neg_def, ← ContinuousLinearMap.neg_apply]

end

/-- The **second partial derivative test** for functions on two variables : if the Hessian matrix
at a stationary point of a bivariate function has a positive determinant, then that point is a
local extremum. -/
theorem isLocalExtr_of_det_hessian_pos (hf : ContDiffAt ℝ 2 f a) (ha : fderiv ℝ f a = 0)
    (h : 0 < (hessian (Basis.finTwoProd ℝ) f a).det) : IsLocalExtr f a := by
  rcases lt_trichotomy (hessian (Basis.finTwoProd ℝ) f a 0 0) 0 with h0 | h0 | h0
  · apply Or.inr; apply isLocalMax_of_hessian (Basis.finTwoProd ℝ) hf ha
    simp_all [det_fin_two]; apply isSymm_hessian hf
  · simp_all [det_fin_two, (isSymm_hessian hf).apply, ← sq]; absurd h; simp [sq_nonneg]
  · apply Or.inl; apply isLocalMin_of_hessian (Basis.finTwoProd ℝ) hf ha
    simp_all [det_fin_two]; apply isSymm_hessian hf
