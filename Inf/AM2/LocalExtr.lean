import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Inf.ALG2.Sylvester
import Mathlib.Analysis.Calculus.Taylor
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.Calculus.DerivativeTest

/-! # Second partial derivative test -/

open Module Matrix Topology Filter

section
variable [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {f : E → F} {a v : E}

theorem fderiv_apply_eq_deriv (hf : DifferentiableAt ℝ f a) :
    fderiv ℝ f a v = deriv (fun x => f (a + x • v)) (0 : ℝ) := by
  symm; convert fderiv_comp_deriv (l := f) (f := (a + · • v)) (0 : ℝ) (by simpa) (by simp)
    <;> simp [deriv_smul_const]

theorem fderiv_fderiv_apply_same (hf : ∀ᶠ x in nhds a, DifferentiableAt ℝ f x)
    (hf' : DifferentiableAt ℝ (fderiv ℝ f) a) :
    fderiv ℝ (fderiv ℝ f) a v v = deriv (deriv fun x => f (a + x • v)) (0 : ℝ) := by
  rw [fderiv_apply_eq_deriv hf']; symm
  convert deriv_clm_apply (c := fun x => fderiv ℝ f (a + x • v)) ?_ (differentiableAt_const v) using 1
  swap; simp; rfl; swap
  · change DifferentiableAt ℝ (fderiv ℝ f ∘ (a + · • v)) 0; apply DifferentiableAt.comp
    · simpa
    · fun_prop
  have : Tendsto (fun x : ℝ => a + x • v) (𝓝 0) (𝓝 a) := by apply Continuous.tendsto'; fun_prop; simp
  apply EventuallyEq.deriv_eq; filter_upwards [this.eventually hf] with x hx
  convert! fderiv_comp_deriv (l := f) (f := (a + · • v)) x hx (by fun_prop)
  simp; rw [deriv_smul_const] <;> simp

theorem ContDiffAt.fderiv_fderiv_apply_same (hf : ContDiffAt ℝ 2 f a) :
    fderiv ℝ (fderiv ℝ f) a v v = deriv (deriv fun x => f (a + x • v)) (0 : ℝ) :=
  _root_.fderiv_fderiv_apply_same
    ((hf.eventually (by simp)).mono fun x hx => hx.differentiableAt two_ne_zero)
    hf.fderiv_right_succ.differentiableAt_one

/-- The Hessian matrix of second-order partial derivatives of `f` with respect to basis vectors in
`b`. -/
noncomputable def hessian (b : Basis ι ℝ E) (f : E → F) (a : E) : Matrix ι ι F :=
  of fun i j => fderiv ℝ (fun x => fderiv ℝ f x) a (b i) (b j)

/-- Symmetry of partial derivatives: the Hessian matrix of a function differentiable on a
neighborhood and twice differentiable in a point is symmetric. -/
theorem isSymm_hessian (hf : ∀ᶠ x in nhds a, DifferentiableAt ℝ f x)
    (hf' : DifferentiableAt ℝ (fderiv ℝ f) a) : (hessian b f a).IsSymm :=
  IsSymm.ext fun i j => second_derivative_symmetric_of_eventually
    (hf.mono fun _ => DifferentiableAt.hasFDerivAt) hf'.hasFDerivAt (b j) (b i)

theorem ContDiffAt.isSymm_hessian (hf : ContDiffAt ℝ 2 f a) : (hessian b f a).IsSymm := by
  simp [IsSymm.ext_iff, hessian]; intro i j; apply ContDiffAt.isSymmSndFDerivAt hf; simp

variable [Fintype ι] (b : Basis ι ℝ E) {f : E → ℝ}

theorem deriv_deriv_eq_hessian (hf : ∀ᶠ x in nhds a, DifferentiableAt ℝ f x)
    (hf' : DifferentiableAt ℝ (fderiv ℝ f) a) :
    deriv (deriv fun x => f (a + x • v)) (0 : ℝ) = b.repr v ⬝ᵥ hessian b f a *ᵥ b.repr v := calc
  deriv (deriv fun x => f (a + x • v)) (0 : ℝ)
  _ = fderiv ℝ (fderiv ℝ f) a v v := by rw [fderiv_fderiv_apply_same hf hf']
  _ = b.repr v ⬝ᵥ hessian b f a *ᵥ b.repr v := by
    rw [← ContinuousLinearMap.toLinearMap₁₂_apply, ← LinearMap.sum_repr_mul_repr_mul b b,
      Finsupp.sum_fintype _ _ (by simp)]
    simp [hessian, mulVec_eq_sum, dotProduct]; congr; ext x
    rw [Finsupp.sum_fintype _ _ (by simp)]; simp [Finset.mul_sum]

/-- If the Hessian matrix is positive-definite, it is positive-definite on a neighborhood. -/
theorem eventually_posDef_hessian (hf : ContDiffAt ℝ 2 f a) (h : (hessian b f a).PosDef) :
    ∀ᶠ x in 𝓝 a, (hessian b f x).PosDef := by
  have ei := Fintype.equivFin ι
  revert b; suffices ∀ (b : Basis (Fin (Fintype.card ι)) ℝ E), (hessian b f a).PosDef
      → ∀ᶠ (x : E) in 𝓝 a, (hessian b f x).PosDef by
    intro b h; specialize this (b.reindex ei)
    have posDef_reindex_iff v : (hessian b f v).PosDef ↔ (hessian (b.reindex ei) f v).PosDef := by
      rw [posDef_iff_dotProduct_mulVec, posDef_iff_dotProduct_mulVec]; apply and_congr
      · simp [IsSymm.ext_iff]; refine ei.forall_congr fun _ => ei.forall_congr fun _ => ?_
        simp [hessian]
      apply (ei.piCongrLeft fun _ => ℝ).forall_congr; intro x; congr!
      · simp [funext_iff]; apply ei.forall_congr; simp
      simp [mulVec_eq_sum, dotProduct]; apply Fintype.sum_bijective ei ei.bijective
      congr!; simp; apply Fintype.sum_bijective ei ei.bijective; congr! <;> simp [hessian]
    simp [← posDef_reindex_iff] at this; exact this h
  intro b h; simp [posDef_sylvester_iff] at ⊢ h; constructor
  · filter_upwards [hf.eventually (by simp)] with v using ContDiffAt.isSymm_hessian
  intro i; refine continuousAt_const.eventually_lt ?_ (h.2 i)
  apply continuous_id.matrixOf.matrix_det.continuousAt.comp; simp [continuousAt_pi]; intro j k
  repeat refine ContinuousAt.clm_apply ?_ continuousAt_const
  exact hf.fderiv_right_succ.continuousAt_fderiv one_ne_zero

/-- The **second partial derivative test**, minimum version: if the Hessian matrix is
positive-definite at a stationary point, then it is a local minimum. -/
theorem isLocalMin_of_hessian (hf : ContDiffAt ℝ 2 f a) (ha : fderiv ℝ f a = 0) (h : (hessian b f a).PosDef) :
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
  rw [deriv_deriv_eq_hessian b (((h _ hc).1.eventually (by simp)).mono
    fun x hx => hx.differentiableAt two_ne_zero) ((h _ hc).1.fderiv_right_succ.differentiableAt_one)]
  exact (h _ hc).2.posSemidef.dotProduct_mulVec_nonneg _

/-- The **second partial derivative test**, maximum version: if the Hessian matrix is
negative-definite at a stationary point, then it is a local maximum. -/
theorem isLocalMax_of_hessian (hf : ContDiffAt ℝ 2 f a) (ha : fderiv ℝ f a = 0) (h : (-hessian b f a).PosDef) :
    IsLocalMax f a := by
  rw [← neg_neg f]; apply IsLocalMin.neg
  apply isLocalMin_of_hessian b hf.neg (by simpa)
  convert h; simp [hessian]; rfl

theorem IsLocalMin.posSemidef_hessian' (hf : ∀ᶠ x in nhds a, DifferentiableAt ℝ f x)
    (hf' : DifferentiableAt ℝ (fderiv ℝ f) a) (h : IsLocalMin f a) : (hessian b f a).PosSemidef := by
  rw [Matrix.posSemidef_iff_dotProduct_mulVec]; use isSymm_hessian hf hf'; simp; intro x
  let v := b.equivFun.symm x; have : b.equivFun v = x := b.equivFun.apply_symm_apply x
  simp [← this, ← deriv_deriv_eq_hessian b hf hf']
  have := (IsLocalMin.comp_continuous (by simpa using h)
    (show ContinuousAt (fun x : ℝ => a + x • v) 0 by fun_prop)).deriv_eq_zero
  dsimp [Function.comp_def] at this; contrapose! h; simp [IsLocalMin, IsMinFilter]
  have h' := eventually_nhdsWithin_sign_eq_of_deriv_neg h this
  have h' : ∀ᶠ x : ℝ in 𝓝[>] 0, deriv (fun x => f (a + x • v)) x < 0 := by
    filter_upwards [eventually_mem_nhdsWithin, h'.filter_mono nhdsWithin_le_nhds] with x hx h'
    simp_all [sign_eq_neg_one_iff]
  apply (Continuous.tendsto' (by fun_prop) 0 a (by simp) :
    Tendsto (fun x : ℝ => a + x • v) (𝓝 0) (𝓝 a)).frequently
  refine Frequently.filter_mono ?_ (nhdsWithin_le_nhds (s := (Set.Ioi 0))); apply Eventually.frequently
  rw [(nhdsGT_basis 0).eventually_iff] at h'; rcases h' with ⟨i, hi, h'⟩
  filter_upwards [eventually_mem_nhdsWithin, (eventually_lt_nhds hi).filter_mono nhdsWithin_le_nhds]
  suffices StrictAntiOn (fun x => f (a + x • v)) (Set.Ico 0 i) by
    intro x hx0 hxi; simpa using this ⟨le_rfl, hi⟩ ⟨hx0.le, hxi⟩ hx0
  apply strictAntiOn_of_deriv_neg (convex_Ico 0 i) ?_ (by simpa using h')
  intro x ⟨hx0, hxi⟩; apply ContinuousAt.continuousWithinAt; rcases eq_or_lt_of_le' hx0 with rfl | h
  · exact hf.self_of_nhds.continuousAt.comp_of_eq
      (show ContinuousAt (fun x : ℝ => a + x • v) 0 by fun_prop) (by simp)
  exact (differentiableAt_of_deriv_ne_zero (h' ⟨h, hxi⟩).ne).continuousAt

theorem IsLocalMin.posSemidef_hessian (hf : ContDiffAt ℝ 2 f a) (h : IsLocalMin f a) :
    (hessian b f a).PosSemidef :=
  h.posSemidef_hessian' b ((hf.eventually (by simp)).mono fun x hx => hx.differentiableAt two_ne_zero)
    hf.fderiv_right_succ.differentiableAt_one

theorem IsLocalMax.negSemidef_hessian' (hf : ∀ᶠ x in nhds a, DifferentiableAt ℝ f x)
    (hf' : DifferentiableAt ℝ (fderiv ℝ f) a) (h : IsLocalMax f a) : (-hessian b f a).PosSemidef := by
  convert h.neg.posSemidef_hessian' b (hf.mono fun x => DifferentiableAt.neg)
    (by eta_expand; simpa [fderiv_neg]); simp [hessian, fderiv_neg]; rfl

theorem IsLocalMax.negSemidef_hessian (hf : ContDiffAt ℝ 2 f a) (h : IsLocalMax f a) :
    (-hessian b f a).PosSemidef := by convert h.neg.posSemidef_hessian b hf.neg; simp [hessian]; rfl

end

/-- The **second partial derivative test** for functions on two variables : if the Hessian matrix
at a stationary point of a bivariate function has a positive determinant, then that point is a
local extremum. -/
theorem isLocalExtr_of_det_hessian_pos (hf : ContDiffAt ℝ 2 f a) (ha : fderiv ℝ f a = 0)
    (h : (0 : ℝ) < (hessian (Basis.finTwoProd ℝ) f a).det) : IsLocalExtr f a := by
  rcases lt_trichotomy (hessian (Basis.finTwoProd ℝ) f a 0 0) 0 with h0 | h0 | h0
  · apply Or.inr; apply isLocalMax_of_hessian (Basis.finTwoProd ℝ) hf ha
    simp_all [det_fin_two]; apply hf.isSymm_hessian
  · simp_all [det_fin_two, (hf.isSymm_hessian).apply, ← sq]; absurd h; simp [sq_nonneg]
  · apply Or.inl; apply isLocalMin_of_hessian (Basis.finTwoProd ℝ) hf ha
    simp_all [det_fin_two]; apply hf.isSymm_hessian

theorem det_hessian_nonneg_of_isLocalExtr (hf : ContDiffAt ℝ 2 f a) (h : IsLocalExtr f a) :
    (0 : ℝ) ≤ (hessian (Basis.finTwoProd ℝ) f a).det :=
  h.elim (fun hmin => (hmin.posSemidef_hessian _ hf).det_nonneg)
    fun hmax => by simpa [det_neg] using (hmax.negSemidef_hessian (Basis.finTwoProd ℝ) hf).det_nonneg
