import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! # Various upstreamable convergence lemmas -/

open Topology

namespace Filter.Tendsto

/-! `Mathlib.Topology.Order.OrderClosed` -/

@[to_dual]
theorem max_self [TopologicalSpace α] [LinearOrder α] [OrderClosedTopology α] {l : Filter β}
    {f g : β → α} {a : α} (hf : Tendsto f l (𝓝 a)) (hg : Tendsto g l (𝓝 a)) :
    Tendsto (fun x => max (f x) (g x)) l (𝓝 a) := _root_.max_self a ▸ hf.max hg

/-! `Mathlib.Topology.Algebra.Monoid` -/

section variable [TopologicalSpace M] [MulOneClass M] [ContinuousMul M] {f g : α → M}

@[to_additive]
theorem mul_one (hf : Tendsto f l (𝓝 a)) (hg : Tendsto g l (𝓝 1)) :
    Tendsto (fun x => f x * g x) l (𝓝 a) := _root_.mul_one a ▸ hf.mul hg

@[to_additive]
theorem one_mul (hf : Tendsto f l (𝓝 1)) (hg : Tendsto g l (𝓝 a)) :
    Tendsto (fun x => f x * g x) l (𝓝 a) := _root_.one_mul a ▸ hf.mul hg

end

section variable [TopologicalSpace M] [MulOneClass M] [SeparatelyContinuousMul M] (C : M)

@[to_additive]
theorem const_mul_one (hf : Tendsto f l (𝓝 1)) : Tendsto (fun x => C * f x) l (𝓝 C) := by
  simpa using hf.const_mul C

@[to_additive]
theorem one_mul_const (hf : Tendsto f l (𝓝 1)) : Tendsto (fun x => f x * C) l (𝓝 C) := by
  simpa using hf.mul_const C

end

/-! `Mathlib.Topology.Algebra.Group.Basic` -/

theorem neg_zero [TopologicalSpace G] [NegZeroClass G] [ContinuousNeg G] {f : α → G}
    (hf : Tendsto f l (𝓝 0)) : Tendsto (fun x => -f x) l (𝓝 0) := _root_.neg_zero (G := G) ▸ hf.neg

section variable [TopologicalSpace G] [SubNegZeroMonoid G] [ContinuousSub G] (C : G)

theorem sub_zero {f g : α → G} (hf : Tendsto f l (𝓝 a)) (hg : Tendsto g l (𝓝 0)) :
    Tendsto (fun x => f x - g x) l (𝓝 (a)) := _root_.sub_zero a ▸ hf.sub hg

theorem const_sub_zero (hf : Tendsto f l (𝓝 0)) : Tendsto (fun x => C - f x) l (𝓝 C) := by
  simpa using tendsto_const_nhds.sub hf

end

variable [TopologicalSpace G] [SubNegMonoid G] [ContinuousSub G] (C : G) in
theorem zero_sub {f g : α → G} (hf : Tendsto f l (𝓝 0)) (hg : Tendsto g l (𝓝 a)) :
    Tendsto (fun x => f x - g x) l (𝓝 (-a)) := _root_.zero_sub a ▸ hf.sub hg

variable [TopologicalSpace G] [SubNegMonoid G] [SeparatelyContinuousAdd G] (C : G) in
theorem zero_sub_const (hf : Tendsto f l (𝓝 0)) : Tendsto (fun x => f x - C) l (𝓝 (-C)) :=
  (hf.zero_add_const (-C)).congr fun x => (sub_eq_add_neg (f x) C).symm

/-! `Mathlib.Topology.Algebra.GroupWithZero` -/

theorem inv_one [Zero G₀] [InvOneClass G₀] [TopologicalSpace G₀] [ContinuousInv₀ G₀] [NeZero (1 : G₀)]
    {f : α → G₀} (hf : Tendsto f l (𝓝 1)) : Tendsto (fun x => (f x)⁻¹) l (𝓝 1) :=
  _root_.inv_one (G := G₀) ▸ hf.inv₀ one_ne_zero

theorem mul_zero [MulZeroClass G₀] [TopologicalSpace G₀] [ContinuousMul G₀] {f g : α → G₀}
    (hf : Tendsto f l (𝓝 a)) (hg : Tendsto g l (𝓝 0)) : Tendsto (fun x => f x * g x) l (𝓝 0) := by
  simpa using hf.mul hg

theorem zero_mul [MulZeroClass G₀] [TopologicalSpace G₀] [ContinuousMul G₀] {f g : α → G₀}
    (hf : Tendsto f l (𝓝 0)) (hg : Tendsto g l (𝓝 a)) : Tendsto (fun x => f x * g x) l (𝓝 0) := by
  simpa using hf.mul hg

theorem const_mul_zero [MulZeroClass G₀] [TopologicalSpace G₀] [SeparatelyContinuousMul G₀]
    (C : G₀) {l : Filter α} {f : α → G₀} (hf : Tendsto f l (𝓝 0)) : Tendsto (fun x => C * f x) l (𝓝 0) := by
  simpa using hf.const_mul C

theorem zero_mul_const [MulZeroClass G₀] [TopologicalSpace G₀] [SeparatelyContinuousMul G₀]
    (C : G₀) {l : Filter α} {f : α → G₀} (hf : Tendsto f l (𝓝 0)) : Tendsto (fun x => f x * C) l (𝓝 0) := by
  simpa using hf.mul_const C

theorem zero_pow [TopologicalSpace M] [MonoidWithZero M] [ContinuousMul M] (n : ℕ) [NeZero n]
    {l : Filter α} {f : α → M} (hf : Tendsto f l (𝓝 0)) : Tendsto (fun x => f x ^ n) l (𝓝 0) :=
  _root_.zero_pow (M₀ := M) (NeZero.ne n) ▸ hf.pow n

theorem zero_div_const [GroupWithZero G₀] [TopologicalSpace G₀] [SeparatelyContinuousMul G₀]
    (C : G₀) {l : Filter α} {f : α → G₀} (hf : Tendsto f l (𝓝 0)) : Tendsto (fun x => f x / C) l (𝓝 0) :=
  (hf.zero_mul_const C⁻¹).congr fun x => (div_eq_mul_inv (f x) C).symm

theorem const_div [Zero G₀] [DivInvMonoid G₀] [TopologicalSpace G₀] [ContinuousInv₀ G₀] [SeparatelyContinuousMul G₀]
    (C : G₀) {l : Filter α} {f : α → G₀} {a : G₀} (hf : Tendsto f l (𝓝 a)) (h : a ≠ 0) :
    Tendsto (fun x => C / f x) l (𝓝 (C / a)) := by simpa [div_eq_mul_inv] using (hf.inv₀ h).const_mul C

/-! `Mathlib.Topology.Algebra.Order.Group` -/

theorem abs_zero [TopologicalSpace G] [AddCommGroup G] [LinearOrder G] [IsOrderedAddMonoid G]
    [OrderTopology G] {l : Filter α} {f : α → G} (hf : Tendsto f l (𝓝 0)) :
    Tendsto (fun x => |f x|) l (𝓝 0) := _root_.abs_zero (α := G) ▸ hf.abs

/-! `Mathlib.Order.Filter.AtTopBot.Basic` -/

theorem atTop_add_nat (C : ℕ) (hf : Tendsto f l atTop) : Tendsto (fun n => f n + C) l atTop :=
    (tendsto_add_atTop_nat C).comp hf

/-! `Mathlib.Order.Filter.AtTopBot.Group` -/

section variable [AddCommGroup G] [PartialOrder G] [IsOrderedAddMonoid G] (C : G)

alias _root_.tendsto_neg_atTop := tendsto_neg_atTop_atBot

alias _root_.tendsto_neg_atBot := tendsto_neg_atBot_atTop

alias ⟨_, neg_atTop⟩ := tendsto_neg_atBot_iff

alias ⟨_, neg_atBot⟩ := tendsto_neg_atTop_iff

theorem const_add_atTop (hf : Tendsto f l atTop) : Tendsto (fun x => C + f x) l atTop :=
  tendsto_atTop_add_const_left l C hf

theorem const_add_atBot (hf : Tendsto f l atBot) : Tendsto (fun x => C + f x) l atBot :=
  tendsto_atBot_add_const_left l C hf

theorem atTop_add_const (hf : Tendsto f l atTop) : Tendsto (fun x => f x + C) l atTop :=
  tendsto_atTop_add_const_right l C hf

theorem atBot_add_const (hf : Tendsto f l atBot) : Tendsto (fun x => f x + C) l atBot :=
  tendsto_atBot_add_const_right l C hf

theorem const_sub_atTop (hf : Tendsto f l atTop) : Tendsto (fun x => C - f x) l atBot :=
  (hf.neg_atTop.const_add_atBot C).congr fun x => (sub_eq_add_neg C (f x)).symm

theorem const_sub_atBot (hf : Tendsto f l atBot) : Tendsto (fun x => C - f x) l atTop :=
  (hf.neg_atBot.const_add_atTop C).congr fun x => (sub_eq_add_neg C (f x)).symm

theorem atTop_sub_const (hf : Tendsto f l atTop) : Tendsto (fun x => f x - C) l atTop :=
  (hf.atTop_add_const (-C)).congr fun x => (sub_eq_add_neg (f x) C).symm

theorem atBot_sub_const (hf : Tendsto f l atBot) : Tendsto (fun x => f x - C) l atBot :=
  (hf.atBot_add_const (-C)).congr fun x => (sub_eq_add_neg (f x) C).symm

theorem _root_.tendsto_add_atTop : Tendsto (fun x => x + C) atTop atTop :=
  tendsto_id.atTop_add_const C

theorem _root_.tendsto_sub_atTop : Tendsto (fun x => x - C) atTop atTop :=
  tendsto_id.atTop_sub_const C

end

/-! `Mathlib.Order.Filter.AtTopBot.Archimedean` -/

alias _root_.tendsto_natCast_atTop := tendsto_natCast_atTop_atTop

variable [Semiring R] [PartialOrder R] [IsOrderedRing R] [Archimedean R] in
theorem natCast_atTop (h : Tendsto f atTop l) : Tendsto (fun (n : ℕ) => f (n : R)) atTop l :=
  h.comp tendsto_natCast_atTop

section variable [Ring R] [PartialOrder R] [IsOrderedRing R] [Archimedean R]

theorem _root_.tendsto_natCast_add_atTop (C : R) : Tendsto (fun (n : ℕ) => n + C) atTop atTop :=
  tendsto_natCast_atTop.atTop_add_const C

theorem _root_.tendsto_natCast_sub_atTop (C : R) : Tendsto (fun (n : ℕ) => n - C) atTop atTop :=
  tendsto_natCast_atTop.atTop_sub_const C

end

section variable [Semiring R] [LinearOrder R] [IsStrictOrderedRing R] [Archimedean R]

theorem _root_.tendsto_const_mul_atTop' {C : R} (h : 0 < C) : Tendsto (fun x => C * x) atTop atTop :=
  tendsto_id.const_mul_atTop' h

end

/-! `Mathlib.Order.Filter.AtTopBot.Ring` -/

theorem atTop_pow₀ [Semiring R] [PartialOrder R] [IsOrderedRing R] (n : ℕ) [NeZero n]
    {l : Filter α} {f : α → R} (hf : Tendsto f l atTop) : Tendsto (fun x => f x ^ n) l atTop :=
  (tendsto_pow_atTop (NeZero.ne n)).comp hf

/-! `Mathlib.Order.Filter.AtTopBot.Field` -/

variable [Semifield K] [LinearOrder K] [IsStrictOrderedRing K] in
theorem _root_.tendsto_const_mul_atTop {C : K} (h : 0 < C) : Tendsto (fun x => C * x) atTop atTop :=
  tendsto_id.const_mul_atTop h

variable [Field K] [LinearOrder K] [IsStrictOrderedRing K] in
theorem _root_.tendsto_const_mul_atTop_of_neg {C : K} (h : C < 0) :
    Tendsto (fun x => C * x) atTop atBot := tendsto_id.const_mul_atTop_of_neg h

/-! `Mathlib.Topology.Algebra.Order.Field` -/

variable [Semifield K] [LinearOrder K] [IsStrictOrderedRing K] [TopologicalSpace K] [OrderTopology K] in
theorem inv_atTop {f : α → K} (h : Tendsto f l atTop) : Tendsto (fun x => (f x)⁻¹) l (𝓝 0) :=
  h.inv_tendsto_atTop

variable [Field K] [LinearOrder K] [IsStrictOrderedRing K] [TopologicalSpace K] [OrderTopology K] in
theorem _root_.tendsto_const_div_atTop (C : K) : Tendsto (fun x => C / x) atTop (𝓝 0) :=
  tendsto_id.const_div_atTop C

/-! `Mathlib.Data.Real.Sqrt` -/

theorem sqrt_atTop (h : Tendsto f l atTop) : Tendsto (fun x => √(f x)) l atTop :=
  Real.tendsto_sqrt_atTop.comp h

/-! `Mathlib.Analysis.SpecialFunctions.Exp` -/

theorem rexp_atTop (h : Tendsto f l atTop) : Tendsto (fun x => Real.exp (f x)) l atTop :=
  Real.tendsto_exp_atTop.comp h

theorem rexp_atBot (h : Tendsto f l atBot) : Tendsto (fun x => Real.exp (f x)) l (𝓝 0) :=
  Real.tendsto_exp_atBot.comp h

/-! `Mathlib.Analysis.SpecialFunction.Log.Basic` -/

theorem log_one (h : Tendsto f l (𝓝 1)) : Tendsto (fun x => Real.log (f x)) l (𝓝 0) :=
  Real.log_one ▸ h.log one_ne_zero

theorem log_atTop (h : Tendsto f l atTop) : Tendsto (fun x => Real.log (f x)) l atTop :=
  Real.tendsto_log_atTop.comp h

/-! `Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics` -/

theorem const_rpow_atTop {f : α → ℝ} {b : ℝ} (hb : 1 < b) (h : Tendsto f l atTop) :
    Tendsto (fun x => b ^ f x) l atTop := by
  simpa [Real.rpow_def_of_pos (one_pos.trans hb)] using h.const_mul_atTop (Real.log_pos hb)

theorem const_rpow_atTop_of_lt_one {f : α → ℝ} {b : ℝ} (hb₀ : -1 < b) (hb₁ : b < 1) (h : Tendsto f l atTop) :
    Tendsto (fun x => b ^ f x) l (𝓝 0) :=
  (tendsto_rpow_atTop_of_base_lt_one b hb₀ hb₁).comp h

/-! `Mathlib.Analysis.SpecialFunctions.Pow.Continuity` -/

theorem zero_rpow {f g : α → ℝ} {a : ℝ} (hf : Tendsto f l (𝓝 0)) (hg : Tendsto g l (𝓝 a)) (h : 0 < a) :
    Tendsto (fun x => f x ^ g x) l (𝓝 0) := by simpa [h, h.ne'] using hf.rpow hg

theorem zero_rpow_const {f : α → ℝ} (p : ℝ) (hf : Tendsto f l (𝓝 0)) (h : 0 < p) :
    Tendsto (fun x => f x ^ p) l (𝓝 0) := by simpa [h.ne'] using hf.rpow_const (Or.inr h.le)

theorem one_rpow {f g : α → ℝ} {a : ℝ} (hf : Tendsto f l (𝓝 1)) (hg : Tendsto g l (𝓝 a)) :
    Tendsto (fun x => f x ^ g x) l (𝓝 1) := by simpa using hf.rpow hg

theorem one_rpow_const {f : α → ℝ} (p : ℝ) (hf : Tendsto f l (𝓝 1)) :
    Tendsto (fun x => f x ^ p) l (𝓝 1) := by simpa using hf.rpow_const

theorem rpow_zero {f g : α → ℝ} {a : ℝ} (hf : Tendsto f l (𝓝 a)) (hg : Tendsto g l (𝓝 0)) (h : a ≠ 0) :
    Tendsto (fun x => f x ^ g x) l (𝓝 1) := by simpa [h] using hf.rpow hg

theorem const_rpow_zero {f : α → ℝ} {a : ℝ} (hf : Tendsto f l (𝓝 0)) (h : a ≠ 0) :
    Tendsto (fun x => a ^ f x) l (𝓝 1) := tendsto_const_nhds.rpow_zero hf h

theorem _root_.tendsto_const_rpow_inv (a : ℝ) (ha : a ≠ 0) : Tendsto (fun x : ℝ => a ^ x⁻¹) atTop (𝓝 1) := by
  simpa using tendsto_const_nhds.rpow tendsto_inv_atTop_zero (.inl ha)
