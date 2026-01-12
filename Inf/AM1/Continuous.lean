import Inf.AM1.LimitAt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! # End of lecture 5, lectures 6 & 7

Mathlib already has predicates `Continuous`, `ContinuousOn`, `ContinuousAt`
and `ContinuousWithinAt`, meaning this file here is mostly glue and restatements
of theorems involving limits. -/

/-- (Heine's) definition of function continuity.

Cauchy's epsilon-delta definition is `Metric.continuousWithinAt_iff` -/
lemma continuousWithinAt_iff_hasLim {f : ℝ → ℝ} {D : Set ℝ} {a : ℝ} :
    ContinuousWithinAt f D a ↔ ∀ x, (∀ n, x n ∈ D) → HasLim x a → HasLim (f ∘ x) (f a) := by
  rw [ContinuousWithinAt, Filter.tendsto_iff_seq_tendsto]
  simp [hasLim_iff_tendsto, tendsto_nhdsWithin_iff]
  use fun h x hd ht => h x ht 0 (fun n _ => hd n)
  intro h x ht n0 hx
  refine (h (fun n => x (max n n0)) (fun n => hx _ (by simp)) (ht.congr' ?_)).congr' ?_ <;>
  · simp [Filter.EventuallyEq]
    exact ⟨n0, fun n hn => by congr; simpa⟩

/-- (Heine's) definition of function continuity.

Cauchy's epsilon-delta definition is `Metric.continuousAt_iff` -/
lemma continuousAt_iff_hasLim {f : ℝ → ℝ} {a : ℝ} :
    ContinuousAt f a ↔ ∀ x, HasLim x a → HasLim (f ∘ x) (f a) := by
  simp [← continuousWithinAt_univ, continuousWithinAt_iff_hasLim]

/-- (Heine's) definition of function continuity.

Cauchy's epsilon-delta definition is `Metric.continuousOn_iff` -/
lemma continuousOn_iff_hasLim {f : ℝ → ℝ} {D : Set ℝ} :
    ContinuousOn f D ↔ ∀ a ∈ D, ∀ x, (∀ n, x n ∈ D) → HasLim x a → HasLim (f ∘ x) (f a) :=
  forall₂_congr fun _ _ => continuousWithinAt_iff_hasLim

/-- (Heine's) definition of function continuity.

Cauchy's epsilon-delta definition is `Metric.continuous_iff` -/
lemma continuous_iff_hasLim {f : ℝ → ℝ} :
    Continuous f ↔ ∀ a x, HasLim x a → HasLim (f ∘ x) (f a) :=
  continuous_iff_continuousAt.trans (forall_congr' fun _ => continuousAt_iff_hasLim)

lemma ContinuousOn.hasLim {f : ℝ → ℝ} {D : Set ℝ} (h : ContinuousOn f D) {a : ℝ} (ha : a ∈ D) {x : ℕ → ℝ} :
    (∀ n, x n ∈ D) → HasLim x a → HasLim (f ∘ x) (f a) :=
  continuousOn_iff_hasLim.mp h a ha x

lemma Continuous.hasLim {f : ℝ → ℝ} (h : Continuous f) (a : ℝ) {x : ℕ → ℝ} :
    HasLim x a → HasLim (f ∘ x) (f a) :=
  continuous_iff_hasLim.mp h a x

/-- **Th. 5.6.** Within a continuous function's domain, limits are equal to its values. -/
lemma continuousWithinAt_iff_hasLimAt {f : ℝ → ℝ} {D : Set ℝ} {a : ℝ} :
    ContinuousWithinAt f D a ↔ HasLimAt f D a (f a) := by
  simp [Metric.continuousWithinAt_iff, HasLimAt.def]
  peel with e he d he x hx
  use fun h _ => h
  intro h hxd
  by_cases x = a
  case pos heq => subst heq; simpa
  case neg hne => exact h hne hxd

/-- **Th. 5.6.** Within a continuous function's domain, limits are equal to its values. -/
lemma continuousAt_iff_hasLimAt {f : ℝ → ℝ} {a : ℝ} :
    ContinuousAt f a ↔ HasLimAt f Set.univ a (f a) :=
  (continuousWithinAt_univ f a).symm.trans continuousWithinAt_iff_hasLimAt

/-- **Th. 5.6.** Within a continuous function's domain, limits are equal to its values. -/
lemma continuousOn_iff_hasLimAt {f : ℝ → ℝ} {D : Set ℝ} : ContinuousOn f D ↔ ∀ a ∈ D, HasLimAt f D a (f a) :=
  forall₂_congr fun _ _ => continuousWithinAt_iff_hasLimAt

/-- **Th. 5.6.** Within a continuous function's domain, limits are equal to its values. -/
lemma continuous_iff_hasLimAt {f : ℝ → ℝ} : Continuous f ↔ ∀ a : ℝ, HasLimAt f Set.univ a (f a) :=
  continuous_iff_continuousAt.trans (forall_congr' fun _ => continuousAt_iff_hasLimAt)

lemma ContinuousOn.hasLimAt {f : ℝ → ℝ} {D : Set ℝ} (h : ContinuousOn f D) {a : ℝ} (ha : a ∈ D) :
    HasLimAt f D a (f a) := continuousOn_iff_hasLimAt.mp h a ha

lemma Continuous.hasLimAt {f : ℝ → ℝ} (h : Continuous f) (a : ℝ) : HasLimAt f Set.univ a (f a) :=
  continuous_iff_hasLimAt.mp h a

section

variable {X M : Type*} [TopologicalSpace X] [TopologicalSpace M] [Add M] [ContinuousAdd M]
    {f : X → M} {D : Set X} {a : X} (y : M)

lemma ContinuousWithinAt.add_const (h : ContinuousWithinAt f D a) : ContinuousWithinAt (fun x => f x + y) D a :=
  h.add continuousWithinAt_const
lemma ContinuousAt.add_const (h : ContinuousAt f a) : ContinuousAt (fun x => f x + y) a :=
  h.add continuousAt_const
lemma ContinuousOn.add_const (h : ContinuousOn f D) : ContinuousOn (fun x => f x + y) D :=
  h.add continuousOn_const
lemma Continuous.add_const (h : Continuous f) : Continuous fun x => f x + y := h.add continuous_const

lemma ContinuousWithinAt.const_add (h : ContinuousWithinAt f D a) : ContinuousWithinAt (fun x => y + f x) D a :=
  continuousWithinAt_const.add h
lemma ContinuousAt.const_add (h : ContinuousAt f a) : ContinuousAt (fun x => y + f x) a :=
  continuousAt_const.add h
lemma ContinuousOn.const_add (h : ContinuousOn f D) : ContinuousOn (fun x => y + f x) D :=
  continuousOn_const.add h
lemma Continuous.const_add (h : Continuous f) : Continuous fun x => y + f x := continuous_const.add h

end

section

variable {X G : Type*} [TopologicalSpace X] [TopologicalSpace G] [Sub G] [ContinuousSub G]
    {f : X → G} {D : Set X} {a : X} (y : G)

lemma ContinuousWithinAt.sub_const (h : ContinuousWithinAt f D a) : ContinuousWithinAt (fun x => f x - y) D a :=
  h.sub continuousWithinAt_const
lemma ContinuousAt.sub_const (h : ContinuousAt f a) : ContinuousAt (fun x => f x - y) a :=
  h.sub continuousAt_const
lemma ContinuousOn.sub_const (h : ContinuousOn f D) : ContinuousOn (fun x => f x - y) D :=
  h.sub continuousOn_const
lemma Continuous.sub_const (h : Continuous f) : Continuous fun x => f x - y := h.sub continuous_const

lemma ContinuousWithinAt.const_sub (h : ContinuousWithinAt f D a) : ContinuousWithinAt (fun x => y - f x) D a :=
  continuousWithinAt_const.sub h
lemma ContinuousAt.const_sub (h : ContinuousAt f a) : ContinuousAt (fun x => y - f x) a :=
  continuousAt_const.sub h
lemma ContinuousOn.const_sub (h : ContinuousOn f D) : ContinuousOn (fun x => y - f x) D :=
  continuousOn_const.sub h
lemma Continuous.const_sub (h : Continuous f) : Continuous fun x => y - f x := continuous_const.sub h

end

section

variable {X M : Type*} [TopologicalSpace X] [TopologicalSpace M] [Mul M] [ContinuousMul M]
    {f : X → M} {D : Set X} {a : X} (y : M)

lemma ContinuousWithinAt.mul_const (h : ContinuousWithinAt f D a) : ContinuousWithinAt (fun x => f x * y) D a :=
  h.mul continuousWithinAt_const
lemma ContinuousAt.mul_const (h : ContinuousAt f a) : ContinuousAt (fun x => f x * y) a :=
  h.mul continuousAt_const
lemma ContinuousOn.mul_const (h : ContinuousOn f D) : ContinuousOn (fun x => f x * y) D :=
  h.mul continuousOn_const
lemma Continuous.mul_const (h : Continuous f) : Continuous fun x => f x * y := h.mul continuous_const

lemma ContinuousWithinAt.const_mul (h : ContinuousWithinAt f D a) : ContinuousWithinAt (fun x => y * f x) D a :=
  continuousWithinAt_const.mul h
lemma ContinuousAt.const_mul (h : ContinuousAt f a) : ContinuousAt (fun x => y * f x) a :=
  continuousAt_const.mul h
lemma ContinuousOn.const_mul (h : ContinuousOn f D) : ContinuousOn (fun x => y * f x) D :=
  continuousOn_const.mul h
lemma Continuous.const_mul (h : Continuous f) : Continuous fun x => y * f x := continuous_const.mul h

end

section

variable {X G₀ : Type*} [TopologicalSpace X] [TopologicalSpace G₀] [GroupWithZero G₀] [ContinuousInv₀ G₀]
    [ContinuousMul G₀] {f : X → G₀} {D : Set X} {a : X} (y : G₀)

lemma ContinuousWithinAt.const_div (h : ContinuousWithinAt f D a) (hf : f a ≠ 0) :
    ContinuousWithinAt (fun x => y / f x) D a := continuousWithinAt_const.div h hf
lemma ContinuousAt.const_div (h : ContinuousAt f a) (hf : f a ≠ 0) :
    ContinuousAt (fun x => y / f x) a := continuousAt_const.div h hf
lemma ContinuousOn.const_div (h : ContinuousOn f D) (hf : ∀ x ∈ D, f x ≠ 0) :
    ContinuousOn (fun x => y / f x) D := continuousOn_const.div h hf
lemma Continuous.const_div (h : Continuous f) (hf : ∀ x, f x ≠ 0) :
    Continuous fun x => y / f x := continuous_const.div h hf

end

lemma HasLimAt.comp_continuousWithinAt {f h : ℝ → ℝ} {D₁ D₂ : Set ℝ}
    (hd : ∀ x ∈ D₁, f x ∈ D₂) {a : EReal} {g : ℝ} :
    HasLimAt f D₁ a g → ContinuousWithinAt h D₂ g → HasLimAt (h ∘ f) D₁ a (h g) :=
  fun hf hh => hf.comp hd (continuousWithinAt_iff_hasLimAt.mp hh)

lemma HasLimAt.comp_continuousAt {f h : ℝ → ℝ} {D : Set ℝ} {a : EReal} {g : ℝ} :
    HasLimAt f D a g → ContinuousAt h g → HasLimAt (h ∘ f) D a (h g) :=
  fun hf hh => hf.comp (by simp) (continuousAt_iff_hasLimAt.mp hh)

lemma HasLimAt.comp_continuousOn {f h : ℝ → ℝ} {D₁ D₂ : Set ℝ}
    (hd : ∀ x ∈ D₁, f x ∈ D₂) {a : EReal} {g : ℝ}
    (hg : g ∈ D₂) : HasLimAt f D₁ a g → ContinuousOn h D₂ → HasLimAt (h ∘ f) D₁ a (h g) :=
  fun hf hh => hf.comp hd (hh.hasLimAt hg)

lemma HasLimAt.comp_continuous {f h : ℝ → ℝ} {D : Set ℝ} {a : EReal} {g : ℝ} :
    HasLimAt f D a g → Continuous h → HasLimAt (h ∘ f) D a (h g) :=
  fun hf hh => hf.comp (by simp) (hh.hasLimAt g)

lemma HasLimAt.sin {f : ℝ → ℝ} {D : Set ℝ} {a : EReal} {g : ℝ} (h : HasLimAt f D a g) :
    HasLimAt (fun x => Real.sin (f x)) D a (Real.sin g) :=
  h.comp_continuous Real.continuous_sin

lemma HasLimAt.cos {f : ℝ → ℝ} {D : Set ℝ} {a : EReal} {g : ℝ} (h : HasLimAt f D a g) :
    HasLimAt (fun x => Real.cos (f x)) D a (Real.cos g) :=
  h.comp_continuous Real.continuous_cos

/-- **Th. 4.6.** Equivalent to `deriv Real.sin 0 = 1` -/
theorem hasLimAt_sin_div : HasLimAt (fun x => Real.sin x / x) Set.univ 0 1 := by
  apply hasLimAt_iff_left_and_right.mpr
  rw [and_iff_right_of_imp]
  · apply HasLimAt.squeeze_const (f := Real.cos)
    · exists 1, zero_lt_one
      simp
      intro x h1 _ h2
      rw [le_div_comm₀ (Real.cos_pos_of_le_one h2.le) h1,
        ← Real.tan_eq_sin_div_cos]
      exact Real.le_tan h1.le (lt_of_lt_of_le (abs_lt.mp h2).right Real.one_le_pi_div_two)
    · exists 1, zero_lt_one; simp; intro x h _ _; exact (div_le_one h).mpr (Real.sin_le h.le)
    · convert (Real.continuous_cos.hasLimAt 0).subset (by simp); simp
  · intro hr x hx ha
    specialize hr (fun n => -x n)
    apply HasLim.neg at ha
    simp at hr hx ha
    exact hr hx ha

lemma HasLimAt.rexp {f : ℝ → ℝ} {D : Set ℝ} {a : EReal} {g : ℝ} (h : HasLimAt f D a g) :
    HasLimAt (fun x => Real.exp (f x)) D a (Real.exp g) :=
  h.comp_continuous Real.continuous_exp

lemma HasLimAt.rexp_top {f : ℝ → ℝ} {D : Set ℝ} {a : EReal} (h : HasLimAt f D a ⊤) :
    HasLimAt (fun x => Real.exp (f x)) D a ⊤ :=
  (h.add_const 1).squeeze_top (eventually_true fun x _ => Real.add_one_le_exp (f x))

lemma HasLimAt.rexp_bot {f : ℝ → ℝ} {D : Set ℝ} {a : EReal} (h : HasLimAt f D a ⊥) :
    HasLimAt (fun x => Real.exp (f x)) D a 0 := by
  rw [← EReal.coe_zero]; apply h.comp_bot (h := Real.exp) (D₂ := Set.univ) (by simp)
  apply hasLimAt_at_bot_iff_tendsto.mpr; simp [Real.tendsto_exp_atBot]

lemma HasLimAt.const_rpow {f : ℝ → ℝ} {D : Set ℝ} {a : EReal} {g r : ℝ} (hr : r ≠ 0)
    (h : HasLimAt f D a g) : HasLimAt (fun x => r ^ f x) D a (r ^ g : ℝ) :=
  h.comp_continuous (Real.continuous_const_rpow hr)

lemma HasLimAt.log {f : ℝ → ℝ} {D : Set ℝ} {a : EReal} {g : ℝ} (hg : g ≠ 0)
    (h : HasLimAt f D a g) : HasLimAt (fun x => Real.log (f x)) D a (Real.log g) :=
  h.comp_continuousAt (Real.continuousAt_log hg)

/-- **Th. 7.3.** Weierstrass's extreme value theorem: a continuous function on a
closed bounded interval attains a minimum. -/
lemma ContinuousOn.exists_isMinOn_Icc {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (h : ContinuousOn f (Set.Icc a b)) : ∃ x ∈ Set.Icc a b, IsMinOn f (Set.Icc a b) x :=
  IsCompact.exists_isMinOn isCompact_Icc (by simpa) h

/-- **Th. 7.3.** Weierstrass's extreme value theorem: a continuous function on a
closed bounded interval attains a maximum. -/
lemma ContinuousOn.exists_isMaxOn_Icc {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (h : ContinuousOn f (Set.Icc a b)) : ∃ x ∈ Set.Icc a b, IsMaxOn f (Set.Icc a b) x :=
  IsCompact.exists_isMaxOn isCompact_Icc (by simpa) h
