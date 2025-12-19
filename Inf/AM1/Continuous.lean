import Inf.AM1.LimitAt
/-! **End of lecture 5, lectures 6 & 7**

Mathlib already has predicates `Continuous`, `ContinuousOn`, `ContinuousAt`
and `ContinuousWithinAt`, meaning this file here is mostly glue and restatements
of theorems involving limits. -/

/-- (Heine's) definition of function continuity.

Cauchy's epsilon-delta definition is `Metric.continuousWithinAt_iff` -/
lemma continuousWithinAt_iff_hasLim {f : ℝ → ℝ} {D : Set ℝ} {a : ℝ} :
    ContinuousWithinAt f D a ↔ ∀ x, (∀ n, x n ∈ D) → HasLim x a → HasLim (f ∘ x) (f a) := by
  rw [ContinuousWithinAt, Filter.tendsto_iff_seq_tendsto]
  simp [hasLim_iff_tendsto, tendsto_nhdsWithin_iff]; constructor
  · exact fun h x hd ht => h x ht 0 (fun n _ => hd n)
  intro h x ht n0 hx
  specialize h (fun n => x (max n n0)) (fun n => hx _ (by simp)) (ht.congr' ?_)
  · simp [Filter.EventuallyEq]; exists n0; intro n hn; congr; simpa
  refine h.congr' ?_; simp [Filter.EventuallyEq]; exists n0; intro n hn; congr; simpa

/-- (Heine's) definition of function continuity.

Cauchy's epsilon-delta definition is `Metric.continuousAt_iff` -/
lemma continuousAt_iff_hasLim {f : ℝ → ℝ} {a : ℝ} :
    ContinuousAt f a ↔ ∀ x, HasLim x a → HasLim (f ∘ x) (f a) := by
  rw [← continuousWithinAt_univ, continuousWithinAt_iff_hasLim]; simp

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
  simp [Metric.continuousWithinAt_iff, HasLimAt.def]; constructor
  · intro h e he; replace ⟨d, hd, h⟩ := h e he; exists d, hd; exact fun x hx _ => h hx
  intro h e he; replace ⟨d, hd, h⟩ := h e he; exists d, hd; intro x hx; specialize h x hx
  by_cases x = a
  case pos heq => subst heq; simp; tauto
  case neg hne => exact h hne

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

variable [Field R] [LinearOrder R]

lemma HasLimAt.comp_continuousWithinAt {f : R → ℝ} {h : ℝ → ℝ} {D₁ : Set R} {D₂ : Set ℝ}
    (hd : ∀ x ∈ D₁, f x ∈ D₂) {a : WithBot (WithTop R)} {g : ℝ} :
    HasLimAt f D₁ a g → ContinuousWithinAt h D₂ g → HasLimAt (h ∘ f) D₁ a (h g) :=
  fun hf hh => hf.comp hd (continuousWithinAt_iff_hasLimAt.mp hh)

lemma HasLimAt.comp_continuousAt {f : R → ℝ} {h : ℝ → ℝ} {D : Set R} {a : WithBot (WithTop R)} {g : ℝ} :
    HasLimAt f D a g → ContinuousAt h g → HasLimAt (h ∘ f) D a (h g) :=
  fun hf hh => hf.comp (by simp) (continuousAt_iff_hasLimAt.mp hh)

lemma HasLimAt.comp_continuousOn {f : R → ℝ} {h : ℝ → ℝ} {D₁ : Set R} {D₂ : Set ℝ}
    (hd : ∀ x ∈ D₁, f x ∈ D₂) {a : WithBot (WithTop R)} {g : ℝ}
    (hg : g ∈ D₂) : HasLimAt f D₁ a g → ContinuousOn h D₂ → HasLimAt (h ∘ f) D₁ a (h g) :=
  fun hf hh => hf.comp hd (hh.hasLimAt hg)

lemma HasLimAt.comp_continuous {f : R → ℝ} {h : ℝ → ℝ} {D : Set R} {a : WithBot (WithTop R)} {g : ℝ} :
    HasLimAt f D a g → Continuous h → HasLimAt (h ∘ f) D a (h g) :=
  fun hf hh => hf.comp (by simp) (hh.hasLimAt g)

lemma HasLimAt.sin {f : R → ℝ} {D : Set R} {a : WithBot (WithTop R)} {g : ℝ} (h : HasLimAt f D a g) :
    HasLimAt (fun x => Real.sin (f x)) D a (Real.sin g) :=
  h.comp_continuous Real.continuous_sin

lemma HasLimAt.cos {f : R → ℝ} {D : Set R} {a : WithBot (WithTop R)} {g : ℝ} (h : HasLimAt f D a g) :
    HasLimAt (fun x => Real.cos (f x)) D a (Real.cos g) :=
  h.comp_continuous Real.continuous_cos

/-- **Th. 4.6.** Equivalent to `deriv Real.sin 0 = 1` -/
theorem hasLimAt_sin_div : HasLimAt (fun x => Real.sin x / x) Set.univ 0 1 := by
  apply hasLimAt_iff_left_and_right.mpr; rw [and_iff_right_of_imp]
  · apply HasLimAt.squeeze_const (f := Real.cos)
    · exists 1, zero_lt_one; simp; intro x h1 _ h2
      rw [le_div_comm₀ (Real.cos_pos_of_le_one h2.le) h1, ← Real.tan_eq_sin_div_cos]
      exact Real.le_tan h1.le (lt_of_lt_of_le (abs_lt.mp h2).2 Real.one_le_pi_div_two)
    · exists 1, zero_lt_one; simp; intro x h _ _; exact (div_le_one h).mpr (Real.sin_le h.le)
    · convert (Real.continuous_cos.hasLimAt 0).subset (by simp); simp
  · intro hr x hx ha; specialize hr (fun n => -x n); apply HasLim.neg at ha
    simp [WithBot.some, WithTop.some, Function.comp_def] at hr hx ha
    exact hr hx ha

lemma HasLimAt.rexp {f : R → ℝ} {D : Set R} {a : WithBot (WithTop R)} {g : ℝ} (h : HasLimAt f D a g) :
    HasLimAt (fun x => Real.exp (f x)) D a (Real.exp g) :=
  h.comp_continuous Real.continuous_exp

lemma HasLimAt.const_rpow {f : R → ℝ} {D : Set R} {a : WithBot (WithTop R)} {g r : ℝ} (hr : r ≠ 0)
    (h : HasLimAt f D a g) : HasLimAt (fun x => r ^ f x) D a (r ^ g : ℝ) :=
  h.comp_continuous (Real.continuous_const_rpow hr)

lemma HasLimAt.log {f : R → ℝ} {D : Set R} {a : WithBot (WithTop R)} {g : ℝ} (hg : g ≠ 0)
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
