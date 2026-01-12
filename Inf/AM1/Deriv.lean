import Inf.AM1.LimitAt
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.LHopital
import Mathlib.Analysis.Calculus.Taylor

/-! # Lectures 8-10

Relate properties of derivatives to `HasLimAt` -/

lemma hasDerivWithinAt_iff_hasLimAt {f : ℝ → ℝ} {D : Set ℝ} {x f' : ℝ} :
    HasDerivWithinAt f f' D x ↔ HasLimAt (fun x' => (f x' - f x) / (x' - x)) D x f' := by
  simp [hasDerivWithinAt_iff_tendsto_slope, ← hasLimAt_iff_tendsto, slope_fun_def_field]

lemma hasDerivAt_iff_hasLimAt {f : ℝ → ℝ} {x f' : ℝ} : HasDerivAt f f' x ↔
    HasLimAt (fun x' => (f x' - f x) / (x' - x)) Set.univ x f' := by
  rw [← hasDerivWithinAt_univ, hasDerivWithinAt_iff_hasLimAt]

lemma hasDerivAt_iff_hasLimAt' {f : ℝ → ℝ} {x f' : ℝ} : HasDerivAt f f' x ↔
    HasLimAt (fun h => (f (x + h) - f x) / h) Set.univ 0 f' := by
  simp [hasDerivAt_iff_tendsto_slope_zero, ← EReal.coe_zero, hasLimAt_iff_tendsto]; convert Iff.rfl using 3
  · grind
  · ext; simp

lemma hasLimAt_derivWithin {f : ℝ → ℝ} {D : Set ℝ} {x : ℝ} (h : DifferentiableWithinAt ℝ f D x) :
    HasLimAt (fun x' => (f x' - f x) / (x' - x)) D x (derivWithin f D x : ℝ) :=
  hasDerivWithinAt_iff_hasLimAt.mp h.hasDerivWithinAt

lemma hasLimAt_deriv {f : ℝ → ℝ} {x : ℝ} (h : DifferentiableAt ℝ f x) :
    HasLimAt (fun x' => (f x' - f x) / (x' - x)) Set.univ x (deriv f x : ℝ) :=
  hasDerivAt_iff_hasLimAt.mp h.hasDerivAt

lemma hasLimAt_deriv' {f : ℝ → ℝ} {x : ℝ} (h : DifferentiableAt ℝ f x) :
    HasLimAt (fun h => (f (x + h) - f x) / h) Set.univ 0 (deriv f x : ℝ) :=
  hasDerivAt_iff_hasLimAt'.mp h.hasDerivAt

/-- **Thm. 10.1. L'Hôpital's rule** for [0 / 0] indeterminate limits, `HasDerivAt` version. -/
theorem HasDerivAt.lhopital_zero_hasLimAt {f f' g g' : ℝ → ℝ} {a : ℝ} {l : EReal}
    (hff' : Eventually Set.univ a fun x => HasDerivAt f (f' x) x)
    (hgg' : Eventually Set.univ a fun x => HasDerivAt g (g' x) x)
    (hg' : Eventually Set.univ a fun x => g' x ≠ 0)
    (hf : HasLimAt f Set.univ a 0) (hg : HasLimAt g Set.univ a 0)
    (hdiv : HasLimAt (fun x => f' x / g' x) Set.univ a l) : HasLimAt (fun x => f x / g x) Set.univ a l := by
  simp [-eventually_coe, eventually_def, ← Set.compl_eq_univ_diff, ← EReal.coe_zero, hasLimAt_iff_tendsto] at *
  cases l <;>
  · simp [hasLimAt_iff_tendsto, hasLimAt_top_iff_tendsto, hasLimAt_bot_iff_tendsto, ← Set.compl_eq_univ_diff] at *
    exact HasDerivAt.lhopital_zero_nhdsNE hff' hgg' hg' hf hg hdiv

/-- **Thm. 10.1. L'Hôpital's rule** for [0 / 0] indeterminate limits, `deriv` version. -/
theorem deriv.lhopital_zero_hasLimAt {f g : ℝ → ℝ} {a : ℝ} {l : EReal}
    (hdf : Eventually Set.univ a fun x => DifferentiableAt ℝ f x)
    (hg' : Eventually Set.univ a fun x => deriv g x ≠ 0)
    (hf : HasLimAt f Set.univ a 0) (hg : HasLimAt g Set.univ a 0)
    (hdiv : HasLimAt (fun x => deriv f x / deriv g x) Set.univ a l) : HasLimAt (fun x => f x / g x) Set.univ a l := by
  simp [-eventually_coe, eventually_def, ← Set.compl_eq_univ_diff, ← EReal.coe_zero, hasLimAt_iff_tendsto] at *
  cases l <;>
  · simp [hasLimAt_iff_tendsto, hasLimAt_top_iff_tendsto, hasLimAt_bot_iff_tendsto, ← Set.compl_eq_univ_diff] at *
    exact deriv.lhopital_zero_nhdsNE hdf hg' hf hg hdiv

/-- **Thm. 10.1. L'Hôpital's rule** for limits in `⊤`, `HasDerivAt` version. -/
theorem HasDerivAt.lhopital_zero_hasLimAt_top {f f' g g' : ℝ → ℝ} {l : EReal}
    (hff' : Eventually Set.univ ⊤ fun x => HasDerivAt f (f' x) x)
    (hgg' : Eventually Set.univ ⊤ fun x => HasDerivAt g (g' x) x)
    (hg' : Eventually Set.univ ⊤ fun x => g' x ≠ 0)
    (hf : HasLimAt f Set.univ ⊤ 0) (hg : HasLimAt g Set.univ ⊤ 0)
    (hdiv : HasLimAt (fun x => f' x / g' x) Set.univ ⊤ l) : HasLimAt (fun x => f x / g x) Set.univ ⊤ l := by
  simp [eventually_top_def, ← EReal.coe_zero, hasLimAt_at_top_iff_tendsto, -Filter.eventually_atTop] at *
  cases l <;>
  · simp [hasLimAt_at_top_iff_tendsto, hasLimAt_top_top_iff_tendsto, hasLimAt_top_bot_iff_tendsto] at ⊢ hdiv
    exact HasDerivAt.lhopital_zero_atTop hff' hgg' hg' hf hg hdiv

/-- **Thm. 10.1. L'Hôpital's rule** for limits in `⊤`, `deriv` version. -/
theorem deriv.lhopital_zero_hasLimAt_top {f g : ℝ → ℝ} {l : EReal}
    (hdf : Eventually Set.univ ⊤ fun x => DifferentiableAt ℝ f x)
    (hg' : Eventually Set.univ ⊤ fun x => deriv g x ≠ 0)
    (hf : HasLimAt f Set.univ ⊤ 0) (hg : HasLimAt g Set.univ ⊤ 0)
    (hdiv : HasLimAt (fun x => deriv f x / deriv g x) Set.univ ⊤ l) : HasLimAt (fun x => f x / g x) Set.univ ⊤ l := by
  simp [eventually_top_def, ← EReal.coe_zero, hasLimAt_at_top_iff_tendsto, -Filter.eventually_atTop] at *
  cases l <;>
  · simp [hasLimAt_at_top_iff_tendsto, hasLimAt_top_top_iff_tendsto, hasLimAt_top_bot_iff_tendsto] at ⊢ hdiv
    exact deriv.lhopital_zero_atTop hdf hg' hf hg hdiv

/-- **Thm. 10.1. L'Hôpital's rule** for limits in `⊥`, `HasDerivAt` version. -/
theorem HasDerivAt.lhopital_zero_hasLimAt_bot {f f' g g' : ℝ → ℝ} {l : EReal}
    (hff' : Eventually Set.univ ⊥ fun x => HasDerivAt f (f' x) x)
    (hgg' : Eventually Set.univ ⊥ fun x => HasDerivAt g (g' x) x)
    (hg' : Eventually Set.univ ⊥ fun x => g' x ≠ 0)
    (hf : HasLimAt f Set.univ ⊥ 0) (hg : HasLimAt g Set.univ ⊥ 0)
    (hdiv : HasLimAt (fun x => f' x / g' x) Set.univ ⊥ l) : HasLimAt (fun x => f x / g x) Set.univ ⊥ l := by
  simp [eventually_bot_def, ← EReal.coe_zero, hasLimAt_at_bot_iff_tendsto, -Filter.eventually_atBot] at *
  cases l <;>
  · simp [hasLimAt_at_bot_iff_tendsto, hasLimAt_bot_top_iff_tendsto, hasLimAt_bot_bot_iff_tendsto] at ⊢ hdiv
    exact HasDerivAt.lhopital_zero_atBot hff' hgg' hg' hf hg hdiv

/-- **Thm. 10.1. L'Hôpital's rule** for limits in `⊥`, `deriv` version. -/
theorem deriv.lhopital_zero_hasLimAt_bot {f g : ℝ → ℝ} {l : EReal}
    (hdf : Eventually Set.univ ⊥ fun x => DifferentiableAt ℝ f x)
    (hg' : Eventually Set.univ ⊥ fun x => deriv g x ≠ 0)
    (hf : HasLimAt f Set.univ ⊥ 0) (hg : HasLimAt g Set.univ ⊥ 0)
    (hdiv : HasLimAt (fun x => deriv f x / deriv g x) Set.univ ⊥ l) : HasLimAt (fun x => f x / g x) Set.univ ⊥ l := by
  simp [eventually_bot_def, ← EReal.coe_zero, hasLimAt_at_bot_iff_tendsto, -Filter.eventually_atBot] at *
  cases l <;>
  · simp [hasLimAt_at_bot_iff_tendsto, hasLimAt_bot_top_iff_tendsto, hasLimAt_bot_bot_iff_tendsto] at ⊢ hdiv
    exact deriv.lhopital_zero_atBot hdf hg' hf hg hdiv

theorem HasDerivAt.lhopital_zero_hasLimAt' {f f' g g' : ℝ → ℝ} {a l : EReal}
    (hff' : Eventually Set.univ a fun x => HasDerivAt f (f' x) x)
    (hgg' : Eventually Set.univ a fun x => HasDerivAt g (g' x) x)
    (hg' : Eventually Set.univ a fun x => g' x ≠ 0)
    (hf : HasLimAt f Set.univ a 0) (hg : HasLimAt g Set.univ a 0)
    (hdiv : HasLimAt (fun x => f' x / g' x) Set.univ a l) : HasLimAt (fun x => f x / g x) Set.univ a l :=
  match a with
  | (a : ℝ) => HasDerivAt.lhopital_zero_hasLimAt hff' hgg' hg' hf hg hdiv
  | ⊤ => HasDerivAt.lhopital_zero_hasLimAt_top hff' hgg' hg' hf hg hdiv
  | ⊥ => HasDerivAt.lhopital_zero_hasLimAt_bot hff' hgg' hg' hf hg hdiv

theorem deriv.lhopital_zero_hasLimAt' {f g : ℝ → ℝ} {a l : EReal}
    (hdf : Eventually Set.univ a fun x => DifferentiableAt ℝ f x)
    (hg' : Eventually Set.univ a fun x => deriv g x ≠ 0)
    (hf : HasLimAt f Set.univ a 0) (hg : HasLimAt g Set.univ a 0)
    (hdiv : HasLimAt (fun x => deriv f x / deriv g x) Set.univ a l) : HasLimAt (fun x => f x / g x) Set.univ a l :=
  match a with
  | (a : ℝ) => deriv.lhopital_zero_hasLimAt hdf hg' hf hg hdiv
  | ⊤ => deriv.lhopital_zero_hasLimAt_top hdf hg' hf hg hdiv
  | ⊥ => deriv.lhopital_zero_hasLimAt_bot hdf hg' hf hg hdiv

/-- **Thm. 10.1. L'Hôpital's rule** for left limits, `HasDerivAt` version. -/
theorem HasDerivAt.lhopital_zero_hasLeftLim {f f' g g' : ℝ → ℝ} {a : ℝ} {l : EReal}
    (hff' : Eventually (Set.Iio a) a fun x => HasDerivAt f (f' x) x)
    (hgg' : Eventually (Set.Iio a) a fun x => HasDerivAt g (g' x) x)
    (hg' : Eventually (Set.Iio a) a fun x => g' x ≠ 0)
    (hf : HasLimAt f (Set.Iio a) a 0) (hg : HasLimAt g (Set.Iio a) a 0)
    (hdiv : HasLeftLim (fun x => f' x / g' x) Set.univ a l) : HasLeftLim (fun x => f x / g x) Set.univ a l := by
  simp [-eventually_coe, eventually_def, ← EReal.coe_zero, hasLimAt_iff_tendsto] at *; cases l <;>
  · simp [hasLimAt_iff_tendsto, hasLimAt_top_iff_tendsto, hasLimAt_bot_iff_tendsto] at *
    exact HasDerivAt.lhopital_zero_nhdsLT hff' hgg' hg' hf hg hdiv

/-- **Thm. 10.1. L'Hôpital's rule** for left limits, `deriv` version. -/
theorem deriv.lhopital_zero_hasLeftLim {f g : ℝ → ℝ} {a : ℝ} {l : EReal}
    (hdf : Eventually (Set.Iio a) a fun x => DifferentiableAt ℝ f x)
    (hg' : Eventually (Set.Iio a) a fun x => deriv g x ≠ 0)
    (hf : HasLimAt f (Set.Iio a) a 0) (hg : HasLimAt g (Set.Iio a) a 0)
    (hdiv : HasLeftLim (fun x => deriv f x / deriv g x) Set.univ a l) : HasLeftLim (fun x => f x / g x) Set.univ a l := by
  simp [-eventually_coe, eventually_def, ← EReal.coe_zero, hasLimAt_iff_tendsto] at *; cases l <;>
  · simp [hasLimAt_iff_tendsto, hasLimAt_top_iff_tendsto, hasLimAt_bot_iff_tendsto] at *
    exact deriv.lhopital_zero_nhdsLT hdf hg' hf hg hdiv

/-- **Thm. 10.1. L'Hôpital's rule** for right limits, `HasDerivAt` version. -/
theorem HasDerivAt.lhopital_zero_hasRightLim {f f' g g' : ℝ → ℝ} {a : ℝ} {l : EReal}
    (hff' : Eventually (Set.Ioi a) a fun x => HasDerivAt f (f' x) x)
    (hgg' : Eventually (Set.Ioi a) a fun x => HasDerivAt g (g' x) x)
    (hg' : Eventually (Set.Ioi a) a fun x => g' x ≠ 0)
    (hf : HasLimAt f (Set.Ioi a) a 0) (hg : HasLimAt g (Set.Ioi a) a 0)
    (hdiv : HasRightLim (fun x => f' x / g' x) Set.univ a l) : HasRightLim (fun x => f x / g x) Set.univ a l := by
  simp [-eventually_coe, eventually_def, ← EReal.coe_zero, hasLimAt_iff_tendsto] at *; cases l <;>
  · simp [hasLimAt_iff_tendsto, hasLimAt_top_iff_tendsto, hasLimAt_bot_iff_tendsto] at *
    exact HasDerivAt.lhopital_zero_nhdsGT hff' hgg' hg' hf hg hdiv

/-- **Thm. 10.1. L'Hôpital's rule** for right limits, `deriv` version. -/
theorem deriv.lhopital_zero_hasRightLim {f g : ℝ → ℝ} {a : ℝ} {l : EReal}
    (hdf : Eventually (Set.Ioi a) a fun x => DifferentiableAt ℝ f x)
    (hg' : Eventually (Set.Ioi a) a fun x => deriv g x ≠ 0)
    (hf : HasLimAt f (Set.Ioi a) a 0) (hg : HasLimAt g (Set.Ioi a) a 0)
    (hdiv : HasRightLim (fun x => deriv f x / deriv g x) Set.univ a l) : HasRightLim (fun x => f x / g x) Set.univ a l := by
  simp [-eventually_coe, eventually_def, ← EReal.coe_zero, hasLimAt_iff_tendsto] at *; cases l <;>
  · simp [hasLimAt_iff_tendsto, hasLimAt_top_iff_tendsto, hasLimAt_bot_iff_tendsto] at *
    exact deriv.lhopital_zero_nhdsGT hdf hg' hf hg hdiv

/-- **Thm. 10.3.** Taylor series with remainder expressed as a limit. -/
theorem taylor_hasLimAt {f : ℝ → ℝ} {x₀ : ℝ} {n : ℕ} {D : Set ℝ}
    (hD : Convex ℝ D) (hx₀ : x₀ ∈ D) (hf : ContDiffOn ℝ (↑n) f D) :
    HasLimAt (fun (x : ℝ) => (f x - taylorWithinEval f n D x₀ x) / (x - x₀) ^ n) D x₀ 0 :=
  hasLimAt_iff_tendsto.mpr (tendsto_nhdsWithin_mono_left Set.diff_subset (Real.taylor_tendsto hD hx₀ hf))
