import Inf.AM1.Limit
import Mathlib.Topology.Perfect

/-! # Lectures 4 & 5

Again - not using `Filter.Tendsto`, instead introducing `HasLimAt`.

Definitions:

- `Set.AccPt D a` - `a` is an accumulation point of `D` (not using regular `AccPt` because filters)

- `HasLimAt f D a g` - `f : D → ℝ` has a limit `g` at point `a` (both `g` and `a` may be `⊤` or `⊥`)

- `Eventually D a p` - predicate `p` holds on some neighborhood of `a`

- `HasLeftLim f D a g` and `HasRightLim f D a g` - left and right limits

Note that the limit definitions don't check nor require that the point is in / an accumulation point of
the domain (it needs to be shown separately if of interest) - if it's not, they're all vacuously true.
-/

def Set.AccPt (D : Set ℝ) (a : EReal) :=
    ∃ x : ℕ → ℝ, (∀ n, x n ∈ D ∧ x n ≠ a) ∧ HasLim' x a

def Set.accPt_iff {D : Set ℝ} {a : ℝ} : D.AccPt a ↔ _root_.AccPt a (.principal D) := by
  simp [AccPt, accPt_iff_frequently, (nhds_basis_abs_sub_lt a).frequently_iff]
  constructor
  · intro ⟨x, hx, ha⟩ e he
    replace ⟨n, ha⟩ := ha e he
    exact ⟨x n, ha n le_rfl, (hx n).symm⟩
  · intro h
    choose! x h using h
    exists fun n => x (n + 1)⁻¹
    and_intros
    · exact fun n => (h _ (by positivity)).right.symm
    · refine fun e he => ⟨⌈e⁻¹⌉₊ - 1, fun n hn => ?_⟩
      simp at hn
      exact (h _ (by positivity)).left.trans_le (inv_le_of_inv_le₀ he hn)

@[simp]
def Set.accPt_top_iff {D : Set ℝ} : D.AccPt ⊤ ↔ ¬BddAbove D := by
  simp [not_bddAbove_iff, AccPt]
  constructor
  · intro ⟨x, hx, ht⟩ d
    replace ⟨n, ht⟩ := ht d
    exact ⟨x n, hx n, ht n le_rfl⟩
  · intro h
    choose x h using h
    exists fun n => x n, fun n => (h n).left
    refine fun d => ⟨⌈d⌉₊, fun n hn => ?_⟩
    simp at hn
    exact hn.trans_lt (h n).right

@[simp]
def Set.accPt_bot_iff {D : Set ℝ} : D.AccPt ⊥ ↔ ¬BddBelow D := by
  simp [not_bddBelow_iff, AccPt]
  constructor
  · intro ⟨x, hx, ht⟩ d
    replace ⟨n, ht⟩ := ht d
    exact ⟨x n, hx n, ht n le_rfl⟩
  · intro h
    choose x h using h
    exists fun n => x (-n), fun n => (h (-n)).left
    refine fun d => ⟨⌈-d⌉₊, fun n hn => ?_⟩
    simp [neg_le (a := d)] at hn
    exact hn.trans_lt' (h (-n)).right

@[simp]
lemma Set.accPt_univ {a : EReal} : Set.AccPt Set.univ a := by
  induction a <;> simp [accPt_iff, _root_.AccPt, NormedField.nhdsNE_neBot]

lemma Set.accPt_subset {d D : Set ℝ} {a : EReal} (hss: d ⊆ D) (ha : d.AccPt a) : D.AccPt a := by
  peel 1 ha
  grw [← hss]
  assumption

@[simp]
lemma Set.accPt_Ioo {a b c : ℝ} (h : a < b) : (Set.Ioo a b).AccPt c ↔ c ∈ Set.Icc a b := by
  constructor
  · simp [AccPt]
    exact fun x hx hc => ⟨hc.const_le ⟨0, fun n _ => (hx n).1.1.le⟩, hc.le_const ⟨0, fun n _ => (hx n).1.2.le⟩⟩
  · simp [accPt_iff]
    by_cases! c = a; · subst c; simp [accPt_principal_iff_nhdsWithin, left_nhdsWithin_Ioo_neBot h]
    by_cases! c = b; · subst c; simp [accPt_principal_iff_nhdsWithin, right_nhdsWithin_Ioo_neBot h]
    refine fun _ _ => inter_univ (Ioo a b) ▸ (accPt_iff.mp accPt_univ).nhds_inter ?_
    apply Ioo_mem_nhds <;> order

@[simp]
lemma Set.accPt_Icc {a b c : ℝ} (h : a < b) : (Set.Icc a b).AccPt c ↔ c ∈ Set.Icc a b := by
  constructor
  · simp [AccPt]
    exact fun x hx hc => ⟨hc.const_le ⟨0, fun n _ => (hx n).1.1⟩, hc.le_const ⟨0, fun n _ => (hx n).1.2⟩⟩
  · rw [← accPt_Ioo h]; exact accPt_subset Ioo_subset_Icc_self

@[simp]
lemma Set.accPt_Ico {a b c : ℝ} (h : a < b) : (Set.Ico a b).AccPt c ↔ c ∈ Set.Icc a b :=
  ⟨(accPt_Icc h).mp.comp (accPt_subset Ico_subset_Icc_self),
    (accPt_subset Ioo_subset_Ico_self).comp (accPt_Ioo h).mpr⟩

@[simp]
lemma Set.accPt_Ioc {a b c : ℝ} (h : a < b) :
    (Set.Ioc a b).AccPt c ↔ c ∈ Set.Icc a b :=
  ⟨(accPt_Icc h).mp.comp (accPt_subset Ioc_subset_Icc_self),
    (accPt_subset Ioo_subset_Ioc_self).comp (accPt_Ioo h).mpr⟩

@[simp]
lemma Set.accPt_Iio {a : ℝ} {b : EReal} : (Set.Iio a).AccPt b ↔ b ≤ a := by
  use fun ⟨x, hx, hb⟩ => hb.le_const ⟨0, fun n _ => (hx n).1.le⟩
  induction b <;> simp [not_bddBelow_Iio]
  rename_i b; intro hb
  apply accPt_subset (Ioo_subset_Iio_self (a := b - 1))
  rw [accPt_Ioo] <;> grind

@[simp]
lemma Set.accPt_Iic {a : ℝ} {b : EReal} : (Set.Iic a).AccPt b ↔ b ≤ a := by
  use fun ⟨x, hx, hb⟩ => hb.le_const ⟨0, fun n _ => (hx n).1⟩
  rw [← accPt_Iio]
  exact accPt_subset (Iio_subset_Iic_self)

@[simp]
lemma Set.accPt_Ioi {a : ℝ} {b : EReal} : (Set.Ioi a).AccPt b ↔ a ≤ b := by
  use fun ⟨x, hx, hb⟩ => hb.const_le ⟨0, fun n _ => (hx n).1.le⟩
  induction b <;> simp [not_bddAbove_Ioi]
  rename_i b; intro hb
  apply accPt_subset (Ioo_subset_Ioi_self (b := b + 1))
  rw [accPt_Ioo] <;> grind

@[simp]
lemma Set.accPt_Ici {a : ℝ} {b : EReal} : (Set.Ici a).AccPt b ↔ ↑a ≤ b := by
  use fun ⟨x, hx, hb⟩ => hb.const_le ⟨0, fun n _ => (hx n).1⟩
  rw [← accPt_Ioi]
  exact accPt_subset (Ioi_subset_Ici_self)

/-- Limit of a function (Heine's definition). `g` is a the limit of `f` at `a` within the domain `D`
if the image of any sequence with values in `D \ {a}` converging to `a` converges to `g`.-/
def HasLimAt (f : ℝ → ℝ) (D : Set ℝ) (a g : EReal) :=
    ∀ x, (∀ n, x n ∈ D ∧ x n ≠ a) → HasLim' x a → HasLim' (fun n => f (x n)) g

/-- **Th. 4.1.** If a limit exists, it's unique. -/
lemma HasLimAt.eq {f : ℝ → ℝ} {D : Set ℝ} {a g₁ g₂ : EReal} (ha : D.AccPt a) :
    HasLimAt f D a g₁ → HasLimAt f D a g₂ → g₁ = g₂ := by
  replace ⟨x, hx, ha⟩ := ha
  exact fun h1 h2 => (h1 x hx ha).eq (h2 x hx ha)

/-- If the images of two sequences as above do not converge to the same value,
the limit does not exist. -/
lemma not_hasLimAt_of_ne {f : ℝ → ℝ} {D : Set ℝ} {a g₁ g₂ : EReal} {x₁ x₂ : ℕ → ℝ} :
    (∀ n, x₁ n ∈ D ∧ x₁ n ≠ a) → (∀ n, x₂ n ∈ D ∧ x₂ n ≠ a) → HasLim' x₁ a → HasLim' x₂ a →
    HasLim' (f ∘ x₁) g₁ → HasLim' (f ∘ x₂) g₂ → g₁ ≠ g₂ → ¬∃ g, HasLimAt f D a g := by
  intro hx1 hx2 h1 h2 hf1 hf2 hne ⟨g, hg⟩
  apply hne
  exact (hf1.eq (hg x₁ hx1 h1)).trans ((hg x₂ hx2 h2).eq hf2)

/-- Intuitively: `p` holds for all numbers sufficiently close to `a`. -/
abbrev Eventually (D : Set ℝ) (a : EReal) (p : ℝ → Prop) : Prop :=
  match a with
  | (a : ℝ) => ∃ δ > 0, ∀ x ∈ D, x ≠ a → |x - a| < δ → p x
  | ⊤ => ∃ G, ∀ x ∈ D, G < x → p x
  | ⊥ => ∃ G, ∀ x ∈ D, x < G → p x

@[simp]
lemma eventually_coe {D : Set ℝ} {a : ℝ} {p : ℝ → Prop} :
    Eventually D a p ↔ ∃ δ > 0, ∀ x ∈ D, x ≠ a → |x - a| < δ → p x := Iff.rfl

lemma eventually_true {D : Set ℝ} {a : EReal} {p : ℝ → Prop} : (∀ x ∈ D, p x) → Eventually D a p := by
  cases a
  · intro h; simp [Eventually]; use 0; tauto
  · intro h; simp; use 1, zero_lt_one; tauto
  · intro h; simp [Eventually]; use 0; tauto

lemma eventually_iff_hasLim {D : Set ℝ} {a : EReal} {p : ℝ → Prop} :
    Eventually D a p ↔ ∀ x, (∀ n, x n ∈ D ∧ x n ≠ a) → HasLim' x a → ∃ n₀, ∀ n ≥ n₀, p (x n) := by
  constructor
  · cases a
    · intro ⟨G, h⟩ x hx ha; simp [HasLim'] at hx ha
      peel ha G with _ n _ ha; exact h (x n) (hx n) ha
    · intro ⟨d, hd, h⟩ x hx ha; simp [HasLim] at hx ha
      peel ha d hd with _ n _ ha; exact h (x n) (hx n).1 (hx n).2 ha
    · intro ⟨G, h⟩ x hx ha; simp [HasLim'] at hx ha
      peel ha G with _ n _ ha; exact h (x n) (hx n) ha
  · cases a <;> (simp [Eventually]; contrapose!)
    · intro h; choose x h1 h3 h4 using fun (n : ℕ) => h (-n)
      have hb := HasLim'.bot_squeeze ⟨0, fun n _ => (h3 n).le⟩ HasLim'.id.neg
      exact ⟨x, h1, hb, fun n => ⟨n, le_rfl, h4 n⟩⟩
    · rename_i a; intro h; choose x h1 h2 h3 h4 using fun (n : ℕ) => h (n + 1)⁻¹ (by positivity)
      have ha : HasLim x a := by
        refine fun d hd => ⟨⌈d⁻¹⌉₊, fun n hn => ?_⟩
        grw [h3]
        apply inv_lt_of_inv_lt₀ hd
        simp at hn; grind
      exact ⟨x, fun n => ⟨h1 n, h2 n⟩, ha, fun n => ⟨n, le_rfl, h4 n⟩⟩
    · intro h; choose x h1 h3 h4 using fun (n : ℕ) => h n
      have ht := HasLim'.squeeze_top ⟨0, fun n _ => (h3 n).le⟩ HasLim'.id
      exact ⟨x, h1, ht, fun n => ⟨n, le_rfl, h4 n⟩⟩

lemma HasLimAt.def' {f : ℝ → ℝ} {D : Set ℝ} {a : EReal} {g : ℝ} :
    HasLimAt f D a g ↔ ∀ ε > 0, Eventually D a fun x => |f x - g| < ε := by
  simp [eventually_iff_hasLim]; tauto

lemma HasLimAt.def_top' {f : ℝ → ℝ} {D : Set ℝ} {a : EReal} :
    HasLimAt f D a ⊤ ↔ ∀ L, Eventually D a fun x => L < f x := by
  simp [eventually_iff_hasLim]; tauto

lemma HasLimAt.def_bot' {f : ℝ → ℝ} {D : Set ℝ} {a : EReal} :
    HasLimAt f D a ⊥ ↔ ∀ L, Eventually D a fun x => f x < L := by
  simp [eventually_iff_hasLim]; tauto

/-- **Th. 4.2.** Cauchy's (epsilon-delta) definition is equivalent (finite-finite case). -/
lemma HasLimAt.def {f : ℝ → ℝ} {D : Set ℝ} {a g : ℝ} :
    HasLimAt f D a g ↔ ∀ ε > 0, ∃ δ > 0, ∀ x ∈ D, x ≠ a → |x - a| < δ → |f x - g| < ε := HasLimAt.def'

/-- **Th. 4.3.** Cauchy's (epsilon-delta) definition is equivalent (finite-`⊤` case). -/
lemma HasLimAt.def_top {f : ℝ → ℝ} {D : Set ℝ} {a : ℝ} :
    HasLimAt f D a ⊤ ↔ ∀ L, ∃ δ > 0, ∀ x ∈ D, x ≠ a → |x - a| < δ → L < f x := HasLimAt.def_top'

/-- **Th. 4.3.** Cauchy's (epsilon-delta) definition is equivalent (finite-`⊥` case). -/
lemma HasLimAt.def_bot {f : ℝ → ℝ} {D : Set ℝ} {a : ℝ} :
    HasLimAt f D a ⊥ ↔ ∀ L, ∃ δ > 0, ∀ x ∈ D, x ≠ a → |x - a| < δ → f x < L := HasLimAt.def_bot'

/-- **Th. 4.3.** Cauchy's (epsilon-delta) definition is equivalent (`⊤`-finite case). -/
lemma HasLimAt.def_at_top {f : ℝ → ℝ} {D : Set ℝ} {g : ℝ} :
    HasLimAt f D ⊤ g ↔ ∀ ε > 0, ∃ G, ∀ x ∈ D, G < x → |f x - g| < ε := HasLimAt.def'

/-- **Th. 4.3.** Cauchy's (epsilon-delta) definition is equivalent (`⊥`-finite case). -/
lemma HasLimAt.def_at_bot {f : ℝ → ℝ} {D : Set ℝ} {g : ℝ} :
    HasLimAt f D ⊥ g ↔ ∀ ε > 0, ∃ G, ∀ x ∈ D, x < G → |f x - g| < ε := HasLimAt.def'

/-- **Th. 4.3.** Cauchy's (epsilon-delta) definition is equivalent (`⊤`-`⊤` case). -/
lemma HasLimAt.def_top_top {f : ℝ → ℝ} {D : Set ℝ} :
    HasLimAt f D ⊤ ⊤ ↔ ∀ L, ∃ G, ∀ x ∈ D, G < x → L < f x := HasLimAt.def_top'

/-- **Th. 4.3.** Cauchy's (epsilon-delta) definition is equivalent (`⊥`-`⊤` case). -/
lemma HasLimAt.def_bot_top {f : ℝ → ℝ} {D : Set ℝ} :
    HasLimAt f D ⊥ ⊤ ↔ ∀ L, ∃ G, ∀ x ∈ D, x < G → L < f x := HasLimAt.def_top'

/-- **Th. 4.3.** Cauchy's (epsilon-delta) definition is equivalent (`⊤`-`⊥` case). -/
lemma HasLimAt.def_top_bot {f : ℝ → ℝ} {D : Set ℝ} :
    HasLimAt f D ⊤ ⊥ ↔ ∀ L, ∃ G, ∀ x ∈ D, G < x → f x < L := HasLimAt.def_bot'

/-- **Th. 4.3.** Cauchy's (epsilon-delta) definition is equivalent (`⊥`-`⊥` case). -/
lemma HasLimAt.def_bot_bot {f : ℝ → ℝ} {D : Set ℝ} :
    HasLimAt f D ⊥ ⊥ ↔ ∀ L, ∃ G, ∀ x ∈ D, x < G → f x < L := HasLimAt.def_bot'

lemma HasLimAt.of_eq {f h : ℝ → ℝ} {D : Set ℝ} {a g : EReal}
    (heq : ∀ x ∈ D, ↑x ≠ a → f x = h x) (hh : HasLimAt h D a g) : HasLimAt f D a g :=
  fun x hx ha => HasLim'.of_eq (fun n => heq (x n) (hx n).left (hx n).right) (hh x hx ha)

lemma HasLimAt.subset {f : ℝ → ℝ} {d D : Set ℝ} {a g : EReal} (hd : d ⊆ D) :
    HasLimAt f D a g → HasLimAt f d a g :=
  fun h x hx => h x fun n => ⟨Set.mem_of_subset_of_mem hd (hx n).1, (hx n).2⟩

lemma HasLimAt.of_eventually_eq {f h : ℝ → ℝ} {D : Set ℝ} {a g : EReal}
    (heq : Eventually D a fun x => f x = h x) (hh : HasLimAt h D a g) : HasLimAt f D a g := by
  simp [eventually_iff_hasLim] at heq
  peel 3 hh with x hx ha hh
  exact hh.of_eventually_eq (heq x hx ha)

lemma hasLimAt_id {D : Set ℝ} (a : EReal) : HasLimAt (fun x => x) D a a := fun _ _ => id

lemma hasLimAt_const {D : Set ℝ} (a : EReal) (c : ℝ) : HasLimAt (fun _ => c) D a c :=
  fun _ _ _ => HasLim.const c

/-- **Th. 4.4.** Squeeze theorem for functions. -/
lemma HasLimAt.squeeze {f p h : ℝ → ℝ} {D : Set ℝ} {a : EReal} {g : ℝ}
    (hfp : Eventually D a fun x => f x ≤ p x) (hph : Eventually D a fun x => p x ≤ h x)
    (hf : HasLimAt f D a g) (hh : HasLimAt h D a g) : HasLimAt p D a g := by
  intro x hx ha
  apply HasLim.squeeze (a := f ∘ x) (c := h ∘ x)
  · simp [eventually_iff_hasLim] at hfp
    exact hfp x hx ha
  · simp [eventually_iff_hasLim] at hph
    exact hph x hx ha
  · exact hf x hx ha
  · exact hh x hx ha

lemma HasLimAt.squeeze_const {f h : ℝ → ℝ} {D : Set ℝ} {a : EReal} {g : ℝ}
    (hfh : Eventually D a fun x => f x ≤ h x) (hhg : Eventually D a fun x => h x ≤ g)
    (hf : HasLimAt f D a g) : HasLimAt h D a g := HasLimAt.squeeze hfh hhg hf (hasLimAt_const _ _)

lemma HasLimAt.const_squeeze {f h : ℝ → ℝ} {D : Set ℝ} {a : EReal} {g : ℝ}
    (hgf : Eventually D a fun x => g ≤ f x) (hfh : Eventually D a fun x => f x ≤ h x)
    (hh : HasLimAt h D a g) : HasLimAt f D a g := HasLimAt.squeeze hgf hfh (hasLimAt_const _ _) hh

/-- **Th. 4.5.** Squeeze theorem for functions diverging to `⊤`. -/
lemma HasLimAt.squeeze_top {f h : ℝ → ℝ} {D : Set ℝ} {a : EReal}
    (hfh : Eventually D a fun x => f x ≤ h x) (hf : HasLimAt f D a ⊤) : HasLimAt h D a ⊤ := by
  intro x hx ha; apply HasLim'.squeeze_top (a := f ∘ x)
  · simp [eventually_iff_hasLim] at hfh
    exact hfh x hx ha
  · exact hf x hx ha

/-- **Th. 4.5.** Squeeze theorem for functions diverging to `⊥`. -/
lemma HasLimAt.bot_squeeze {f h : ℝ → ℝ} {D : Set ℝ} {a : EReal}
    (hfh : Eventually D a fun x => f x ≤ h x) (hh : HasLimAt h D a ⊥) : HasLimAt f D a ⊥ := by
  intro x hx ha; apply HasLim'.bot_squeeze (b := h ∘ x)
  · simp [eventually_iff_hasLim] at hfh
    exact hfh x hx ha
  · exact hh x hx ha

lemma HasLimAt.add {f h : ℝ → ℝ} {D : Set ℝ} {a g₁ g₂ : EReal} (hf : HasLimAt f D a g₁)
    (hh : HasLimAt h D a g₂) (hn : ¬(g₁ = ⊤ ∧ g₂ = ⊥) ∧ ¬(g₁ = ⊥ ∧ g₂ = ⊤) := by simp [*]) :
    HasLimAt (fun x => f x + h x) D a (g₁ + g₂) := fun x hx ha => (hf x hx ha).add (hh x hx ha)

lemma HasLimAt.add_const {f : ℝ → ℝ} {D : Set ℝ} {a g : EReal} (r : ℝ) (h : HasLimAt f D a g) :
    HasLimAt (fun x => f x + r) D a (g + r) := fun x hx ha => (h x hx ha).add_const r

lemma HasLimAt.const_add {f : ℝ → ℝ} {D : Set ℝ} {a g : EReal} (r : ℝ) (h : HasLimAt f D a g) :
    HasLimAt (fun x => r + f x) D a (r + g) := fun x hx ha => (h x hx ha).const_add r

lemma HasLimAt.neg {f : ℝ → ℝ} {D : Set ℝ} {a g : EReal}
    (h : HasLimAt f D a g) : HasLimAt (fun x => -f x) D a ↑(-g) := fun x hx ha => (h x hx ha).neg

lemma HasLimAt.sub {f h : ℝ → ℝ} {D : Set ℝ} {a g₁ g₂ : EReal} (hf : HasLimAt f D a g₁)
    (hh : HasLimAt h D a g₂) (hn : ¬(g₁ = ⊤ ∧ g₂ = ⊤) ∧ ¬(g₁ = ⊥ ∧ g₂ = ⊥) := by simp [*]) :
    HasLimAt (fun x => f x - h x) D a (g₁ - g₂) := fun x hx ha => (hf x hx ha).sub (hh x hx ha)

lemma HasLimAt.sub_const {f : ℝ → ℝ} {D : Set ℝ} {a g : EReal} (r : ℝ) (h : HasLimAt f D a g) :
    HasLimAt (fun x => f x - r) D a (g - r) := fun x hx ha => (h x hx ha).sub_const r

lemma HasLimAt.const_sub {f : ℝ → ℝ} {D : Set ℝ} {a g : EReal} (r : ℝ) (h : HasLimAt f D a g) :
    HasLimAt (fun x => r - f x) D a (r - g) := fun x hx ha => (h x hx ha).const_sub r

lemma HasLimAt.mul {f h : ℝ → ℝ} {D : Set ℝ} {a g₁ g₂ : EReal} (hf : HasLimAt f D a g₁)
    (hh : HasLimAt h D a g₂) (hn : ¬(g₁ = ⊤ ∧ g₂ = 0) ∧ ¬(g₁ = ⊥ ∧ g₂ = 0)
      ∧ ¬(g₁ = 0 ∧ g₂ = ⊤) ∧ ¬(g₁ = 0 ∧ g₂ = ⊥) := by simp [*] <;> order) :
    HasLimAt (fun x => f x * h x) D a (g₁ * g₂) := fun x hx ha => (hf x hx ha).mul (hh x hx ha)

lemma HasLimAt.mul_const {f : ℝ → ℝ} {D : Set ℝ} {a g : EReal} (r : ℝ) (h : HasLimAt f D a g)
    (hr : r ≠ 0 := by simp [*]) : HasLimAt (fun x => f x * r) D a (g * r) := h.mul (hasLimAt_const a r)

lemma HasLimAt.const_mul {f : ℝ → ℝ} {D : Set ℝ} {a g : EReal} (r : ℝ) (h : HasLimAt f D a g)
    (hr : r ≠ 0 := by simp [*]) : HasLimAt (fun x => r * f x) D a (r * g) := (hasLimAt_const a r).mul h

lemma HasLimAt.inv {f : ℝ → ℝ} {D : Set ℝ} {a g : EReal} (h : HasLimAt f D a g)
    (hg : g ≠ 0 := by simp [*]) : HasLimAt (fun x => (f x)⁻¹) D a ↑g⁻¹ :=
  fun x hx ha => (h x hx ha).inv hg

lemma HasLimAt.inv_zero_pos {f : ℝ → ℝ} {D : Set ℝ} {a : EReal} (hpos : Eventually D a fun x => 0 < f x)
    (h : HasLimAt f D a 0) : HasLimAt (fun x => (f x)⁻¹) D a ⊤ := by
  simp [eventually_iff_hasLim] at hpos
  peel 3 hpos with x hx ha hpos
  intro L
  specialize h x hx ha (max L 1)⁻¹ (by positivity)
  peel exists_forall_ge_and h hpos; replace ⟨h, hpos⟩ := this
  simp [abs_of_pos hpos] at h
  exact (lt_inv_of_lt_inv₀ hpos h).trans_le' (le_max_left L 1)

lemma HasLimAt.inv_zero_neg {f : ℝ → ℝ} {D : Set ℝ} {a : EReal} (hneg : Eventually D a fun x => f x < 0)
    (h : HasLimAt f D a 0) : HasLimAt (fun x => (f x)⁻¹) D a ⊥ := by
  apply neg at h
  simp at h
  convert (h.inv_zero_pos (by simpa)).neg using 2
  simp

lemma HasLimAt.div {f h : ℝ → ℝ} {D : Set ℝ} {a g₁ g₂ : EReal} (hf : HasLimAt f D a g₁)
    (hh : HasLimAt h D a g₂) (hg : g₂ ≠ 0 := by simp [*])
    (hn : (g₁ ≠ ⊤ ∧ g₁ ≠ ⊥) ∨ (g₂ ≠ ⊤ ∧ g₂ ≠ ⊥) := by simp [*]) :
    HasLimAt (fun x => f x / h x) D a (g₁ / g₂) :=
  fun x hx ha => (hf x hx ha).div (hh x hx ha) hg

lemma HasLimAt.div_const {f : ℝ → ℝ} {D : Set ℝ} {a g : EReal} {r : ℝ} (h : HasLimAt f D a g)
    (hr : r ≠ 0 := by simp [*]) : HasLimAt (fun x => f x / r) D a (g / r) := h.div (hasLimAt_const a r)

lemma HasLimAt.const_div {f : ℝ → ℝ} {D : Set ℝ} {a g : EReal} (r : ℝ) (h : HasLimAt f D a g)
    (hg : g ≠ 0 := by simp [*]) : HasLimAt (fun x => r / f x) D a (r / g) := (hasLimAt_const a r).div h

lemma HasLimAt.pow_const {f : ℝ → ℝ} {D : Set ℝ} {a g : EReal} (n : ℕ) (h : HasLimAt f D a g) :
    HasLimAt (fun x => (f x) ^ n) D a (g ^ n) :=
  fun x hx ha => (h x hx ha).pow_const n

lemma HasLimAt.rpow_const {f : ℝ → ℝ} {D : Set ℝ} {a : EReal} {g : ℝ} (r : ℝ) (h : HasLimAt f D a g)
    (hgr : g ≠ 0 ∨ 0 ≤ r := by simp [*]) : HasLimAt (fun x => (f x) ^ r) D a (g ^ r : ℝ) :=
  fun x hx ha => HasLim.rpow_const (h x hx ha) hgr

abbrev HasLeftLim (f : ℝ → ℝ) (D : Set ℝ := Set.univ) (a : ℝ) (g : EReal) :=
  HasLimAt f (D ∩ Set.Iio a) a g

abbrev HasRightLim (f : ℝ → ℝ) (D : Set ℝ := Set.univ) (a : ℝ) (g : EReal) :=
  HasLimAt f (D ∩ Set.Ioi a) a g

lemma eventually_left_iff_hasLim {D : Set ℝ} {a : ℝ} {p : ℝ → Prop} :
    Eventually (D ∩ Set.Iio a) a p ↔ ∃ δ > 0, ∀ x ∈ D, x < a → a - x < δ → p x := by
  simp
  peel with d hd x hx hu
  exact ⟨fun h hl => h hu.ne (abs_sub_lt_iff.mpr ⟨by linarith, hl⟩),
    fun h hne hl => h (lt_of_abs_lt (abs_sub_comm a x ▸ hl))⟩

lemma eventually_right_iff_hasLim {D : Set ℝ} {a : ℝ} {p : ℝ → Prop} :
    Eventually (D ∩ Set.Ioi a) a p ↔ ∃ δ > 0, ∀ x ∈ D, a < x → x - a < δ → p x := by
  simp
  peel with d hd x hx hl
  exact ⟨fun h hu => h hl.ne' (abs_sub_lt_iff.mpr ⟨hu, by linarith⟩),
    fun h hne hu => h (lt_of_abs_lt (abs_sub_comm a x ▸ hu))⟩

/-- **Th. 5.1.** Cauchy's epsilon-delta definition for a finite left limit -/
lemma HasLeftLim.def {f : ℝ → ℝ} {D : Set ℝ} {a g : ℝ} :
    HasLeftLim f D a g ↔ ∀ ε > 0, ∃ δ > 0, ∀ x ∈ D, x < a → a - x < δ → |f x - g| < ε := by
  simp only [HasLimAt.def', eventually_left_iff_hasLim]

/-- **Th. 5.1.** Cauchy's epsilon-delta definition for a `⊤` left limit -/
lemma HasLeftLim.def_top {f : ℝ → ℝ} {D : Set ℝ} {a : ℝ} :
    HasLeftLim f D a ⊤ ↔ ∀ L, ∃ δ > 0, ∀ x ∈ D, x < a → a - x < δ → L < f x := by
  simp only [HasLimAt.def_top', eventually_left_iff_hasLim]

/-- **Th. 5.1.** Cauchy's epsilon-delta definition for a `⊥` left limit -/
lemma HasLeftLim.def_bot {f : ℝ → ℝ} {D : Set ℝ} {a : ℝ} :
    HasLeftLim f D a ⊥ ↔ ∀ L, ∃ δ > 0, ∀ x ∈ D, x < a → a - x < δ → f x < L := by
  simp only [HasLimAt.def_bot', eventually_left_iff_hasLim]

/-- **Th. 5.1.** Cauchy's epsilon-delta definition for a finite right limit -/
lemma HasRightLim.def {f : ℝ → ℝ} {D : Set ℝ} {a g : ℝ} :
    HasRightLim f D a g ↔ ∀ ε > 0, ∃ δ > 0, ∀ x ∈ D, a < x → x - a < δ → |f x - g| < ε := by
  simp only [HasLimAt.def', eventually_right_iff_hasLim]

/-- **Th. 5.1.** Cauchy's epsilon-delta definition for a `⊤` right limit -/
lemma HasRightLim.def_top {f : ℝ → ℝ} {D : Set ℝ} {a : ℝ} :
    HasRightLim f D a ⊤ ↔ ∀ L, ∃ δ > 0, ∀ x ∈ D, a < x → x - a < δ → L < f x := by
  simp only [HasLimAt.def_top', eventually_right_iff_hasLim]

/-- **Th. 5.1.** Cauchy's epsilon-delta definition for a `⊥` right limit -/
lemma HasRightLim.def_bot {f : ℝ → ℝ} {D : Set ℝ} {a : ℝ} :
    HasRightLim f D a ⊥ ↔ ∀ L, ∃ δ > 0, ∀ x ∈ D, a < x → x - a < δ → f x < L := by
  simp only [HasLimAt.def_bot', eventually_right_iff_hasLim]

/-- **Th. 5.3.** A limit exists iff the left and right limits agree. -/
lemma hasLimAt_iff_left_and_right {f : ℝ → ℝ} {D : Set ℝ} {a : ℝ}
    {g : EReal} : HasLimAt f D a g ↔ HasLeftLim f D a g ∧ HasRightLim f D a g := by
  use fun h => ⟨h.subset Set.inter_subset_left, h.subset Set.inter_subset_left⟩
  cases g <;>
  · simp only [HasLeftLim, HasRightLim, HasLimAt.def_bot, HasLimAt.def, HasLimAt.def_top,
      Set.mem_inter_iff, Set.mem_Iio, Set.mem_Ioi, ← forall_and]
    intro h; peel h
    obtain ⟨⟨dl, hdl, hl⟩, ⟨dr, hdr, hr⟩⟩ := this
    exists min dl dr, lt_min hdl hdr
    intro x hx hne hd
    rcases lt_or_gt_of_ne hne with h | h
    · exact hl x ⟨hx, h⟩ hne (lt_min_iff.mp hd).left
    · exact hr x ⟨hx, h⟩ hne (lt_min_iff.mp hd).right

/-- **Th. 5.3.** Limit doesn't exist if the left and right limits disagree. -/
lemma not_hasLimAt_of_left_ne_right {f : ℝ → ℝ} {D : Set ℝ} {a : ℝ} {g₁ g₂ : EReal}
    (hal : (D ∩ Set.Iio a).AccPt a) (har : (D ∩ Set.Ioi a).AccPt a)
    (hl : HasLeftLim f D a g₁) (hr : HasRightLim f D a g₂) : g₁ ≠ g₂ → ¬∃ g, HasLimAt f D a g := by
  contrapose
  simp [hasLimAt_iff_left_and_right (D := D)]
  exact fun g hl' hr' => (hl.eq hal hl').trans (hr'.eq har hr)

/-- Effectively the same statement as `HasLimAt.comp_continuousWithinAt` -/
lemma HasLimAt.comp {f h : ℝ → ℝ} {D₁ D₂ : Set ℝ} (hd : ∀ x ∈ D₁, f x ∈ D₂) {a : EReal}
    {g : ℝ} : HasLimAt f D₁ a g → HasLimAt h D₂ g (h g) → HasLimAt (h ∘ f) D₁ a (h g) := by
  intro hf hh x hx ha e he
  replace ⟨d, h_d, hh⟩ := def.mp hh e he
  peel hf x hx ha d h_d with _ n _ hf
  by_cases! f (x n) = g
  case pos heq => simpa [heq]
  case neg hne => exact hh _ (hd (x n) (hx n).left) hne hf

lemma HasLimAt.comp_top {f h : ℝ → ℝ} {D₁ D₂ : Set ℝ} (hd : ∀ x ∈ D₁, f x ∈ D₂) {a : EReal}
    {g : ℝ} : HasLimAt f D₁ a ⊤ → HasLimAt h D₂ ⊤ g → HasLimAt (h ∘ f) D₁ a g :=
  fun hf hh x hx ha => hh (f ∘ x) (by simp; intro n; exact hd (x n) (hx n).left) (hf x hx ha)

lemma HasLimAt.comp_bot {f h : ℝ → ℝ} {D₁ D₂ : Set ℝ} (hd : ∀ x ∈ D₁, f x ∈ D₂) {a : EReal}
    {g : ℝ} : HasLimAt f D₁ a ⊥ → HasLimAt h D₂ ⊥ g → HasLimAt (h ∘ f) D₁ a g :=
  fun hf hh x hx ha => hh (f ∘ x) (by simp; intro n; exact hd (x n) (hx n).left) (hf x hx ha)

lemma HasLimAt.comp_neg {f : ℝ → ℝ} {D : Set ℝ} {a g : EReal} :
    HasLimAt f D a g ↔ HasLimAt (fun x => f (-x)) (-D) (-a) g := by
  revert f D a; suffices ∀ f D a, HasLimAt f D a g → HasLimAt (fun x => f (-x)) (-D) (-a) g by
    intro f D a; use this f D a; convert this (fun x => f (-x)) (-D) (-a) <;> simp
  intro f D a hf x hx ha
  exact hf (fun n => -x n) (by simp [← neg_eq_iff_eq_neg] at hx; exact hx)
    (by convert ha.neg; simp)

lemma eventually_def {D : Set ℝ} {a : ℝ} {p : ℝ → Prop} :
    Eventually D a p ↔ ∀ᶠ x in (nhdsWithin a (D \ {a})), p x := by
  simp [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff, Real.dist_eq]; peel 3; tauto

lemma eventually_bot_def {D : Set ℝ} {p : ℝ → Prop} :
    Eventually D ⊥ p ↔ ∀ᶠ x in (Filter.atBot ⊓ Filter.principal D), p x := by
  simp [Eventually, Filter.eventually_inf_principal, Filter.atBot_basis_Iio.eventually_iff]; peel 2; tauto

lemma eventually_top_def {D : Set ℝ} {p : ℝ → Prop} :
    Eventually D ⊤ p ↔ ∀ᶠ x in (Filter.atTop ⊓ Filter.principal D), p x := by
  simp [Eventually, Filter.eventually_inf_principal, Filter.atTop_basis_Ioi.eventually_iff]; peel 2; tauto

lemma eventually_left_def {D : Set ℝ} {a : ℝ} {p : ℝ → Prop} :
    Eventually (D ∩ Set.Iio a) a p ↔ ∀ᶠ x in (nhdsWithin a (D ∩ Set.Iio a)), p x := by
  simp [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff, Real.dist_eq]; grind

lemma eventually_right_def {D : Set ℝ} {a : ℝ} {p : ℝ → Prop} :
    Eventually (D ∩ Set.Ioi a) a p ↔ ∀ᶠ x in (nhdsWithin a (D ∩ Set.Ioi a)), p x := by
  simp [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff, Real.dist_eq]; grind

/-- `HasLimAt` agrees with Mathlib's `Tendsto` on the reals. -/
lemma hasLimAt_iff_tendsto {f : ℝ → ℝ} {D : Set ℝ} {a g : ℝ} :
    HasLimAt f D a g ↔ Filter.Tendsto f (nhdsWithin a (D \ {a})) (nhds g) := by
  simp [HasLimAt.def, Metric.tendsto_nhdsWithin_nhds, Real.dist_eq]

lemma hasLimAt_top_iff_tendsto {f : ℝ → ℝ} {D : Set ℝ} {a : ℝ} :
    HasLimAt f D a ⊤ ↔ Filter.Tendsto f (nhdsWithin a (D \ {a})) Filter.atTop := by
  simp [HasLimAt.def_top, (nhdsWithin_hasBasis (nhds_basis_abs_sub_lt a) _).tendsto_iff Filter.atTop_basis_Ioi]
  peel with L d hd x; tauto

lemma hasLimAt_bot_iff_tendsto {f : ℝ → ℝ} {D : Set ℝ} {a : ℝ} :
    HasLimAt f D a ⊥ ↔ Filter.Tendsto f (nhdsWithin a (D \ {a})) Filter.atBot := by
  simp [HasLimAt.def_bot, (nhdsWithin_hasBasis (nhds_basis_abs_sub_lt a) _).tendsto_iff Filter.atBot_basis_Iio]
  peel with L d hd x; tauto

lemma hasLimAt_at_top_iff_tendsto {f : ℝ → ℝ} {D : Set ℝ} {g : ℝ} :
    HasLimAt f D ⊤ g ↔ Filter.Tendsto f (Filter.atTop ⊓ Filter.principal D) (nhds g) := by
  simp [HasLimAt.def_at_top, (Filter.atTop_basis_Ioi.inf_principal D).tendsto_iff (nhds_basis_abs_sub_lt g)]
  peel with e he G x; tauto

lemma hasLimAt_at_bot_iff_tendsto {f : ℝ → ℝ} {D : Set ℝ} {g : ℝ} :
    HasLimAt f D ⊥ g ↔ Filter.Tendsto f (Filter.atBot ⊓ Filter.principal D) (nhds g) := by
  simp [HasLimAt.def_at_bot, (Filter.atBot_basis_Iio.inf_principal D).tendsto_iff (nhds_basis_abs_sub_lt g)]
  peel with e he G x; tauto

lemma hasLimAt_top_top_iff_tendsto {f : ℝ → ℝ} {D : Set ℝ} :
    HasLimAt f D ⊤ ⊤ ↔ Filter.Tendsto f (Filter.atTop ⊓ Filter.principal D) Filter.atTop := by
  simp [HasLimAt.def_top_top, (Filter.atTop_basis_Ioi.inf_principal D).tendsto_iff Filter.atTop_basis_Ioi]
  peel with L G x; tauto

lemma hasLimAt_top_bot_iff_tendsto {f : ℝ → ℝ} {D : Set ℝ} :
    HasLimAt f D ⊤ ⊥ ↔ Filter.Tendsto f (Filter.atTop ⊓ Filter.principal D) Filter.atBot := by
  simp [HasLimAt.def_top_bot, (Filter.atTop_basis_Ioi.inf_principal D).tendsto_iff Filter.atBot_basis_Iio]
  peel with L G x; tauto

lemma hasLimAt_bot_top_iff_tendsto {f : ℝ → ℝ} {D : Set ℝ} :
    HasLimAt f D ⊥ ⊤ ↔ Filter.Tendsto f (Filter.atBot ⊓ Filter.principal D) Filter.atTop := by
  simp [HasLimAt.def_bot_top, (Filter.atBot_basis_Iio.inf_principal D).tendsto_iff Filter.atTop_basis_Ioi]
  peel with L G x; tauto

lemma hasLimAt_bot_bot_iff_tendsto {f : ℝ → ℝ} {D : Set ℝ} :
    HasLimAt f D ⊥ ⊥ ↔ Filter.Tendsto f (Filter.atBot ⊓ Filter.principal D) Filter.atBot := by
  simp [HasLimAt.def_bot_bot, (Filter.atBot_basis_Iio.inf_principal D).tendsto_iff Filter.atBot_basis_Iio]
  peel with L G x; tauto
