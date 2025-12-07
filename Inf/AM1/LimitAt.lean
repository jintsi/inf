import Inf.AM1.Limit
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-! # Lectures 4 & 5

Again - not using `Filter.Tendsto`, instead introducing `HasLimAt`.

Definitions:

- `Set.AccPt D a` - `a` is an accumulation point of `D` (not using regular `AccPt` because filters)

- `HasLimAt f a g` - `f` has a limit `g` at point `a` (both `g` and `a` may be `⊤` or `⊥`)

- `HasLimAt f D a g` - an optional parameter for specifying `f`'s domain (by default, `Set.univ`)

- `HasLeftLim f (D) a g` and `HasRightLim f (D) a g`

Note the limit definitions don't check nor require that the point is in / an accumulation point of
the domain (it needs to be shown separately if of interest) - if it's not, they're all vacuously true,

...wait, i just realised how these parameters look like-
-/

variable [Field R] [LinearOrder R] [Field S] [LinearOrder S]

def Set.AccPt (D : Set R) (a : WithBot (WithTop R)) :=
    ∃ x : ℕ → R, (∀ n, x n ∈ D ∧ some (some (x n)) ≠ a) ∧ HasLim' x a

@[simp]
lemma Set.accPt_univ [IsOrderedRing R] [FloorSemiring R] {a : WithBot (WithTop R)} : Set.AccPt Set.univ a := by
  rcases a with _ | _ | a
  · exists fun n => -n; simp; exact HasLim'.id.neg_top
  · exists (↑); simp; exact HasLim'.id
  exists fun n => a + 1 / (n + 1); simp [HasLim']; and_intros
  · intro n; positivity
  convert (HasLim'.id.top_add (HasLim.const 1).bddBelow).inv_top.const_add a; simp

lemma Set.accPt_subset {d D : Set R} {a : WithBot (WithTop R)} (hss: d ⊆ D) (ha : d.AccPt a) : D.AccPt a := by
  replace ⟨x, hx, ha⟩ := ha; exists x; and_intros; intro n; and_intros
  · grw [← hss]; exact (hx n).1
  · exact (hx n).2
  · exact ha

@[simp]
lemma Set.accPt_Ioo_left [IsStrictOrderedRing R] [FloorSemiring R] {a b : R} (h : a < b) : (Set.Ioo a b).AccPt a := by
  exists fun n => a + (b - a) / (n + 2); and_intros; intro n; and_intros
  · simp; apply div_pos; simpa; positivity
  · simp; apply add_lt_of_lt_sub_left; apply div_lt_self; simpa; linarith
  · simp [WithBot.some, WithTop.some, sub_eq_zero]; exact ⟨ne_of_gt h, by positivity⟩
  · simp [HasLim']
    convert ((HasLim'.id.top_add (HasLim.const 2).bddBelow).inv_top.const_mul (b - a)).const_add a using 3
    · simp [div_eq_mul_inv]
    · simp

@[simp]
lemma Set.accPt_Ioo_right [IsStrictOrderedRing R] [FloorSemiring R] {a b : R} (h : a < b) : (Set.Ioo a b).AccPt b := by
  exists fun n => b - (b - a) / (n + 2); and_intros; intro n; and_intros
  · simp; rw [lt_sub_comm]; apply div_lt_self; simpa; linarith
  · simp; apply div_pos; simpa; positivity
  · simp [WithBot.some, WithTop.some, sub_eq_zero]; exact ⟨ne_of_gt h, by positivity⟩
  · simp [HasLim']
    convert ((HasLim'.id.top_add (HasLim.const 2).bddBelow).inv_top.const_mul (b - a)).const_sub b using 3
    · simp [div_eq_mul_inv]
    · simp

/-- Limit of a function (Heine's definition). `g` is a the limit of `f` at `a` if the image
of any sequence converging to `a` converges to `g`.

`D` (the domain of `f`) is supposed to be an optional parameter defaulting to `Set.univ`,
but it tends to not work and `Set.univ` has to be written manually.

Literally Scunthorpian. -/
def HasLimAt (f : R → S) (D : Set R := Set.univ) (a : WithBot (WithTop R)) (g : WithBot (WithTop S)) :=
    ∀ x : ℕ → R, (∀ n, x n ∈ D ∧ some (some (x n)) ≠ a) → HasLim' x a → HasLim' (f ∘ x) g

/-- **Th. 4.1.** If a limit exists, it's unique. -/
lemma HasLimAt.eq [IsOrderedRing S] {f : R → S} {D : Set R} {a : WithBot (WithTop R)}
    {g₁ g₂ : WithBot (WithTop S)} (ha : D.AccPt a) : HasLimAt f D a g₁ → HasLimAt f D a g₂ → g₁ = g₂ := by
  replace ⟨x, hx, ha⟩ := ha; intro h1 h2; specialize h1 x hx ha; specialize h2 x hx ha
  apply le_antisymm
  · exact HasLim'.le ⟨0, fun _ _ => le_rfl⟩ h1 h2
  · exact HasLim'.le ⟨0, fun _ _ => le_rfl⟩ h2 h1

/-- **Th. 4.2.** Cauchy's (epsilon-delta) definition is equivalent (finite-finite case). -/
lemma HasLimAt.def [IsOrderedRing R] [FloorSemiring R] {f : R → S} {D : Set R} {a : R} {g : S} :
    HasLimAt f D a g ↔ ∀ ε > 0, ∃ δ > 0, ∀ x ∈ D, x ≠ a → |x - a| < δ → |f x - g| < ε := by
  constructor
  · intro h e he; by_contra!
    choose x hx1 hx2 hx3 hx4 using fun n : ℕ => this (n + 1)⁻¹ (by simp; linarith)
    have ha : HasLim x a := by
      intro e he; exists ⌈e⁻¹⌉₊; intro n hn
      grw [hx3]; apply inv_lt_of_inv_lt₀ he
      rw [ge_iff_le, Nat.ceil_le] at hn; linarith
    have h := h x ?_ ha
    case refine_1 => intro n; convert And.intro (hx1 n) (hx2 n); simp [WithBot.some, WithTop.some]
    revert h; simp [HasLim', HasLim]; exists e, he; intro n; exact ⟨n, le_rfl, hx4 n⟩
  · intro h x hx ha e he; replace ⟨d, hd, h⟩ := h e he; replace ⟨n, ha⟩ := ha d hd
    exists n; intro n hn; specialize hx n; specialize ha n hn
    simp [WithBot.some, WithTop.some] at hx
    exact h (x n) hx.1 hx.2 ha

/-- **Th. 4.3.** Cauchy's (epsilon-delta) definition is equivalent (finite-`⊤` case). -/
lemma HasLimAt.def_top' [IsOrderedRing R] [FloorSemiring R] {f : R → S} {D : Set R} {a : R} :
    HasLimAt f D a ⊤ ↔ ∀ L, ∃ δ > 0, ∀ x ∈ D, x ≠ a → |x - a| < δ → L < f x := by
  constructor
  · intro h L; by_contra!
    choose x hx1 hx2 hx3 hx4 using fun n : ℕ => this (n + 1)⁻¹ (by simp; linarith)
    have ha : HasLim x a := by
      intro e he; exists ⌈e⁻¹⌉₊; intro n hn
      grw [hx3]; apply inv_lt_of_inv_lt₀ he
      rw [ge_iff_le, Nat.ceil_le] at hn; linarith
    have h := h x ?_ ha
    case refine_1 => intro n; convert And.intro (hx1 n) (hx2 n); simp [WithBot.some, WithTop.some]
    revert h; simp [HasLim']; exists L; intro n; exact ⟨n, le_rfl, hx4 n⟩
  · intro h x hx ha D; replace ⟨d, hd, h⟩ := h D; replace ⟨n, ha⟩ := ha d hd
    exists n; intro n hn; specialize hx n; specialize ha n hn
    simp [WithBot.some, WithTop.some] at hx
    exact h (x n) hx.1 hx.2 ha

/-- **Th. 4.3.** Cauchy's (epsilon-delta) definition is equivalent (finite-`⊥` case). -/
lemma HasLimAt.def_bot' [IsOrderedRing R] [FloorSemiring R] {f : R → S} {D : Set R} {a : R} :
    HasLimAt f D a ⊥ ↔ ∀ L, ∃ δ > 0, ∀ x ∈ D, x ≠ a → |x - a| < δ → f x < L := by
  constructor
  · intro h L; by_contra!
    choose x hx1 hx2 hx3 hx4 using fun n : ℕ => this (n + 1)⁻¹ (by simp; linarith)
    have ha : HasLim x a := by
      intro e he; exists ⌈e⁻¹⌉₊; intro n hn
      grw [hx3]; apply inv_lt_of_inv_lt₀ he
      rw [ge_iff_le, Nat.ceil_le] at hn; linarith
    have h := h x ?_ ha
    case refine_1 => intro n; convert And.intro (hx1 n) (hx2 n); simp [WithBot.some, WithTop.some]
    revert h; simp [HasLim']; exists L; intro n; exact ⟨n, le_rfl, hx4 n⟩
  · intro h x hx ha D; replace ⟨d, hd, h⟩ := h D; replace ⟨n, ha⟩ := ha d hd
    exists n; intro n hn; specialize hx n; specialize ha n hn
    simp [WithBot.some, WithTop.some] at hx
    exact h (x n) hx.1 hx.2 ha

/-- **Th. 4.3.** Cauchy's (epsilon-delta) definition is equivalent (`⊤`-finite case). -/
lemma HasLimAt.def_top [IsOrderedRing R] [FloorSemiring R] {f : R → S} {D : Set R} {g : S} :
    HasLimAt f D ⊤ g ↔ ∀ ε > 0, ∃ G, ∀ x ∈ D, G < x → |f x - g| < ε := by
  constructor
  · intro h e he; by_contra!
    choose x hx1 hx3 hx4 using fun n : ℕ => this n
    have ht := HasLim'.squeeze_top ⟨0, fun n _ => (hx3 n).le⟩ HasLim'.id
    have h := h x (by simpa [Top.top, WithBot.some]) ht
    revert h; simp [HasLim', HasLim]; exists e, he; intro n; exact ⟨n, le_rfl, hx4 n⟩
  · intro h x hx ht e he; replace ⟨G, h⟩ := h e he; replace ⟨n, ht⟩ := ht G
    exists n; intro n hn; specialize hx n; specialize ht n hn
    simp [Top.top, WithBot.some] at hx
    exact h (x n) hx ht

/-- **Th. 4.3.** Cauchy's (epsilon-delta) definition is equivalent (`⊥`-finite case). -/
lemma HasLimAt.def_bot [IsOrderedRing R] [FloorSemiring R] {f : R → S} {D : Set R} {g : S} :
    HasLimAt f D ⊥ g ↔ ∀ ε > 0, ∃ G, ∀ x ∈ D, x < G → |f x - g| < ε := by
  constructor
  · intro h e he; by_contra!
    choose x hx1 hx3 hx4 using fun n : ℕ => this (-n)
    have hb := HasLim'.bot_squeeze ⟨0, fun n _ => (hx3 n).le⟩ HasLim'.id.neg_top
    have h := h x (by simpa) hb
    revert h; simp [HasLim', HasLim]; exists e, he; intro n; exact ⟨n, le_rfl, hx4 n⟩
  · intro h x hx hb e he; replace ⟨G, h⟩ := h e he; replace ⟨n, hb⟩ := hb G
    exists n; intro n hn; specialize hx n; specialize hb n hn
    simp at hx
    exact h (x n) hx hb

/-- **Th. 4.3.** Cauchy's (epsilon-delta) definition is equivalent (`⊤`-`⊤` case). -/
lemma HasLimAt.def_top_top [IsOrderedRing R] [FloorSemiring R] {f : R → S} {D : Set R} :
    HasLimAt f D ⊤ ⊤ ↔ ∀ L, ∃ G, ∀ x ∈ D, G < x → L < f x := by
  constructor
  · intro h L; by_contra!
    choose x hx1 hx3 hx4 using fun n : ℕ => this n
    have ht := HasLim'.squeeze_top ⟨0, fun n _ => (hx3 n).le⟩ HasLim'.id
    have h := h x (by simpa [Top.top, WithBot.some]) ht
    revert h; simp [HasLim']; exists L; intro n; exact ⟨n, le_rfl, hx4 n⟩
  · intro h x hx ht L; replace ⟨G, h⟩ := h L; replace ⟨n, ht⟩ := ht G
    exists n; intro n hn; specialize hx n; specialize ht n hn
    simp [Top.top, WithBot.some] at hx
    exact h (x n) hx ht

/-- **Th. 4.3.** Cauchy's (epsilon-delta) definition is equivalent (`⊥`-`⊤` case). -/
lemma HasLimAt.def_bot_top [IsOrderedRing R] [FloorSemiring R] {f : R → S} {D : Set R} :
    HasLimAt f D ⊥ ⊤ ↔ ∀ L, ∃ G, ∀ x ∈ D, x < G → L < f x := by
  constructor
  · intro h L; by_contra!
    choose x hx1 hx3 hx4 using fun n : ℕ => this (-n)
    have hb := HasLim'.bot_squeeze ⟨0, fun n _ => (hx3 n).le⟩ HasLim'.id.neg_top
    have h := h x (by simpa) hb
    revert h; simp [HasLim']; exists L; intro n; exact ⟨n, le_rfl, hx4 n⟩
  · intro h x hx hb L; replace ⟨G, h⟩ := h L; replace ⟨n, hb⟩ := hb G
    exists n; intro n hn; specialize hx n; specialize hb n hn
    simp at hx
    exact h (x n) hx hb

/-- **Th. 4.3.** Cauchy's (epsilon-delta) definition is equivalent (`⊤`-`⊥` case). -/
lemma HasLimAt.def_top_bot [IsOrderedRing R] [FloorSemiring R] {f : R → S} {D : Set R} :
    HasLimAt f D ⊤ ⊥ ↔ ∀ L, ∃ G, ∀ x ∈ D, G < x → f x < L := by
  constructor
  · intro h L; by_contra!
    choose x hx1 hx3 hx4 using fun n : ℕ => this n
    have ht := HasLim'.squeeze_top ⟨0, fun n _ => (hx3 n).le⟩ HasLim'.id
    have h := h x (by simpa [Top.top, WithBot.some]) ht
    revert h; simp [HasLim']; exists L; intro n; exact ⟨n, le_rfl, hx4 n⟩
  · intro h x hx ht L; replace ⟨G, h⟩ := h L; replace ⟨n, ht⟩ := ht G
    exists n; intro n hn; specialize hx n; specialize ht n hn
    simp [Top.top, WithBot.some] at hx
    exact h (x n) hx ht

/-- **Th. 4.3.** Cauchy's (epsilon-delta) definition is equivalent (`⊥`-`⊥` case). -/
lemma HasLimAt.def_bot_bot [IsOrderedRing R] [FloorSemiring R] {f : R → S} {D : Set R} :
    HasLimAt f D ⊥ ⊥ ↔ ∀ L, ∃ G, ∀ x ∈ D, x < G → f x < L := by
  constructor
  · intro h L; by_contra!
    choose x hx1 hx3 hx4 using fun n : ℕ => this (-n)
    have hb := HasLim'.bot_squeeze ⟨0, fun n _ => (hx3 n).le⟩ HasLim'.id.neg_top
    have h := h x (by simpa) hb
    revert h; simp [HasLim']; exists L; intro n; exact ⟨n, le_rfl, hx4 n⟩
  · intro h x hx hb L; replace ⟨G, h⟩ := h L; replace ⟨n, hb⟩ := hb G
    exists n; intro n hn; specialize hx n; specialize hb n hn
    simp at hx
    exact h (x n) hx hb

lemma HasLimAt.subset {f : R → S} {d D : Set R} {a : WithBot (WithTop R)} {g : WithBot (WithTop S)}
    (hd : d ⊆ D) : HasLimAt f D a g → HasLimAt f d a g :=
  fun h x hx => h x fun n => ⟨Set.mem_of_subset_of_mem hd (hx n).1, (hx n).2⟩

lemma hasLimAt_id {D : Set R} (a : WithBot (WithTop R)) : HasLimAt id D a a := fun _ _ => id

lemma hasLimAt_const [AddLeftMono S] {D : Set R} (a : WithBot (WithTop R)) (c : S) :
    HasLimAt (fun _ => c) D a c := fun _ _ _ => HasLim.const c

/-- **Th. 4.4.** Squeeze theorem for functions. -/
lemma HasLimAt.squeeze [IsOrderedRing S] {f p h : R → S} {D : Set R} {a : R} {g : S}
    (hfp : ∃ δ > 0, ∀ x ∈ D, x ≠ a → |x - a| < δ → f x ≤ p x) (hph : ∃ δ > 0, ∀ x ∈ D, x ≠ a → |x - a| < δ → p x ≤ h x)
    (hf : HasLimAt f D a g) (hh : HasLimAt h D a g) : HasLimAt p D a g := by
  intro x hx ha; apply HasLim.squeeze (a := f ∘ x) (c := h ∘ x)
  · replace ⟨d, hd, hfp⟩ := hfp; replace ⟨n, ha⟩ := ha d hd; simp [WithBot.some, WithTop.some] at hx
    exact ⟨n, fun n hn => hfp (x n) (hx n).1 (hx n).2 (ha n hn)⟩
  · replace ⟨d, hd, hph⟩ := hph; replace ⟨n, ha⟩ := ha d hd; simp [WithBot.some, WithTop.some] at hx
    exact ⟨n, fun n hn => hph (x n) (hx n).1 (hx n).2 (ha n hn)⟩
  · exact hf x hx ha
  · exact hh x hx ha

lemma HasLimAt.squeeze_at_top [IsOrderedRing S] {f p h : R → S} {D : Set R} {g : S}
    (hfp : ∃ G, ∀ x ∈ D, G < x → f x ≤ p x) (hph : ∃ G, ∀ x ∈ D, G < x → p x ≤ h x)
    (hf : HasLimAt f D ⊤ g) (hh : HasLimAt h D ⊤ g) : HasLimAt p D ⊤ g := by
  intro x hx ht; apply HasLim.squeeze (a := f ∘ x) (c := h ∘ x)
  · replace ⟨G, hfp⟩ := hfp; replace ⟨n, ht⟩ := ht G; exact ⟨n, fun n hn => hfp (x n) (hx n).1 (ht n hn)⟩
  · replace ⟨G, hph⟩ := hph; replace ⟨n, ht⟩ := ht G; exact ⟨n, fun n hn => hph (x n) (hx n).1 (ht n hn)⟩
  · exact hf x hx ht
  · exact hh x hx ht

lemma HasLimAt.squeeze_at_bot [IsOrderedRing S] {f p h : R → S} {D : Set R} {g : S}
    (hfp : ∃ G, ∀ x ∈ D, x < G → f x ≤ p x) (hph : ∃ G, ∀ x ∈ D, x < G → p x ≤ h x)
    (hf : HasLimAt f D ⊥ g) (hh : HasLimAt h D ⊥ g) : HasLimAt p D ⊥ g := by
  intro x hx hb; apply HasLim.squeeze (a := f ∘ x) (c := h ∘ x)
  · replace ⟨G, hfp⟩ := hfp; replace ⟨n, hb⟩ := hb G; exact ⟨n, fun n hn => hfp (x n) (hx n).1 (hb n hn)⟩
  · replace ⟨G, hph⟩ := hph; replace ⟨n, hb⟩ := hb G; exact ⟨n, fun n hn => hph (x n) (hx n).1 (hb n hn)⟩
  · exact hf x hx hb
  · exact hh x hx hb

lemma HasLimAt.squeeze_const [IsOrderedRing S] {f h : R → S} {D : Set R} {a : R} {g : S}
    (hfh : ∃ δ > 0, ∀ x ∈ D, x ≠ a → |x - a| < δ → f x ≤ h x) (hhg : ∃ δ > 0, ∀ x ∈ D, x ≠ a → |x - a| < δ → h x ≤ g)
    (hf : HasLimAt f D a g) : HasLimAt h D a g := HasLimAt.squeeze hfh hhg hf (hasLimAt_const _ _)

lemma HasLimAt.squeeze_const_at_top [IsOrderedRing S] {f h : R → S} {D : Set R} {g : S}
    (hfh : ∃ G, ∀ x ∈ D, G < x → f x ≤ h x) (hhg : ∃ G, ∀ x ∈ D, G < x → h x ≤ g)
    (hf : HasLimAt f D ⊤ g) : HasLimAt h D ⊤ g := HasLimAt.squeeze_at_top hfh hhg hf (hasLimAt_const _ _)

lemma HasLimAt.squeeze_const_at_bot [IsOrderedRing S] {f h : R → S} {D : Set R} {g : S}
    (hfh : ∃ G, ∀ x ∈ D, x < G → f x ≤ h x) (hhg : ∃ G, ∀ x ∈ D, x < G → h x ≤ g)
    (hf : HasLimAt f D ⊥ g) : HasLimAt h D ⊥ g := HasLimAt.squeeze_at_bot hfh hhg hf (hasLimAt_const _ _)

lemma HasLimAt.const_squeeze [IsOrderedRing S] {f h : R → S} {D : Set R} {a : R} {g : S}
    (hgf : ∃ δ > 0, ∀ x ∈ D, x ≠ a → |x - a| < δ → g ≤ f x) (hfh : ∃ δ > 0, ∀ x ∈ D, x ≠ a → |x - a| < δ → f x ≤ h x)
    (hh : HasLimAt h D a g) : HasLimAt f D a g := HasLimAt.squeeze hgf hfh (hasLimAt_const _ _) hh

lemma HasLimAt.const_squeeze_at_top [IsOrderedRing S] {f h : R → S} {D : Set R} {g : S}
    (hgf : ∃ G, ∀ x ∈ D, G < x → g ≤ f x) (hfh : ∃ G, ∀ x ∈ D, G < x → f x ≤ h x)
    (hh : HasLimAt h D ⊤ g) : HasLimAt f D ⊤ g := HasLimAt.squeeze_at_top hgf hfh (hasLimAt_const _ _) hh

lemma HasLimAt.const_squeeze_at_bot [IsOrderedRing S] {f h : R → S} {D : Set R} {g : S}
    (hgf : ∃ G, ∀ x ∈ D, x < G → g ≤ f x) (hfh : ∃ G, ∀ x ∈ D, x < G → f x ≤ h x)
    (hh : HasLimAt h D ⊥ g) : HasLimAt f D ⊥ g := HasLimAt.squeeze_at_bot hgf hfh (hasLimAt_const _ _) hh

/-- **Th. 4.5.** Squeeze theorem for functions diverging to `⊤`. -/
lemma HasLimAt.squeeze_top {f h : R → S} {D : Set R} {a : R}
    (hfh : ∃ δ > 0, ∀ x ∈ D, x ≠ a → |x - a| < δ → f x ≤ h x)
    (hf : HasLimAt f D a ⊤) : HasLimAt h D a ⊤ := by
  intro x hx ha; apply HasLim'.squeeze_top (a := f ∘ x)
  · replace ⟨d, hd, hfh⟩ := hfh; replace ⟨n, ha⟩ := ha d hd
    simp [WithBot.some, WithTop.some] at hx
    exact ⟨n, fun n hn => hfh (x n) (hx n).1 (hx n).2 (ha n hn)⟩
  · exact hf x hx ha

lemma HasLimAt.squeeze_top_at_top {f h : R → S} {D : Set R} (hfh : ∃ G, ∀ x ∈ D, G < x → f x ≤ h x)
    (hf : HasLimAt f D ⊤ ⊤) : HasLimAt h D ⊤ ⊤ := by
  intro x hx ht; apply HasLim'.squeeze_top (a := f ∘ x)
  · replace ⟨G, hfh⟩ := hfh; replace ⟨n, ht⟩ := ht G
    exact ⟨n, fun n hn => hfh (x n) (hx n).1 (ht n hn)⟩
  · exact hf x hx ht

lemma HasLimAt.squeeze_top_at_bot {f h : R → S} {D : Set R} (hfh : ∃ G, ∀ x ∈ D, x < G → f x ≤ h x)
    (hf : HasLimAt f D ⊥ ⊤) : HasLimAt h D ⊥ ⊤ := by
  intro x hx hb; apply HasLim'.squeeze_top (a := f ∘ x)
  · replace ⟨G, hfh⟩ := hfh; replace ⟨n, hb⟩ := hb G
    exact ⟨n, fun n hn => hfh (x n) (hx n).1 (hb n hn)⟩
  · exact hf x hx hb

/-- **Th. 4.5.** Squeeze theorem for functions diverging to `⊥`. -/
lemma HasLimAt.bot_squeeze {f h : R → S} {D : Set R} {a : R}
    (hfh : ∃ δ > 0, ∀ x ∈ D, x ≠ a → |x - a| < δ → f x ≤ h x)
    (hh : HasLimAt h D a ⊥) : HasLimAt f D a ⊥ := by
  intro x hx ha; apply HasLim'.bot_squeeze (b := h ∘ x)
  · replace ⟨d, hd, hfh⟩ := hfh; replace ⟨n, ha⟩ := ha d hd
    simp [WithBot.some, WithTop.some] at hx
    exact ⟨n, fun n hn => hfh (x n) (hx n).1 (hx n).2 (ha n hn)⟩
  · exact hh x hx ha

lemma HasLimAt.bot_squeeze_at_top {f h : R → S} {D : Set R} (hfh : ∃ G, ∀ x ∈ D, G < x → f x ≤ h x)
    (hh : HasLimAt h D ⊤ ⊥) : HasLimAt f D ⊤ ⊥ := by
  intro x hx ht; apply HasLim'.bot_squeeze (b := h ∘ x)
  · replace ⟨G, hfh⟩ := hfh; replace ⟨n, ht⟩ := ht G
    exact ⟨n, fun n hn => hfh (x n) (hx n).1 (ht n hn)⟩
  · exact hh x hx ht

lemma HasLimAt.bot_squeeze_at_bot {f h : R → S} {D : Set R} (hfh : ∃ G, ∀ x ∈ D, x < G → f x ≤ h x)
    (hh : HasLimAt h D ⊥ ⊥) : HasLimAt f D ⊥ ⊥ := by
  intro x hx hb; apply HasLim'.bot_squeeze (b := h ∘ x)
  · replace ⟨G, hfh⟩ := hfh; replace ⟨n, hb⟩ := hb G
    exact ⟨n, fun n hn => hfh (x n) (hx n).1 (hb n hn)⟩
  · exact hh x hx hb

lemma HasLimAt.add [IsOrderedRing S] {f h : R → S} {D : Set R} {a : WithBot (WithTop R)} {g₁ g₂ : WithBot (WithTop S)}
    (hf : HasLimAt f D a g₁) (hh : HasLimAt h D a g₂) (hn : ¬(g₁ = ⊤ ∧ g₂ = ⊥) ∧ ¬(g₁ = ⊥ ∧ g₂ = ⊤) := by decide) :
    HasLimAt (fun x => f x + h x) D a (g₁ + g₂) := fun x hx ha => (hf x hx ha).add (hh x hx ha) hn

lemma HasLimAt.add_const [AddRightStrictMono S] {f : R → S} {D : Set R} {a : WithBot (WithTop R)}
    {g : WithBot (WithTop S)} (r : S) (h : HasLimAt f D a g) : HasLimAt (fun x => f x + r) D a (g + r) := by
  intro x hx ha; specialize h x hx ha
  match g with
  | some (some g) => exact h.add_const r
  | ⊤ => intro D; replace ⟨n, h⟩ := h (D - r); exact ⟨n, fun n hn => lt_add_of_sub_right_lt (h n hn)⟩
  | ⊥ => intro D; replace ⟨n, h⟩ := h (D - r); exact ⟨n, fun n hn => add_lt_of_lt_sub_right (h n hn)⟩

lemma HasLimAt.const_add [AddRightStrictMono S] {f : R → S} {D : Set R} {a : WithBot (WithTop R)}
    {g : WithBot (WithTop S)} (r : S) (h : HasLimAt f D a g) : HasLimAt (fun x => r + f x) D a (r + g) := by
  convert h.add_const r using 1; ext; repeat apply add_comm

lemma HasLimAt.neg {f : R → S} {D : Set R} {a : WithBot (WithTop R)} {g : S}
    (h : HasLimAt f D a g) : HasLimAt (fun x => -f x) D a ↑(-g) := fun x hx ha => (h x hx ha).neg

lemma HasLimAt.neg_top [IsOrderedAddMonoid S] {f : R → S} {D : Set R} {a : WithBot (WithTop R)}
    (h : HasLimAt f D a ⊤) : HasLimAt (fun x => -f x) D a ⊥ := fun x hx ha => (h x hx ha).neg_top

lemma HasLimAt.neg_bot [IsOrderedAddMonoid S] {f : R → S} {D : Set R} {a : WithBot (WithTop R)}
    (h : HasLimAt f D a ⊥) : HasLimAt (fun x => -f x) D a ⊤ := fun x hx ha => (h x hx ha).neg_bot

lemma HasLimAt.sub [IsOrderedRing S] {f h : R → S} {D : Set R} {a : WithBot (WithTop R)} {g₁ g₂ : S}
    (hf : HasLimAt f D a g₁) (hh : HasLimAt h D a g₂) : HasLimAt (fun x => f x - h x) D a (g₁ - g₂) :=
  fun x hx ha => (hf x hx ha).sub (hh x hx ha)

lemma HasLimAt.sub_const [AddRightStrictMono S] {f : R → S} {D : Set R} {a : WithBot (WithTop R)}
    {g : WithBot (WithTop S)} (h : HasLimAt f D a g) (r : S) : HasLimAt (fun x => f x - r) D a (g + ↑(-r)) := by
  convert h.add_const (-r) using 2; apply sub_eq_add_neg

lemma HasLimAt.const_sub [AddRightStrictMono S] {f : R → S} {D : Set R} {a : WithBot (WithTop R)} {g : S}
    (r : S) (h : HasLimAt f D a g) : HasLimAt (fun x => r - f x) D a (r - g) := by
  convert h.neg.const_add r using 2; apply sub_eq_add_neg; norm_cast; apply sub_eq_add_neg

lemma HasLimAt.const_sub_top [IsOrderedAddMonoid S] {f : R → S} {D : Set R} {a : WithBot (WithTop R)}
    (r : S) (h : HasLimAt f D a ⊤) : HasLimAt (fun x => r - f x) D a ⊥ := by
  convert h.neg_top.const_add r using 2; apply sub_eq_add_neg

lemma HasLimAt.const_sub_bot [IsOrderedAddMonoid S] {f : R → S} {D : Set R} {a : WithBot (WithTop R)}
    (r : S) (h : HasLimAt f D a ⊥) : HasLimAt (fun x => r - f x) D a ⊤ := by
  convert h.neg_bot.const_add r using 2; apply sub_eq_add_neg

lemma HasLimAt.mul [IsOrderedRing S] {f h : R → S} {D : Set R} {a : WithBot (WithTop R)} {g₁ g₂ : S}
    (hf : HasLimAt f D a g₁) (hh : HasLimAt h D a g₂) : HasLimAt (fun x => f x * h x) D a (g₁ * g₂) :=
  fun x hx ha => (hf x hx ha).mul (hh x hx ha)

lemma HasLimAt.mul_const [IsOrderedRing S] {f : R → S} {D : Set R} {a : WithBot (WithTop R)} {g : S}
    (r : S) (h : HasLimAt f D a g) : HasLimAt (fun x => f x * r) D a (g * r) := h.mul (hasLimAt_const a r)

lemma HasLimAt.const_mul [IsOrderedRing S] {f : R → S} {D : Set R} {a : WithBot (WithTop R)} {g : S}
    (r : S) (h : HasLimAt f D a g) : HasLimAt (fun x => r * f x) D a (r * g) := (hasLimAt_const a r).mul h

lemma HasLimAt.top_mul_pos [IsOrderedRing S] {f h : R → S} {D : Set R} {a : WithBot (WithTop R)} {g : S}
    (hg : 0 < g) (hf : HasLimAt f D a ⊤) (hh : HasLimAt h D a g) : HasLimAt (fun x => f x * h x) D a ⊤ :=
  fun x hx ha => (hf x hx ha).top_mul_pos hg (hh x hx ha)

lemma HasLimAt.top_mul_neg [IsOrderedRing S] {f h : R → S} {D : Set R} {a : WithBot (WithTop R)} {g : S}
    (hg : g < 0) (hf : HasLimAt f D a ⊤) (hh : HasLimAt h D a g) : HasLimAt (fun x => f x * h x) D a ⊥ :=
  fun x hx ha => (hf x hx ha).top_mul_neg hg (hh x hx ha)

lemma HasLimAt.pos_mul_top [IsOrderedRing S] {f h : R → S} {D : Set R} {a : WithBot (WithTop R)} {g : S}
    (hg : 0 < g) (hf : HasLimAt f D a g) (hh : HasLimAt h D a ⊤) : HasLimAt (fun x => f x * h x) D a ⊤ :=
  fun x hx ha => (hh x hx ha).pos_mul_top hg (hf x hx ha)

lemma HasLimAt.neg_mul_top [IsOrderedRing S] {f h : R → S} {D : Set R} {a : WithBot (WithTop R)} {g : S}
    (hg : g < 0) (hf : HasLimAt f D a g) (hh : HasLimAt h D a ⊤) : HasLimAt (fun x => f x * h x) D a ⊥ :=
  fun x hx ha => (hh x hx ha).neg_mul_top hg (hf x hx ha)

lemma HasLimAt.bot_mul_pos [IsOrderedRing S] {f h : R → S} {D : Set R} {a : WithBot (WithTop R)} {g : S}
    (hg : 0 < g) (hf : HasLimAt f D a ⊥) (hh : HasLimAt h D a g) : HasLimAt (fun x => f x * h x) D a ⊥ :=
  fun x hx ha => (hf x hx ha).bot_mul_pos hg (hh x hx ha)

lemma HasLimAt.bot_mul_neg [IsOrderedRing S] {f h : R → S} {D : Set R} {a : WithBot (WithTop R)} {g : S}
    (hg : g < 0) (hf : HasLimAt f D a ⊥) (hh : HasLimAt h D a g) : HasLimAt (fun x => f x * h x) D a ⊤ :=
  fun x hx ha => (hf x hx ha).bot_mul_neg hg (hh x hx ha)

lemma HasLimAt.pos_mul_bot [IsOrderedRing S] {f h : R → S} {D : Set R} {a : WithBot (WithTop R)} {g : S}
    (hg : 0 < g) (hf : HasLimAt f D a g) (hh : HasLimAt h D a ⊥) : HasLimAt (fun x => f x * h x) D a ⊥ :=
  fun x hx ha => (hh x hx ha).pos_mul_bot hg (hf x hx ha)

lemma HasLimAt.neg_mul_bot [IsOrderedRing S] {f h : R → S} {D : Set R} {a : WithBot (WithTop R)} {g : S}
    (hg : g < 0) (hf : HasLimAt f D a g) (hh : HasLimAt h D a ⊥) : HasLimAt (fun x => f x * h x) D a ⊤ :=
  fun x hx ha => (hh x hx ha).neg_mul_bot hg (hf x hx ha)

lemma HasLimAt.inv [IsOrderedRing S] {f : R → S} {D : Set R} {a : WithBot (WithTop R)} {g : S}
    (h : HasLimAt f D a g) (hg : g ≠ 0) : HasLimAt (fun x => (f x)⁻¹) D a ↑g⁻¹ := fun x hx ha => (h x hx ha).inv hg

lemma HasLimAt.inv_top [IsOrderedRing S] {f : R → S} {D : Set R} {a : WithBot (WithTop R)}
    (h : HasLimAt f D a ⊤) : HasLimAt (fun x => (f x)⁻¹) D a 0 := fun x hx ha => (h x hx ha).inv_top

lemma HasLimAt.inv_bot [IsOrderedRing S] {f : R → S} {D : Set R} {a : WithBot (WithTop R)}
    (h : HasLimAt f D a ⊥) : HasLimAt (fun x => (f x)⁻¹) D a 0 := fun x hx ha => (h x hx ha).inv_bot

lemma HasLimAt.div [IsOrderedRing S] {f h : R → S} {D : Set R} {a : WithBot (WithTop R)} {g₁ g₂ : S}
    (hf : HasLimAt f D a g₁) (hh : HasLimAt h D a g₂) (hg : g₂ ≠ 0) : HasLimAt (fun x => f x / h x) D a (g₁ / g₂) := by
  simp [div_eq_mul_inv]; exact fun x hx ha => (hf x hx ha).mul ((hh x hx ha).inv hg)

lemma HasLimAt.top_div_pos [IsOrderedRing S] {f h : R → S} {D : Set R} {a : WithBot (WithTop R)} {g : S}
    (hg : 0 < g) (hf : HasLimAt f D a ⊤) (hh : HasLimAt h D a g) : HasLimAt (fun x => f x / h x) D a ⊤ := by
  simp [div_eq_mul_inv]; exact hf.top_mul_pos (inv_pos.mpr hg) (hh.inv hg.ne.symm)

lemma HasLimAt.top_div_neg [IsOrderedRing S] {f h : R → S} {D : Set R} {a : WithBot (WithTop R)} {g : S}
    (hg : g < 0) (hf : HasLimAt f D a ⊤) (hh : HasLimAt h D a g) : HasLimAt (fun x => f x / h x) D a ⊥ := by
  simp [div_eq_mul_inv]; exact hf.top_mul_neg (inv_neg''.mpr hg) (hh.inv hg.ne)

lemma HasLimAt.div_top [IsOrderedRing S] {f h : R → S} {D : Set R} {a : WithBot (WithTop R)} {g : S}
    (hf : HasLimAt f D a g) (hh : HasLimAt h D a ⊤) : HasLimAt (fun x => f x / h x) D a 0 := by
  simp [div_eq_mul_inv]; convert hf.mul hh.inv_top; simp

lemma HasLimAt.bot_div_pos [IsOrderedRing S] {f h : R → S} {D : Set R} {a : WithBot (WithTop R)} {g : S}
    (hg : 0 < g) (hf : HasLimAt f D a ⊥) (hh : HasLimAt h D a g) : HasLimAt (fun x => f x / h x) D a ⊥ := by
  simp [div_eq_mul_inv]; exact hf.bot_mul_pos (inv_pos.mpr hg) (hh.inv hg.ne.symm)

lemma HasLimAt.bot_div_neg [IsOrderedRing S] {f h : R → S} {D : Set R} {a : WithBot (WithTop R)} {g : S}
    (hg : g < 0) (hf : HasLimAt f D a ⊥) (hh : HasLimAt h D a g) : HasLimAt (fun x => f x / h x) D a ⊤ := by
  simp [div_eq_mul_inv]; exact hf.bot_mul_neg (inv_neg''.mpr hg) (hh.inv hg.ne)

lemma HasLimAt.div_bot [IsOrderedRing S] {f h : R → S} {D : Set R} {a : WithBot (WithTop R)} {g : S}
    (hf : HasLimAt f D a g) (hh : HasLimAt h D a ⊥) : HasLimAt (fun x => f x / h x) D a 0 := by
  simp [div_eq_mul_inv]; convert hf.mul hh.inv_bot; simp

abbrev HasLeftLim (f : R → S) (D : Set R := Set.univ) (a : R) (g : WithBot (WithTop S)) :=
  HasLimAt f (D ∩ Set.Iio a) a g

abbrev HasRightLim (f : R → S) (D : Set R := Set.univ) (a : R) (g : WithBot (WithTop S)) :=
  HasLimAt f (D ∩ Set.Ioi a) a g

/-- **Th. 5.1.** Cauchy's epsilon-delta definition for a finite left limit -/
lemma HasLeftLim.def [IsOrderedRing R] [FloorSemiring R] {f : R → S} {D : Set R} {a : R} {g : S} :
    HasLeftLim f D a g ↔ ∀ ε > 0, ∃ δ > 0, ∀ x ∈ D, x < a → a - x < δ → |f x - g| < ε := by
  simp [HasLeftLim, HasLimAt.def]; apply forall₂_congr; intro e he
  apply exists_congr; intro d; apply and_congr_right; intro hd
  apply forall₃_congr; intro x hx hu; constructor
  · exact fun h hl => h hu.ne (abs_sub_lt_iff.mpr ⟨(sub_neg_of_lt hu).trans hd, hl⟩)
  · intro h hn hl; apply h; apply lt_of_abs_lt; rwa [abs_sub_comm]

/-- **Th. 5.1.** Cauchy's epsilon-delta definition for a `⊤` left limit -/
lemma HasLeftLim.def_top [IsOrderedRing R] [FloorSemiring R] {f : R → S} {D : Set R} {a : R} :
    HasLeftLim f D a ⊤ ↔ ∀ L, ∃ δ > 0, ∀ x ∈ D, x < a → a - x < δ → L < f x := by
  simp [HasLeftLim, HasLimAt.def_top']; apply forall_congr'; intro L
  apply exists_congr; intro d; apply and_congr_right; intro hd
  apply forall₃_congr; intro x hx hu; constructor
  · exact fun h hl => h hu.ne (abs_sub_lt_iff.mpr ⟨(sub_neg_of_lt hu).trans hd, hl⟩)
  · intro h hn hl; apply h; apply lt_of_abs_lt; rwa [abs_sub_comm]

/-- **Th. 5.1.** Cauchy's epsilon-delta definition for a `⊥` left limit -/
lemma HasLeftLim.def_bot [IsOrderedRing R] [FloorSemiring R] {f : R → S} {D : Set R} {a : R} :
    HasLeftLim f D a ⊥ ↔ ∀ L, ∃ δ > 0, ∀ x ∈ D, x < a → a - x < δ → f x < L := by
  simp [HasLeftLim, HasLimAt.def_bot']; apply forall_congr'; intro L
  apply exists_congr; intro d; apply and_congr_right; intro hd
  apply forall₃_congr; intro x hx hu; constructor
  · exact fun h hl => h hu.ne (abs_sub_lt_iff.mpr ⟨(sub_neg_of_lt hu).trans hd, hl⟩)
  · intro h hn hl; apply h; apply lt_of_abs_lt; rwa [abs_sub_comm]

/-- **Th. 5.1.** Cauchy's epsilon-delta definition for a finite right limit -/
lemma HasRightLim.def [IsOrderedRing R] [FloorSemiring R] {f : R → S} {D : Set R} {a : R} {g : S} :
    HasRightLim f D a g ↔ ∀ ε > 0, ∃ δ > 0, ∀ x ∈ D, a < x → x - a < δ → |f x - g| < ε := by
  simp [HasRightLim, HasLimAt.def]; apply forall₂_congr; intro e he
  apply exists_congr; intro d; apply and_congr_right; intro hd
  apply forall₃_congr; intro x hx hl; constructor
  · exact fun h hu => h hl.ne.symm (abs_sub_lt_iff.mpr ⟨hu, (sub_neg_of_lt hl).trans hd⟩)
  · exact fun h hn hu => h (lt_of_abs_lt hu)

/-- **Th. 5.1.** Cauchy's epsilon-delta definition for a `⊤` right limit -/
lemma HasRightLim.def_top [IsOrderedRing R] [FloorSemiring R] {f : R → S} {D : Set R} {a : R} :
    HasRightLim f D a ⊤ ↔ ∀ L, ∃ δ > 0, ∀ x ∈ D, a < x → x - a < δ → L < f x := by
  simp [HasRightLim, HasLimAt.def_top']; apply forall_congr'; intro L
  apply exists_congr; intro d; apply and_congr_right; intro hd
  apply forall₃_congr; intro x hx hl; constructor
  · exact fun h hu => h hl.ne.symm (abs_sub_lt_iff.mpr ⟨hu, (sub_neg_of_lt hl).trans hd⟩)
  · exact fun h hn hu => h (lt_of_abs_lt hu)

/-- **Th. 5.1.** Cauchy's epsilon-delta definition for a `⊥` right limit -/
lemma HasRightLim.def_bot [IsOrderedRing R] [FloorSemiring R] {f : R → S} {D : Set R} {a : R} :
    HasRightLim f D a ⊥ ↔ ∀ L, ∃ δ > 0, ∀ x ∈ D, a < x → x - a < δ → f x < L := by
  simp [HasRightLim, HasLimAt.def_bot']; apply forall_congr'; intro L
  apply exists_congr; intro d; apply and_congr_right; intro hd
  apply forall₃_congr; intro x hx hl; constructor
  · exact fun h hu => h hl.ne.symm (abs_sub_lt_iff.mpr ⟨hu, (sub_neg_of_lt hl).trans hd⟩)
  · exact fun h hn hu => h (lt_of_abs_lt hu)

/-- **Th. 5.3.** A limit exists iff the left and right limits agree. -/
lemma hasLimAt_iff_left_and_right [IsOrderedRing R] [FloorSemiring R] {f : R → S} {D : Set R} {a : R}
    {g : WithBot (WithTop S)} : HasLimAt f D a g ↔ HasLeftLim f D a g ∧ HasRightLim f D a g := by
  constructor; intro h; and_intros
  · exact fun x hx ha => h x (fun n => ⟨Set.mem_of_mem_inter_left (hx n).1, (hx n).2⟩) ha
  · exact fun x hx ha => h x (fun n => ⟨Set.mem_of_mem_inter_left (hx n).1, (hx n).2⟩) ha
  · match g with
    | (g : S) =>
      rw [HasLeftLim.def, HasRightLim.def, HasLimAt.def]; intro ⟨hl, hr⟩ e he
      replace ⟨d1, hd1, hl⟩ := hl e he; replace ⟨d2, hd2, hr⟩ := hr e he
      exists min d1 d2, lt_min hd1 hd2; intro x hx hne hd; cases lt_or_gt_of_ne hne
      case inl h => rw [abs_sub_comm, abs_lt, lt_min_iff] at hd; exact hl x hx h hd.2.1
      case inr h => exact hr x hx h (lt_min_iff.mp (abs_lt.mp hd).2).2
    | ⊤ =>
      rw [HasLeftLim.def_top, HasRightLim.def_top, HasLimAt.def_top']; intro ⟨hl, hr⟩ L
      replace ⟨d1, hd1, hl⟩ := hl L; replace ⟨d2, hd2, hr⟩ := hr L
      exists min d1 d2, lt_min hd1 hd2; intro x hx hne hd; cases lt_or_gt_of_ne hne
      case inl h => rw [abs_sub_comm, abs_lt, lt_min_iff] at hd; exact hl x hx h hd.2.1
      case inr h => exact hr x hx h (lt_min_iff.mp (abs_lt.mp hd).2).2
    | ⊥ =>
      rw [HasLeftLim.def_bot, HasRightLim.def_bot, HasLimAt.def_bot']; intro ⟨hl, hr⟩ L
      replace ⟨d1, hd1, hl⟩ := hl L; replace ⟨d2, hd2, hr⟩ := hr L
      exists min d1 d2, lt_min hd1 hd2; intro x hx hne hd; cases lt_or_gt_of_ne hne
      case inl h => rw [abs_sub_comm, abs_lt, lt_min_iff] at hd; exact hl x hx h hd.2.1
      case inr h => exact hr x hx h (lt_min_iff.mp (abs_lt.mp hd).2).2

/-- **Th. 5.3.** Limit doesn't exist if the left and right limits disagree. -/
lemma hasLimAt_of_left_ne_right [IsOrderedRing R] [FloorSemiring R] [IsOrderedRing S] {f : R → S} {D : Set R} {a : R}
    {g₁ g₂ : WithBot (WithTop S)} (hal : (D ∩ Set.Iio a).AccPt a) (har : (D ∩ Set.Ioi a).AccPt a)
    (hl : HasLeftLim f D a g₁) (hr : HasRightLim f D a g₂) (hne : g₁ ≠ g₂) : ¬∃ g, HasLimAt f D a g := by
  by_contra!; replace ⟨g, this⟩ := this
  rw [hasLimAt_iff_left_and_right] at this
  replace hl := HasLimAt.eq hal hl this.1
  replace hr := HasLimAt.eq har hr this.2
  revert hne; simp [hl, hr]

/-- `HasLimAt` agrees with Mathlib's `Tendsto` on the reals. -/
lemma hasLimAt_iff_tendsto {f : ℝ → ℝ} {D : Set ℝ} (a g : ℝ) :
    HasLimAt f D a g ↔ Filter.Tendsto f (nhdsWithin a (D \ {a})) (nhds g) := by
  simp [HasLimAt.def, Metric.tendsto_nhdsWithin_nhds, Real.dist_eq]

lemma hasLimAt_top'_iff_tendsto {f : ℝ → ℝ} {D : Set ℝ} (a : ℝ) :
    HasLimAt f D a ⊤ ↔ Filter.Tendsto f (nhdsWithin a (D \ {a})) Filter.atTop := by
  simp_rw [HasLimAt, hasLim'_top_iff_tendsto, HasLim', hasLim_iff_tendsto]
  rw [Filter.tendsto_iff_seq_tendsto]
  simp [WithBot.some, WithTop.some, tendsto_nhdsWithin_iff]; constructor
  · intro h x ha n0 hx
    specialize h (fun n => x (max n n0)) (fun n => hx _ (by simp))
    specialize h (ha.congr' _)
    · simp [Filter.EventuallyEq]; exists n0; intro n hn; congr; exact (max_eq_left hn).symm
    refine h.congr' ?_; simp [Filter.EventuallyEq]; exists n0; intro n hn; congr; exact (max_eq_left hn)
  · intro h x hx ha; specialize h x ha 0; simp at h; exact h hx

lemma hasLimAt_bot'_iff_tendsto {f : ℝ → ℝ} {D : Set ℝ} (a : ℝ) :
    HasLimAt f D a ⊥ ↔ Filter.Tendsto f (nhdsWithin a (D \ {a})) Filter.atBot := by
  simp_rw [HasLimAt, hasLim'_bot_iff_tendsto, HasLim', hasLim_iff_tendsto]
  rw [Filter.tendsto_iff_seq_tendsto]
  simp [WithBot.some, WithTop.some, tendsto_nhdsWithin_iff]; constructor
  · intro h x ha n0 hx
    specialize h (fun n => x (max n n0)) (fun n => hx _ (by simp))
    specialize h (ha.congr' _)
    · simp [Filter.EventuallyEq]; exists n0; intro n hn; congr; exact (max_eq_left hn).symm
    refine h.congr' ?_; simp [Filter.EventuallyEq]; exists n0; intro n hn; congr; exact (max_eq_left hn)
  · intro h x hx ha; specialize h x ha 0; simp at h; exact h hx

/-- **Th. 4.6.** Equivalent to `deriv Real.sin 0 = 1` -/
theorem hasLimAt_sin_div : HasLimAt (fun x => Real.sin x / x) Set.univ 0 1 := by
  apply hasLimAt_iff_left_and_right.mpr; rw [and_iff_right_of_imp]
  · apply HasLimAt.squeeze_const (f := Real.cos)
    · exists 1, zero_lt_one; simp; intro x h1 _ h2
      rw [le_div_comm₀ (Real.cos_pos_of_le_one h2.le) h1, ← Real.tan_eq_sin_div_cos]
      exact Real.le_tan h1.le (lt_of_lt_of_le (abs_lt.mp h2).2 Real.one_le_pi_div_two)
    · exists 1, zero_lt_one; simp; intro x h _ _; exact (div_le_one h).mpr (Real.sin_le h.le)
    · rw [hasLimAt_iff_tendsto] -- perhaps instead downstream this to Continuous.lean?
      apply tendsto_nhdsWithin_of_tendsto_nhds
      exact Real.continuous_cos.tendsto' 0 1 Real.cos_zero
  · intro hr x hx ha; specialize hr (fun n => -x n); apply HasLim.neg at ha
    simp [WithBot.some, WithTop.some, Function.comp_def] at hr hx ha
    exact hr hx ha
