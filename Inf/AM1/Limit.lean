import Mathlib.Tactic
import Mathlib.Algebra.Order.AbsoluteValue.Basic

/-! ## Roughly the content of lectures 2 & 3 -/

variable [Field R] [LinearOrder R]

/-- (Really general) definition of a limit of a sequence.
Note that the sequence is `Nat`-indexed, as opposed to `PNat` -/
def HasLim (a : ℕ → R) (g : R) := ∀ ε > 0, ∃ n₀, ∀ n ≥ n₀, abs (a n - g) < ε

/-- **Th. 2.1.** A constant sequence is convergent. -/
lemma hasLim_const [IsStrictOrderedRing R] {a : R} : HasLim (fun _ => a) a := by
  intro e he; exists 0; intro n hn; convert he.lt; simp

/-- **Th. 2.2.** A convergent sequence has only one limit. -/
lemma hasLim_unique [IsStrictOrderedRing R] (a : ℕ → R) : Subsingleton {g // HasLim a g} where
  allEq := by
    simp [HasLim]
    intro g1 hg1 g2 hg2
    by_contra! h
    have he : 0 < abs (g1 - g2) / 2 := by field_simp; simp; grind
    have ⟨n1, hg1⟩ := hg1 _ he
    have ⟨n2, hg2⟩ := hg2 _ he
    let n := max n1 n2
    have hg1 := hg1 n (by omega)
    have hg2 := hg2 n (by omega)
    have h := add_lt_add hg1 hg2; revert h; simp
    convert abs_sub_le g1 (a n) g2 using 2
    exact abs_sub_comm (a n) g1

/-- **Th. 2.3.** A convergent sequence is bounded -/
lemma hasLim_bddAbove [IsStrictOrderedRing R] {a : ℕ → R} {g : R} (h : HasLim a g) :
    BddAbove (Set.range a) := by
  simp [HasLim, bddAbove_def] at *
  have ⟨n, h⟩ := h 1 (by simp)
  exists WithBot.unbot (↑(g + 1) ::ₘ (Multiset.range n).map ((↑) ∘ a)).sup ?H
  · simp --mathlib pls give us Multiset.sup'
  intro i; simp [WithBot.le_unbot_iff]
  by_cases! hi : i < n
  · right; apply Multiset.le_sup; apply Multiset.mem_map_of_mem; simpa
  · left; rw [← WithBot.coe_one, ← WithBot.coe_add, WithBot.coe_le_coe]
    have h := abs_lt.mp (h i hi)
    grind

/-- **Th. 2.3.** A convergent sequence is bounded -/
lemma hasLim_bddBelow [IsStrictOrderedRing R] {a : ℕ → R} {g : R} (h : HasLim a g) :
    BddBelow (Set.range a) := by
  simp [HasLim, bddBelow_def] at *
  have ⟨n, h⟩ := h 1 (by simp)
  exists WithTop.untop (↑(g - 1) ::ₘ (Multiset.range n).map ((↑) ∘ a)).inf ?H
  · simp
  intro i; simp [WithTop.untop_le_iff]
  by_cases! hi : i < n
  · right; apply Multiset.inf_le; apply Multiset.mem_map_of_mem; simpa
  · left; rw [← WithTop.coe_one, ← WithTop.LinearOrderedAddCommGroup.coe_sub, WithTop.coe_le_coe] -- "shouldn't create diamonds" my ass
    have h := abs_lt.mp (h i hi)
    grind

lemma hasLim_add [IsStrictOrderedRing R] {an bn : ℕ → R} {a b : R} (ha : HasLim an a) (hb : HasLim bn b) :
    HasLim (an + bn) (a + b) := by
  simp [HasLim] at *
  intro e he
  have ⟨n1, ha⟩ := ha (e / 2) (by positivity)
  have ⟨n2, hb⟩ := hb (e / 2) (by positivity)
  exists max n1 n2; intro n hn;
  have h := add_lt_add (ha n (by grind)) (hb n (by grind)); simp at h
  rw [add_sub_add_comm]
  exact lt_of_le_of_lt (abs_add_le _ _) h

lemma hasLim_add_const {a : ℕ → R} {g b : R} (h : HasLim a g) :
    HasLim (a + fun _ => b) (g + b) := by simpa [HasLim]

lemma hasLim_const_add (a : ℕ → R) {g b : R} {h : HasLim a g} :
    HasLim ((fun _ => b) + a) (b + g) := by simpa [HasLim]

lemma hasLim_mul [IsStrictOrderedRing R] {an bn : ℕ → R} {a b : R} (ha : HasLim an a) (hb : HasLim bn b) :
    HasLim (an * bn) (a * b) := by
  simp [HasLim] at *
  intro e he
  have ⟨n1, ha⟩ := ha (e / 2 / max (|a| + |b|) (e + 1)) (by positivity)
  have ⟨n2, hb⟩ := hb (e / 2 / max (|a| + |b|) (e + 1)) (by positivity)
  exists max n1 n2; intro n hn;
  replace ha := ha n (by grind); replace hb := hb n (by grind)
  have hab1 := mul_lt_mul'' ha hb (by simp) (by simp); rw [← abs_mul, ← sq] at hab1
  replace ha := mul_le_mul_of_nonneg_left ha.le (abs_nonneg b)
  replace hb := mul_le_mul_of_nonneg_left hb.le (abs_nonneg a)
  have hab2 := ((add_mul |a| |b| _) ▸ add_le_add hb ha).trans
    (mul_le_mul_of_nonneg_right (le_max_left _ (e + 1)) (by positivity))
  field_simp at hab2; rw [← le_div_iff₀, ← abs_mul, ← abs_mul] at hab2
  simp [-abs_mul, mul_sub] at hab2
  apply (abs_add_le _ _).trans at hab2
  have hab := add_lt_add_of_lt_of_le hab1 hab2;
  apply lt_of_le_of_lt (abs_add_le _ _) at hab
  ring_nf at hab; refine lt_of_lt_of_le hab ?_
  field_simp; rw [two_mul, add_mul]; simp;
  have h : e * 2 ≤ (1 + e) ^ 2 := by
    ring_nf; exact le_add_of_le_of_nonneg (le_add_of_nonneg_left (by simp)) (by positivity)
  apply fun h => le_trans h ((sq_le_sq₀ (by positivity) (by positivity)).mpr
    (le_max_right (|a|+|b|) (1 + e))) at h
  grind; simp

lemma hasLim_mul_const [IsStrictOrderedRing R] {a : ℕ → R} {g b : R} (h : HasLim a g) :
    HasLim (a * fun _ => b) (g * b) := hasLim_mul h hasLim_const

lemma hasLim_const_mul [IsStrictOrderedRing R] {a : ℕ → R} {g b : R} (h : HasLim a g) :
    HasLim ((fun _ => b) * a) (b * g) := hasLim_mul hasLim_const h

lemma hasLim_neg {a : ℕ → R} {g : R} (h : HasLim a g) : HasLim (-a) (-g) := by
  simp [HasLim, abs_sub_comm, neg_add_eq_sub] at *; assumption

lemma hasLim_sub [IsStrictOrderedRing R] {an bn : ℕ → R} {a b : R} (ha : HasLim an a) (hb : HasLim bn b) :
    HasLim (an - bn) (a - b) := by rw [sub_eq_add_neg, sub_eq_add_neg]; exact hasLim_add ha (hasLim_neg hb)

lemma hasLim_sub_const {a : ℕ → R} {g b : R} (h : HasLim a g) :
    HasLim (a - fun _ => b) (g - b) := by simpa [HasLim]

lemma hasLim_const_sub (a : ℕ → R) {g b : R} {h : HasLim a g} :
    HasLim ((fun _ => b) - a) (b - g) := by simp [HasLim, abs_sub_comm] at *; assumption

lemma hasLim_inv [IsStrictOrderedRing R] {a : ℕ → R} {g : R} (h : HasLim a g) (hg : g ≠ 0) : HasLim a⁻¹ g⁻¹ := by
  wlog hg : 0 < g generalizing a g
  · have this := hasLim_neg <| this (hasLim_neg h) (by simp; assumption) (by grind); simp at this; assumption
  simp [HasLim] at *
  intro e he
  wlog heg : e < g⁻¹ generalizing e
  · have ⟨n, h⟩ := this (g⁻¹ / 2) (by positivity) (by simpa)
    exists n; intro n hn; replace h := h n hn
    simp at heg; exact lt_of_lt_of_le h (le_trans (half_le_self (by positivity)) heg)
  have ⟨n, h⟩ := h (e / (g⁻¹ * (g⁻¹ + e))) (div_pos he <| mul_pos (inv_pos.mpr hg) <| add_pos (inv_pos.mpr hg) he)
  exists n; intro n hn; replace h := h n hn
  rw (occs := .pos [1]) [← add_sub_cancel_left g⁻¹ e, ← inv_sub_inv, inv_inv] at h <;> try positivity
  have han : 0 < a n := sub_self g ▸ (sub_lt_comm.mp <| lt_of_abs_lt <|
    (abs_sub_comm (a n) g ▸ h).trans (sub_lt_self g (by positivity)))
  rw [abs_lt, neg_lt, neg_sub]; constructor
  · rw [sub_lt_comm, lt_inv_comm₀, ← sub_lt_sub_iff_right g]
    apply lt_of_lt_of_le (lt_of_abs_lt h); rw (occs := .pos [1,4]) [← inv_inv g]
    rw [inv_sub_inv, inv_sub_inv]; field_simp; simp; field_simp; rw [one_le_div]
    simp; ring_nf; apply le_add_of_nonneg_right; positivity
    have hge := (mul_lt_mul_iff_right₀ hg).mpr heg; rw [mul_inv_cancel₀] at hge; simpa; assumption
    exact sub_ne_zero_of_ne (ne_of_gt heg); (repeat positivity); exact sub_pos_of_lt heg
    · exact han
  · rw [sub_lt_iff_lt_add, inv_lt_comm₀, ← sub_lt_sub_iff_left g]; rw [abs_sub_comm] at h
    case right.ha => exact han
    case right.hb => exact add_pos he (he.trans heg)
    apply lt_of_lt_of_le (lt_of_abs_lt h); field_simp; simp; ring_nf; simp

lemma hasLim_div [IsStrictOrderedRing R] {an bn : ℕ → R} {a b : R} (ha : HasLim an a) (hb : HasLim bn b)
    (hne : b ≠ 0) : HasLim (an / bn) (a / b) := by
  rw [div_eq_mul_inv, div_eq_mul_inv]; exact hasLim_mul ha (hasLim_inv hb hne)

lemma hasLim_div_const [IsStrictOrderedRing R] {a : ℕ → R} {g b : R} (h : HasLim a g) :
    HasLim (a / fun _ => b) (g / b) := by rw [div_eq_mul_inv, div_eq_mul_inv]; exact hasLim_mul_const h

lemma hasLim_const_div [IsStrictOrderedRing R] {a : ℕ → R} {g b : R} (h : HasLim a g) (hb : b ≠ 0) :
    HasLim (a / fun _ => b) (g / b) := hasLim_div h hasLim_const hb
