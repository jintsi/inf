import Mathlib.Analysis.Real.Cardinality
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Polynomial.Cardinal
import Mathlib.Order.Filter.EventuallyConst

namespace Elitm.Cwi8

open Cardinal

def Zad1a [Ring α] : {a : α // Even a} ≃ {b : α // Odd b} where
  toFun := fun ⟨a, h⟩ => ⟨a + 1, h.add_one⟩
  invFun := fun ⟨b, h⟩ => ⟨b - 1, h.sub_odd odd_one⟩
  left_inv := fun ⟨a, h⟩ => by simp
  right_inv := fun ⟨b, h⟩ => by simp

alias Zad1b := finSumNatEquiv

@[simp]
theorem Zad1h : #NNReal = #ℝ := by
  apply le_antisymm (mk_subtype_le _)
  rw [le_def]; use fun r => ⟨r.exp, r.exp_nonneg⟩; intro r r'; simp

alias Zad2 := Equiv.Set.congr

noncomputable def Zad3 : Set α ≃ (α → Bool) := (Equiv.refl α).arrowCongr Equiv.propEquivBool

theorem Zad4 : #(ℕ → Bool) = #(ℕ → ℝ) := by simp [mk_real]

theorem Zad5a : Set.ncard {x : ℕ | ∃ y, x = Real.sin y} = 2 := by
  trans Set.ncard {0, 1}; congr 1
  · ext n; simp; constructor
    · intro ⟨y, hy⟩; suffices n ≤ 1 by omega
      simpa [← hy] using Real.sin_le_one y
    · rintro (rfl | rfl)
      · use 0; simp
      · use Real.pi / 2; simp
  simp

noncomputable def Zad5b : {x // ∃ y : ℕ, x = Real.log y} ≃ ℕ where
  toFun := fun ⟨x, h⟩ => ⌊x.exp⌋₊ - 1
  invFun n := ⟨Real.log (n + 1), n + 1, by simp⟩
  left_inv := fun ⟨x, y, h⟩ => by
    simp [h]; cases y with
    | zero => simp
    | succ y => rw [Real.exp_log (by norm_cast; simp), Nat.floor_natCast]; simp
  right_inv n := by simp; rw [Real.exp_log (by norm_cast; simp), ← Nat.cast_add_one,
    Nat.floor_natCast]; rfl

def Zad5c : {x : ℕ // ∃ y, x = Real.tan y} ≃ ℕ :=
  Equiv.subtypeUnivEquiv fun n => ⟨Real.arctan n, by simp⟩

def Zad5d [DivisionRing K] : {p : K × K // p.2 = 3 * p.1 - 4} ≃ K where
  toFun := fun ⟨p, h⟩ => p.1
  invFun x := ⟨⟨x, 3 * x - 4⟩, rfl⟩
  left_inv := fun ⟨p, h⟩ => by simp [← h]

theorem Zad5e : #{x : ℝ // ∃ n, ¬Irrational (x ^ (n + 1))} = ℵ₀ := by
  apply le_antisymm; swap
  · rw [← Cardinal.mkRat, le_def]; use fun q => ⟨q, 0, by simp⟩
    intro a b; simp
  trans #(ℚ × ℕ); swap; simp
  apply mk_le_of_surjective
  case f => intro ⟨q, n⟩; exact if h : 0 ≤ q then
      ⟨q ^ (n.succ : ℝ)⁻¹, n, by rw [Real.rpow_inv_natCast_pow] <;> simp [h]⟩
    else ⟨-(-q) ^ (n.succ : ℝ)⁻¹, n, by
      rw [neg_pow, Real.rpow_inv_natCast_pow]
      · simp [Irrational]; use (-1) ^ n * q; simp [pow_succ]
      · simpa using le_of_not_ge h
      · simp⟩
  intro ⟨x, n, h⟩; simp [Irrational] at h; rcases h with ⟨q, h⟩
  by_cases hx : 0 ≤ x
  · use ⟨q, n⟩; dsimp
    rw [dif_pos (by grw [← Rat.cast_nonneg (K := ℝ), h, ← hx, pow_succ, mul_zero]),
      Subtype.mk.injEq, h, Real.pow_rpow_inv_natCast hx n.add_one_ne_zero]
  · use ⟨-q ^ 2, n + 1 + n⟩; dsimp
    rw [dif_neg (by simp; rw [← Rat.cast_eq_zero (α := ℝ), h]; simpa using ne_of_not_ge hx),
      Subtype.mk.injEq, Rat.cast_neg, neg_neg, Rat.cast_pow, h, ← pow_mul, mul_two, ← add_assoc]
    trans -((-x) ^ ?_) ^ (?_ : ℝ)
    · congr 2; swap; rfl; symm; convert Even.neg_pow _ _; simp
    rw [Real.pow_rpow_inv_natCast, neg_neg]; simpa using le_of_not_ge hx
    simp

theorem Zad5h : #(Polynomial ℚ) = ℵ₀ := by simp

theorem Zad5i : #{f : ℕ → ℝ // Filter.atTop.EventuallyConst f} = 𝔠 := by
  trans #(ℝ × (ℕ →₀ ℝ)); swap; · simpa using mk_real
  apply mk_congr; constructor
  case toFun =>
    intro ⟨f, hf⟩; use Filter.atTop.limUnder f
    apply Finsupp.ofSupportFinite fun n => f n - Filter.atTop.limUnder f;
    have := hf.exists_tendsto; simp at this; rcases this with ⟨g, a, h⟩
    apply BddAbove.finite; simp [bddAbove_def]; use a; intro b; contrapose
    simp [sub_eq_zero]; intro hab; rw [h b hab.le]; symm; apply Filter.Tendsto.limUnder_eq
    apply tendsto_atTop_of_eventually_const h
  case invFun =>
    intro ⟨g, s, f, h⟩; use fun n => f n + g; simp [Filter.eventuallyConst_iff_tendsto]
    use g; simp; use (s.sup id).succ; intro n; contrapose!; simp [← h]; apply s.le_sup
  case left_inv => intro ⟨f, hf⟩; ext n; simp [Finsupp.ofSupportFinite]
  case right_inv =>
    intro ⟨g, s, f, h⟩; simp; rw [and_iff_left_of_imp]
    · apply Filter.Tendsto.limUnder_eq; apply tendsto_atTop_of_eventually_const
      swap; exact (s.sup id).succ; intro n; contrapose!; simp [← h]; apply s.le_sup
    intro hg; ext n; simp [Finsupp.ofSupportFinite_coe, hg]

theorem Zad5k [Ring R] [LinearOrder R] [IsOrderedRing R] [Nontrivial R] :
    #{p : R × R // p.1 * p.2 < 1} = #R := by
  apply le_antisymm
  · grw [mk_subtype_le]; simp
  rw [le_def]; use fun x => ⟨(x, -x), by dsimp; grw [mul_neg, ← sq, ← sq_nonneg]; simp⟩
  intro x y; simp

theorem Zad5l : #(Finset ℚ) = ℵ₀ := mk_eq_aleph0 _

theorem Zad5m : #{f : ℕ → ℕ // StrictMono f} = 𝔠 := by
  trans #(ℕ → ℕ); swap; simp
  apply mk_congr; constructor
  case toFun => intro ⟨f, hf⟩ n; exact match n with
    | 0 => f 0
    | n + 1 => f (n + 1) - (f n + 1)
  case invFun =>
    intro f; use fun n => (∑ i ∈ Finset.range (n + 1), f i) + n
    intro a b hab; simp; grw [hab]; gcongr
  case left_inv =>
    intro ⟨f, hf⟩; ext n; simp; induction n with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ]; dsimp
      rw [add_right_comm, ← add_assoc, ih, Nat.add_sub_cancel']; apply hf; simp
  case right_inv =>
    intro f; simp [add_assoc, Nat.add_sub_add_right]; simp [Finset.sum_range_succ]
    ext n; split <;> rfl

theorem Zad5n : #{f : ℕ → ℝ // StrictMono f} = 𝔠 := by
  trans #(ℝ × (ℕ → NNReal)); swap; simp [mk_real]
  trans #{f : ℕ → ℝ // Monotone f}
  · apply le_antisymm (mk_subtype_mono fun f => StrictMono.monotone)
    rw [le_def]; use fun ⟨f, hf⟩ => ⟨fun n => f n + n, by
      intro m n hmn; simp; grw [hmn]; simpa using hf hmn.le⟩
    intro ⟨f, hf⟩ ⟨g, hg⟩; simp [funext_iff]
  apply mk_congr; constructor
  case toFun => intro ⟨f, hf⟩; use f 0; intro n; use f (n + 1) - f n; simp; apply hf; simp
  case invFun =>
    intro ⟨r, f⟩; use fun n => r + ∑ i ∈ Finset.range n, f i
    intro a b hab; dsimp; gcongr
  case left_inv =>
    intro ⟨f, hf⟩; simp; simp [← NNReal.val_eq_coe, -Finset.sum_sub_distrib, Finset.sum_range_sub]
  case right_inv => intro ⟨r, f⟩; simp [Finset.sum_range_succ]; ext; rfl

theorem Zad5o [Semiring R] [Invertible (2 : R)] : #{x : R // Even x} = #R :=
  mk_congr (Equiv.subtypeUnivEquiv Even.all)

theorem Zad5p : #(Set.diagonal α) = #α :=
  mk_congr {
    toFun p := p.val.1
    invFun x := ⟨(x, x), rfl⟩
    left_inv := fun ⟨(a, b), h⟩ => by simpa using h
  }

theorem Zad5r : #{p : ℝ × ℝ // p.1 ^ 2 + p.2 ^ 2 = 1} = 𝔠 := by
  apply le_antisymm
  · grw [mk_subtype_le]; simp [mk_real]
  rw [← mk_Icc_real one_pos, le_def]
  use fun ⟨x, hx⟩ => ⟨(√x, √(1 - x)), by simp; rw [Real.sq_sqrt, Real.sq_sqrt, add_sub_cancel] <;> simp_all⟩
  intro ⟨x, hx⟩ ⟨y, hy⟩; simp; rw [Real.sqrt_inj hx.1 hy.1]; tauto

theorem Zad5s [AddGroup G] (a : G) : #{p : G × G // p.1 - p.2 = a} = #G :=
  mk_congr {
    toFun p := p.val.2
    invFun y := ⟨(a + y, y), by simp⟩
    left_inv := fun ⟨(x, y), h⟩ => by simp [← h]
  }

theorem Zad6 (c : Cardinal.{u}) : 2 ^ c ≠ ℵ₀ := by
  by_cases! h : c < ℵ₀
  · rw [lt_aleph0] at h; rcases h with ⟨n, rfl⟩; norm_cast; exact ne_of_lt natCast_lt_aleph0
  · apply ne_of_gt; grw [h]; exact c.cantor
