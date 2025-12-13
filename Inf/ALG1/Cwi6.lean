import Mathlib.Tactic
import Mathlib.RingTheory.Polynomial.SmallDegreeVieta

namespace ALG1

theorem Zad6_1a : LinearIndependent ℚ ![![(0 : ℚ), 1, 2, -1], ![1, 0, 3, 1], ![0, 2, -1, 4]] := by
  simp [linearIndependent_fin_succ, Fin.tail_def, Submodule.mem_span_singleton, Submodule.mem_span_pair]
  intro x h1 h2 h3; linarith

theorem Zad6_1b : ¬LinearIndependent ℚ ![![(1 : ℚ), 2, 0, 3], ![3, -1, 5, 0], ![-1, 5, -5, 6]] := by
  simp [linearIndependent_fin_succ, Fin.tail_def, Submodule.mem_span_singleton, Submodule.mem_span_pair]
  exists 1 / 2, 1 / 2; norm_num

open Polynomial in
theorem Zad6_1c : ¬LinearIndependent ℚ ![(X ^ 3 + 1 : Polynomial ℚ), X ^ 3 - 1, X ^ 2 + X, X ^ 3 + X ^ 2 + X] := by
  simp [Fintype.not_linearIndependent_iff]; exists ![1, 1, 2, -2]; and_intros
  · simp [Fin.sum_univ_succ, Polynomial.smul_eq_C_mul]; ring_nf
    rw [Polynomial.C_ofNat]; simp
  · exists 0

theorem Zad6_2 (s : ℚ) : LinearIndependent ℚ ![![2, 1, 0, s], ![0, 1, 2, 2], ![0, 1, 1, 2], ![s, 0, 2, s]]
    ↔ (s ≠ 0 ∧ s ≠ 4) := by
  simp [linearIndependent_fin_succ, Fin.tail_def, Submodule.mem_span_singleton, Submodule.mem_span_pair,
        Submodule.mem_span_triple]; apply and_congr
  · exact ⟨fun h hs => (h hs (1 / 2) (by norm_num)).right hs, Not.elim⟩
  · constructor
    · contrapose!; intro hs; subst hs; exists 1 / 2; norm_num; exists 3, -2; norm_num
    · intro hs x hx a b h1 h2 h3; grind

theorem Zad6_3a : LinearIndependent ℝ ![id, Real.sin, Real.cos] := by
  simp [linearIndependent_fin_succ, Fin.tail_def, Submodule.mem_span_singleton, Submodule.mem_span_pair, funext_iff]
  and_intros
  · exists 0; simp
  · intro x; exists Real.pi / 2; simp
  · intro x y; by_cases x = 0
    · subst_vars; exists Real.pi; simp; exact Real.pi_ne_zero.symm
    · exists 0; simpa

theorem Zad6_3b : LinearIndependent ℝ ![Real.sin, Real.cos, fun r => Real.sin (2 * r), fun r => Real.cos (2 * r)] := by
  simp [linearIndependent_fin_succ, Fin.tail_def, Submodule.mem_span_singleton, Submodule.mem_span_pair,
        Submodule.mem_span_triple, funext_iff, Real.sin_two_mul, Real.cos_two_mul]; and_intros
  · exists 0; norm_num
  · intro x; by_cases x = 0
    · subst_vars; exists Real.pi / 3; simp
    · exists 0; norm_num; assumption
  · intro x y; by_cases x = 0
    · subst_vars; exists 0; simp
    · exists Real.pi / 2; simpa
  · intro x y z; by_cases x = -1
    · by_cases z = 1
      · exists Real.pi; subst_vars; norm_num
      · exists 0; subst_vars; norm_num; grind
    · exists Real.pi / 2; simp; rwa [neg_eq_iff_eq_neg]

theorem Zad6_3c : ¬LinearIndependent ℝ ![fun r => Real.cos (2 * r), fun r => r.sin ^ 2, fun r => r.cos ^ 2] := by
  simp [Fintype.not_linearIndependent_iff, Real.cos_two_mul']; exists ![1, 1, -1]; and_intros
  · simp [Fin.sum_univ_succ, Pi.add_def, funext_iff]; intro x; ring_nf
  · exists 0; simp

theorem Zad6_3d (n : ℕ) : LinearIndependent ℝ fun (i : Fin n) (x : ℝ) => ∏ k : Fin i, |x - k| := by
  induction n
  case zero => simp
  case succ n ih =>
    simp [linearIndependent_fin_succ', Fin.init_def, ih, Submodule.mem_span_range_iff_exists_fun, funext_iff]
    intro c; by_cases c = 0
    case pos h =>
      exists n; simp [h]; apply Ne.symm; simp [Finset.prod_ne_zero_iff]
      intro k; simp [sub_ne_zero]; exact k.is_lt.ne.symm
    rename_i h
    cases n; simp
    rename_i n; by_contra!; revert h; simp [funext_iff, Fin.forall_iff]; intro i hi
    induction i using Nat.strong_induction_on
    rename_i i ih; replace ih := fun m h => ih m h (h.trans hi); let i := Fin.mk i hi
    specialize this i; rw [Finset.prod_eq_zero (i := i) (by simp) (by simp)] at this
    apply Finset.eq_zero_of_sum_eq_zero (a := i) at this; simp at this
    refine (this ?_ i).resolve_right (Finset.prod_ne_zero_iff.mpr fun k _ => by simp [sub_ne_zero]; exact k.is_lt.ne.symm)
    intro j hj; cases lt_or_gt_of_ne hj
    case neg.succ.h.inl hj => left; exact ih j hj
    case neg.succ.h.inr hj => right; exact Finset.prod_eq_zero (i := ⟨i, hj⟩) (by simp) (by simp)

theorem Zad6_4 (r : ℚ) : ![r, 8, 6] ∈ Submodule.span ℚ
    {![3, 4, 5], ![1, 4, 4], ![7, 4, 7]} ↔ r = -2 := by
  simp [Submodule.mem_span_triple]; constructor
  · intro ⟨a, b, c, h1, h2, h3⟩; linarith
  · intro hr; subst hr; exists -2, 4, 0; norm_num

variable {x₁ x₂ x₃ x₄ : ℚ}

theorem Zad6_5a : 2 * x₁ + x₂ - 2 * x₃ - x₄ = 0 ↔ ![x₁, x₂, x₃, x₄] ∈ Submodule.span ℚ
    {![1, 0, 0, 2], ![0, 1, 0, 1], ![0, 0, 1, -2]} := by simp [Submodule.mem_span_triple]; grind

theorem Zad6_5b : (x₁ + x₂ - x₃ = 0 ∧ x₁ + 2 * x₂ + x₄ = 0) ↔ ![x₁, x₂, x₃, x₄] ∈ Submodule.span ℚ
    {![1, 0, 1, -1], ![0, 1, 1, -2]} := by simp [Submodule.mem_span_pair]; grind

theorem Zad6_5c : (x₁ - x₂ = 0 ∧ x₂ - x₃ = 0 ∧ x₃ - x₄ = 0) ↔ ![x₁, x₂, x₃, x₄] ∈ Submodule.span ℚ
    {![1, 1, 1, 1]} := by simp [Submodule.mem_span_singleton]; grind

theorem Zad6_5d : (x₁ + x₂ = 0 ∧ x₂ + x₃ = 0 ∧ x₃ + x₄ = 0 ∧ x₁ + x₄ = 0) ↔ ![x₁, x₂, x₃, x₄] ∈ Submodule.span ℚ
    {![1, -1, 1, -1]} := by simp [Submodule.mem_span_singleton]; grind

open Polynomial

theorem Zad6_7a : (w ∈ degreeLE ℝ 2 ∧ w.eval 1 = w.eval 2) ↔ w ∈ Submodule.span ℝ {X ^ 2 - 3 * X, 1} := by
  simp [Submodule.mem_span_pair, mem_degreeLE, smul_eq_C_mul]; constructor
  · intro ⟨hd, hw⟩; apply eq_quadratic_of_degree_le_two at hd; rw [hd] at ⊢ hw; norm_num at hw
    exists w.coeff 2, w.coeff 0; congr
    · simp [sub_eq_add_neg, mul_add, ← mul_assoc, ← neg_mul]
      have h : w.coeff 2 * -3 = w.coeff 1 := by linarith
      convert Polynomial.C_inj.mpr h; simp; left; rfl
  · intro ⟨a, b, h⟩; subst h; norm_num; simp [sub_eq_add_neg, mul_add]
    convert degree_quadratic_le using 4
    swap; exact a * -3; simp [mul_assoc]; left; rfl

theorem Zad6_7b : (w ∈ degreeLE ℝ 2 ∧ w.eval 1 = w.eval (-1)) ↔ w ∈ Submodule.span ℝ {X ^ 2, 1} := by
  simp [Submodule.mem_span_pair, mem_degreeLE, smul_eq_C_mul]; constructor
  · intro ⟨hd, hw⟩; apply eq_quadratic_of_degree_le_two at hd; rw [hd] at ⊢ hw; norm_num at hw
    exists w.coeff 2, w.coeff 0; simp; linarith
  · intro ⟨a, b, h⟩; subst h; simp; convert degree_quadratic_le using 3
    rw [left_eq_add]; simp; rfl

theorem Zad6_7c : (w ∈ degreeLE ℝ 2 ∧ w.eval 1 = w.eval 0 ∧ w.eval 0 = w.eval (-1)) ↔
    w ∈ Submodule.span ℝ {1} := by
  simp [Submodule.mem_span_singleton, mem_degreeLE, smul_eq_C_mul]; constructor
  · intro ⟨hd, h1, h2⟩; apply eq_quadratic_of_degree_le_two at hd; rw [hd] at ⊢ h1 h2; norm_num at h1 h2
    exists w.coeff 0; simp [show w.coeff 2 = 0 by linarith]; linarith
  · intro ⟨a, h⟩; subst h; grw [Polynomial.degree_C_le]; simp

theorem Zad6_D1a : !![(1 : ℚ), 2, 1; 2, 1, 3] ∉ Submodule.span ℚ
    {!![1, 3, 1; 2, 5, 3], !![4, 5, 1; 3, 3, 2]} := by simp [Submodule.mem_span_pair]; grind

theorem Zad6_D1b : !![(7 : ℚ), 7, 1; 4, 1, 1] ∈ Submodule.span ℚ
    {!![1, 3, 1; 2, 5, 3], !![4, 5, 1; 3, 3, 2]} := by simp [Submodule.mem_span_pair]; exists -1, 2; norm_num

theorem Zad6_D1c : !![(3 : ℚ), 2, 0; 2, 4, 1] ∉ Submodule.span ℚ
    {!![1, 3, 1; 2, 5, 3], !![4, 5, 1; 3, 3, 2]} := by simp [Submodule.mem_span_pair]; grind

theorem Zad6_D2 {x₁ x₂ x₃ : ZMod 2} : LinearIndependent (ZMod 2) ![![x₁, x₂, x₃], ![1, 0, 1], ![1, 1, 1]] ↔
    x₁ ≠ x₃ := by
  simp [linearIndependent_fin_succ, Fin.tail_def, Submodule.mem_span_singleton, Submodule.mem_span_pair]
  constructor
  · contrapose!; intro h; subst h; exists x₁ - x₂; simp
  · contrapose!; intro ⟨x, h1, h2⟩; exact h1.symm.trans h2

theorem Zad6_D3a : ∀ v, v ∈ Submodule.span ℝ {![(1 : ℝ), 3, 5], ![2, 7, 5], ![1, 1, 9]} := by
  simp [Submodule.mem_span_triple]; intro v
  let x := v 0; let y := v 1; let z := v 2
  exists -29 * x / 3 + 13 * y / 6 + 5 * z / 6, 11 * x / 3 - 2 * y / 3 - z / 3, 10 * x / 3 - 5 * y / 6 - z / 6
  ring_nf; funext i; fin_cases i <;> simp [x, y, z]

theorem Zad6_D3b : ¬∀ v, v ∈ Submodule.span ℝ {![(1 : ℝ), 4, 5], ![3, 2, 1], ![5, 5, 4]} := by
  simp [Submodule.mem_span_triple]; exists ![1, 0, 0]; simp; grind

open Complex in
theorem Zad6_D4 : ![1, I, I] ∈ Submodule.span ℂ {![c, -1+I, 1+I], ![I, -1, -c]} ↔ (c = 1 ∨ c = 1 + I) := by
  simp [Submodule.mem_span_pair]; constructor
  · intro ⟨a, b, h1, h2, h3⟩; by_cases ha : a = 0
    · simp [ha] at *; rw [neg_mul_eq_neg_mul, h2, mul_eq_left₀ (by simp)] at h3; exact Or.inl h3
    · replace h1 := (mul_eq_mul_right_iff (c := I)).mpr (Or.inl h1)
      simp [add_mul, mul_assoc] at h1; nth_rw 2 [← h1] at h2; simp [ha] at h2
      replace h2 := (mul_eq_mul_right_iff (c := -I)).mpr (Or.inl h2); simp [add_mul, mul_assoc] at h2
      right; symm; exact h2
  · apply Or.rec <;> (intro hc; subst hc)
    · exists 0, -I; simp
    · exists (3 - I) / 10, (-1 - 3 * I) / 5; ring_nf; norm_num

open Complex in
theorem Zad6_D5 {x₁ x₂ x₃ x₄ : ℂ} : ![x₁, x₂, x₃, x₄] ∈ Submodule.span ℂ
    {![I, 1, -I, -1], ![I, -I, -1, 1], ![1, 0, 0, -1]} → x₁ + x₂ + x₃ + x₄ = 0 := by
  simp [Submodule.mem_span_triple]; intro a b c h1 h2 h3 h4; subst_vars; ring

theorem Zad6_D6a : ∀ v, v ∈ Submodule.span ℚ {![(1 : ℚ), 1, 1, 1], ![1, 2, 1, 2], ![1, 0, 0, 0], ![0, 1, 0, 0]} := by
  simp [Submodule.mem_span_insert, Submodule.mem_span_singleton]; intro v
  let x := v 0; let y := v 1; let z := v 2; let w := v 3
  exists 2 * z - w, w - z, x - z, y - w; ring_nf; funext i; fin_cases i <;> simp [x, y, z, w]

theorem Zad6_D6b : ∀ v, v ∈ Submodule.span ℚ
    {![(1 : ℚ), 1, 2, 1, 1], ![1, 2, 3, 1, 1], ![1, 2, 4, 2, 1], ![1, 1, 1, 1, 1], ![1, 0, 0, 0, 0]} := by
  simp [Submodule.mem_span_insert, Submodule.mem_span_singleton]; intro v
  let x := v 0; let y := v 1; let z := v 2; let w := v 3; let u := v 4
  exists z - 2 * y - w + 2 * u, y - w, w - u, w + y - z, x - u; ring_nf
  funext i; fin_cases i <;> simp [x, y, z, w, u]

theorem Zad6_D7 {s t : ℝ} : LinearIndependent ℝ ![![5, 7, s, 2], ![1, 3, 2, 1], ![2, 2, 4, t]] ↔
    (s ≠ 10 ∨ t ≠ 1 / 2) := by
  simp [linearIndependent_fin_succ, Fin.tail_def, Submodule.mem_span_singleton, Submodule.mem_span_pair]
  constructor
  · intro ⟨_, h⟩; specialize h 2 1; norm_num at h; convert imp_iff_not_or.mp h using 1 <;> grind
  · intro h; and_intros
    · intro x h1 h2; linarith
    · intro x y h1 h2 h3 h4; revert h; simp; grind

theorem Zad6_D8_W1 {s : ℝ} : Module.finrank ℝ (Submodule.span ℝ
    {![10, 3, 9 + s, 1, 2 - s], ![4, 1, 6, 1, 1], ![2, 1, -1, -1, -2]}) = if s = 2 then 2 else 3 := by
  split
  case isTrue =>
    subst s; rw [Submodule.span_insert_eq_span (by simp [Submodule.mem_span_pair]; exists 2, 1; norm_num)]
    have h : LinearIndependent ℝ ![![(4 : ℝ), 1, 6, 1, 1], ![2, 1, -1, -1, -2]] := by
      simp [linearIndependent_fin_succ, Fin.tail_def, Submodule.mem_span_singleton]
    convert finrank_span_eq_card h <;> simp [Set.pair_comm]
  case isFalse h =>
    have h : LinearIndependent ℝ ![![10, 3, 9 + s, 1, 2 - s], ![(4 : ℝ), 1, 6, 1, 1], ![2, 1, -1, -1, -2]] := by
      simp [linearIndependent_fin_succ, Fin.tail_def, Submodule.mem_span_singleton, Submodule.mem_span_pair]
      grind
    convert finrank_span_eq_card h <;> simp [Set.union_comm]

theorem Zad6_D8_W2 {t : ℝ} : Set.finrank ℝ {x : Fin 5 → ℝ | 3 * x 0 - 11 * x 1 + t * x 2 - 8 * x 3 + x 4 = 0
                                                           ∧ 2 * x 0 -  4 * x 1 -     x 2 + 3 * x 3 - x 4 = 0
                                                           ∧     x 0 -  5 * x 1 +     x 2 - 6 * x 3 + x 4 = 0}
    = if t = 1 then 3 else 2 := by
  split
  case isTrue =>
    subst t
    have h : LinearIndependent ℝ ![![(1 : ℝ), 0, 0, 1, 5], ![0, 1, 0, -3, -13], ![0, 0, 1, 0, -1]] := by
      simp [linearIndependent_fin_succ, Fin.tail_def, Submodule.mem_span_singleton, Submodule.mem_span_pair]
    apply finrank_span_eq_card at h; simp at h; simp [Set.finrank]
    rw [Submodule.span_eq_of_le]; exact h
    · intro x; simp [Submodule.mem_span_triple]; intro h1 h2 h3; exists x 2, x 1, x 0
      ext i; fin_cases i <;> simp <;> grind
    · apply Submodule.span_mono; intro x; simp; intro h; rcases h with h | h | h <;> simp [h] <;> norm_num
  case isFalse ht =>
    have h : LinearIndependent ℝ ![![(1 : ℝ), 0, 0, 1, 5], ![0, 1, 0, -3, -13]] := by
      simp [linearIndependent_fin_succ, Fin.tail_def, Submodule.mem_span_singleton]
    apply finrank_span_eq_card at h; simp at h; simp [Set.finrank]
    rw [Submodule.span_eq_of_le]; exact h
    · intro x; simp [Submodule.mem_span_pair]; intro h1 h2 h3; exists x 1, x 0
      ext i; fin_cases i <;> simp <;> grind
    · apply Submodule.span_mono; intro x; simp; intro h; rcases h with h | h <;> simp [h] <;> norm_num

theorem Zad6_D8 {s t : ℝ} : Submodule.span ℝ {![10, 3, 9 + s, 1, 2 - s], ![4, 1, 6, 1, 1], ![2, 1, -1, -1, -2]}
    = {x : Fin 5 → ℝ | 3 * x 0 - 11 * x 1 + t * x 2 - 8 * x 3 + x 4 = 0
                     ∧ 2 * x 0 -  4 * x 1 -     x 2 + 3 * x 3 - x 4 = 0
                     ∧     x 0 -  5 * x 1 +     x 2 - 6 * x 3 + x 4 = 0} ↔ s ≠ 2 ∧ t = 1 := by
  constructor
  · intro h
    have hi : (if s = 2 then 2 else 3) = if t = 1 then 3 else 2 := by
      rw [← Zad6_D8_W1, ← Zad6_D8_W2, ← h]; simp [Set.finrank]; rw [Submodule.span_span]
    split at hi <;> split at hi <;> (subst_vars; try trivial)
    exfalso; revert h
    simp [Set.ext_iff]; exists ![2, 1, -1, -1, -2]; apply mt Iff.mp; simp; and_intros
    · apply Submodule.mem_span_of_mem; simp
    · intros; grind
  · intro ⟨hs, ht⟩; subst t; simp
    suffices Submodule.span ℝ {![10, 3, 9 + s, 1, 2 - s], ![4, 1, 6, 1, 1], ![2, 1, -1, -1, -2]} =
        Submodule.span ℝ {x | 3 * x 0 - 11 * x 1 + 1 * x 2 - 8 * x 3 + x 4 = 0 ∧ 2 * x 0 - 4 * x 1 - x 2 + 3 * x 3 - x 4 = 0
                            ∧ x 0 - 5 * x 1 + x 2 - 6 * x 3 + x 4 = 0} by
      rw [this]; ext x; simp only [one_mul]; constructor
      · apply Submodule.span_induction; · tauto
        · simp
        · intro x y hxs hys; simp; grind
        · intro a x hxs; simp; grind
      · exact Submodule.mem_span_of_mem
    apply Submodule.eq_of_le_of_finrank_eq
    · apply Submodule.span_mono; intro x; simp; intro h; rcases h with h | h | h <;> (simp [h]; grind)
    · rw [Zad6_D8_W1, ← Set.finrank, Zad6_D8_W2]; simpa

variable {x₁ x₂ x₃ x₄ x₅ : ℝ}

theorem Zad6_D9_V : (x₁ + x₂ + x₃ = 0 ∧ x₂ + x₃ + x₄ = 0) ↔ ![x₁, x₂, x₃, x₄, x₅] ∈ Submodule.span ℝ
    {![1, -1, 0, 1, 0], ![1, 0, -1, 1, 0], ![0, 0, 0, 0, 1]} := by
  simp [Submodule.mem_span_triple]; constructor
  · intro ⟨h1, h2⟩; exists -x₂, -x₃; grind
  · intro ⟨a, b, h1, h2, h3, h4⟩; grind

theorem Zad6_D9_W : (x₁ + x₃ + x₅ = 0 ∧ x₁ + x₂ + x₄ = 0) ↔ ![x₁, x₂, x₃, x₄, x₅] ∈ Submodule.span ℝ
    {![1, -1, -1, 0, 0], ![1, 0, -1, -1, 0], ![1, 0, 0, -1, -1]} := by
  simp [Submodule.mem_span_triple]; constructor
  · intro ⟨h1, h2⟩; exists -x₂, x₂ - x₃, -x₅; grind
  · intro ⟨a, b, h1, h2, h3, h4⟩; grind

theorem Zad6_D9_VW : (x₁ + x₂ + x₃ = 0 ∧ x₂ + x₃ + x₄ = 0 ∧ x₁ + x₃ + x₅ = 0 ∧ x₁ + x₂ + x₄ = 0) ↔
    ![x₁, x₂, x₃, x₄, x₅] ∈ Submodule.span ℝ {![1, -2, 1, 1, -2]} := by
  simp [Submodule.mem_span_singleton]; grind
