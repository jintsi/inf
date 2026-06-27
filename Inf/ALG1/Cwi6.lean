import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.RingTheory.Polynomial.SmallDegreeVieta
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

namespace ALG1.Cwi6

open Submodule

theorem Zad1a : LinearIndependent ℚ ![![(0 : ℚ), 1, 2, -1], ![1, 0, 3, 1], ![0, 2, -1, 4]] := by
  simp [linearIndependent_finSucc, Fin.tail_def, mem_span_singleton, mem_span_pair]
  intros; linarith

theorem Zad1b : ¬LinearIndependent ℚ ![![(1 : ℚ), 2, 0, 3], ![3, -1, 5, 0], ![-1, 5, -5, 6]] := by
  simp [linearIndependent_finSucc, Fin.tail_def, mem_span_singleton, mem_span_pair]
  exists 1 / 2, 1 / 2; norm_num

open Polynomial in
theorem Zad1c : ¬LinearIndependent (M := ℚ[X]) ℚ
    ![X ^ 3 + 1, X ^ 3 - 1, X ^ 2 + X, X ^ 3 + X ^ 2 + X] := by
  simp [Fintype.not_linearIndependent_iff]; exists ![1, 1, 2, -2]; and_intros
  · simp [Fin.sum_univ_succ, smul_eq_C_mul, C_ofNat]; ring
  · exists 0

theorem Zad2 (s : ℚ) :
    LinearIndependent ℚ ![![2, 1, 0, s], ![0, 1, 2, 2], ![0, 1, 1, 2], ![s, 0, 2, s]]
    ↔ (s ≠ 0 ∧ s ≠ 4) := by
  simp [linearIndependent_finSucc, Fin.tail_def, mem_span_singleton, mem_span_pair, mem_span_triple]
  apply and_congr
  · exact ⟨fun h hs => (h hs (1 / 2) (by norm_num)).right hs, Not.elim⟩
  · constructor
    · contrapose!; intro rfl; exists 1 / 2, (by norm_num), 3, -2; norm_num
    · grind only

theorem Zad3a : LinearIndependent ℝ ![id, Real.sin, Real.cos] := by
  simp [linearIndependent_finSucc, Fin.tail_def, mem_span_singleton, mem_span_pair, funext_iff]
  and_intros
  · exists 0; simp
  · intro x; exists Real.pi / 2; simp
  · intro x y; by_cases x = 0
    · subst x; exists Real.pi; simpa using Real.pi_ne_zero.symm
    · exists 0; simpa

theorem Zad3b : LinearIndependent ℝ
    ![Real.sin, Real.cos, fun r => Real.sin (2 * r), fun r => Real.cos (2 * r)] := by
  simp [linearIndependent_finSucc, Fin.tail_def, mem_span_singleton, mem_span_pair,
        mem_span_triple, funext_iff, Real.sin_two_mul, Real.cos_two_mul]; and_intros
  · exists 0; norm_num
  · intro x; by_cases x = 0
    · subst x; exists Real.pi / 3; simp
    · exists 0; norm_num; assumption
  · intro x y; by_cases x = 0
    · subst x; exists 0; simp
    · exists Real.pi / 2; simpa
  · intro x y z; by_cases x = -1
    · by_cases z = 1
      · exists Real.pi; subst x z; norm_num
      · exists 0; subst x; norm_num; grind only
    · exists Real.pi / 2; simp; rwa [neg_eq_iff_eq_neg]

theorem Zad3c : ¬LinearIndependent ℝ
    ![fun r => Real.cos (2 * r), fun r => r.sin ^ 2, fun r => r.cos ^ 2] := by
  simp [Fintype.not_linearIndependent_iff, Real.cos_two_mul']; exists ![1, 1, -1]; and_intros
  · simp [Fin.sum_univ_succ, Pi.add_def, funext_iff]; intro x; ring_nf
  · exists 0; simp

theorem Zad3d (n : ℕ) : LinearIndependent ℝ fun (i : Fin n) (x : ℝ) => ∏ k : Fin i, |x - k| := by
  induction n
  case zero => simp
  case succ n ih =>
    simp [linearIndependent_finSucc', Fin.init_def, mem_span_range_iff_exists_fun, funext_iff]
    exists ih; intro c; by_cases h : c = 0
    · exists n; simp [h]; apply Ne.symm; simp [Finset.prod_ne_zero_iff, ne_of_gt]
    rcases n with rfl | n; · simp
    contrapose! h with this; simp [funext_iff, Fin.forall_iff, -Order.lt_add_one_iff]; intro i hi
    induction i using Nat.strong_induction_on; rename_i i ih
    replace ih := fun m h => ih m h (h.trans hi); let i := Fin.mk i hi
    specialize this i; rw [Finset.prod_eq_zero (i := i) (by simp) (by simp)] at this
    apply Finset.eq_zero_of_sum_eq_zero (a := i) at this; simp at this
    refine (this ?_ i).resolve_right (Finset.prod_ne_zero_iff.mpr fun k _ => by simp [ne_of_gt])
    intro j hj; cases lt_or_gt_of_ne hj
    case inl hj => left; exact ih j hj
    case inr hj => right; exact Finset.prod_eq_zero (i := ⟨i, hj⟩) (by simp) (by simp)

theorem Zad4 (r : ℚ) : ![r, 8, 6] ∈ span ℚ {![3, 4, 5], ![1, 4, 4], ![7, 4, 7]} ↔ r = -2 := by
  simp [mem_span_triple]; constructor
  · intro ⟨a, b, c, h1, h2, h3⟩; linarith
  · intro rfl; exists -2, 4, 0; norm_num

variable {x₁ x₂ x₃ x₄ : ℚ}

theorem Zad5a : 2 * x₁ + x₂ - 2 * x₃ - x₄ = 0 ↔ ![x₁, x₂, x₃, x₄] ∈ span ℚ
    {![1, 0, 0, 2], ![0, 1, 0, 1], ![0, 0, 1, -2]} := by simp [mem_span_triple]; grind only

theorem Zad5b : (x₁ + x₂ - x₃ = 0 ∧ x₁ + 2 * x₂ + x₄ = 0) ↔ ![x₁, x₂, x₃, x₄] ∈ span ℚ
    {![1, 0, 1, -1], ![0, 1, 1, -2]} := by simp [mem_span_pair]; grind only

theorem Zad5c : (x₁ - x₂ = 0 ∧ x₂ - x₃ = 0 ∧ x₃ - x₄ = 0) ↔ ![x₁, x₂, x₃, x₄] ∈ span ℚ
    {![1, 1, 1, 1]} := by simp [mem_span_singleton]; grind only

theorem Zad5d : (x₁ + x₂ = 0 ∧ x₂ + x₃ = 0 ∧ x₃ + x₄ = 0 ∧ x₁ + x₄ = 0)
    ↔ ![x₁, x₂, x₃, x₄] ∈ span ℚ {![1, -1, 1, -1]} := by simp [mem_span_singleton]; grind only

open Polynomial

theorem Zad7a : (w ∈ degreeLE ℝ 2 ∧ w.eval 1 = w.eval 2) ↔ w ∈ span ℝ {X ^ 2 - 3 * X, 1} := by
  simp [mem_span_pair, mem_degreeLE, smul_eq_C_mul]; constructor
  · intro ⟨hd, hw⟩; apply eq_quadratic_of_degree_le_two at hd; rw [hd] at ⊢ hw; norm_num at hw
    exists w.coeff 2, w.coeff 0; simp [sub_eq_add_neg, mul_add, ← mul_assoc, ← neg_mul]
    convert congrArg C (by linarith : w.coeff 2 * -3 = w.coeff 1); simp; left; rfl
  · rintro ⟨a, b, rfl⟩; norm_num; compute_degree

theorem Zad7b : (w ∈ degreeLE ℝ 2 ∧ w.eval 1 = w.eval (-1)) ↔ w ∈ span ℝ {X ^ 2, 1} := by
  simp [mem_span_pair, mem_degreeLE, smul_eq_C_mul]; constructor
  · intro ⟨hd, hw⟩; apply eq_quadratic_of_degree_le_two at hd; rw [hd] at ⊢ hw; norm_num at hw
    exists w.coeff 2, w.coeff 0; simp; linarith
  · rintro ⟨a, b, rfl⟩; simp; compute_degree

theorem Zad7c : (w ∈ degreeLE ℝ 2 ∧ w.eval 1 = w.eval 0 ∧ w.eval 0 = w.eval (-1)) ↔
    w ∈ span ℝ {1} := by
  simp [mem_span_singleton, mem_degreeLE, smul_eq_C_mul]; constructor
  · intro ⟨hd, h1, h2⟩; apply eq_quadratic_of_degree_le_two at hd; rw [hd] at ⊢ h1 h2
    norm_num at h1 h2; exists w.coeff 0; simp [show w.coeff 2 = 0 by linarith]; linarith
  · rintro ⟨a, rfl⟩; grw [Polynomial.degree_C_le]; simp

theorem ZadD1a : !![(1 : ℚ), 2, 1; 2, 1, 3] ∉ span ℚ
    {!![1, 3, 1; 2, 5, 3], !![4, 5, 1; 3, 3, 2]} := by simp [mem_span_pair]; grind only

theorem ZadD1b : !![(7 : ℚ), 7, 1; 4, 1, 1] ∈ span ℚ
    {!![1, 3, 1; 2, 5, 3], !![4, 5, 1; 3, 3, 2]} := by simp [mem_span_pair]; exists -1, 2; norm_num

theorem ZadD1c : !![(3 : ℚ), 2, 0; 2, 4, 1] ∉ span ℚ
    {!![1, 3, 1; 2, 5, 3], !![4, 5, 1; 3, 3, 2]} := by simp [mem_span_pair]; grind only

theorem ZadD2 {x₁ x₂ x₃ : ZMod 2} :
    LinearIndependent (ZMod 2) ![![x₁, x₂, x₃], ![1, 0, 1], ![1, 1, 1]] ↔ x₁ ≠ x₃ := by
  simp [linearIndependent_finSucc, Fin.tail_def, mem_span_singleton, mem_span_pair]
  constructor
  · contrapose!; intro rfl; exists x₁ - x₂; simp
  · contrapose!; rintro ⟨x, rfl, rfl⟩; rfl

theorem ZadD3a : ∀ v, v ∈ span ℝ {![(1 : ℝ), 3, 5], ![2, 7, 5], ![1, 1, 9]} := by
  simp [mem_span_triple]; intro v
  exists -29 * v 0 / 3 + 13 * v 1 / 6 + 5 * v 2 / 6, 11 * v 0 / 3 - 2 * v 1 / 3 - v 2 / 3,
    10 * v 0 / 3 - 5 * v 1 / 6 - v 2 / 6
  funext i; fin_cases i <;> simp <;> ring

theorem ZadD3b : ¬∀ v, v ∈ span ℝ {![(1 : ℝ), 4, 5], ![3, 2, 1], ![5, 5, 4]} := by
  simp [mem_span_triple]; exists ![1, 0, 0]; simp; grind

open Complex in
theorem ZadD4 : ![1, I, I] ∈ span ℂ {![c, -1+I, 1+I], ![I, -1, -c]} ↔ (c = 1 ∨ c = 1 + I) := by
  simp [mem_span_pair]; constructor
  · intro ⟨a, b, h1, h2, h3⟩; by_cases ha : a = 0
    · simp [ha] at *; rw [neg_mul_eq_neg_mul, h2, mul_eq_left₀ I_ne_zero] at h3; exact Or.inl h3
    · replace h1 := (mul_eq_mul_right_iff (c := I)).mpr (Or.inl h1)
      simp [add_mul, mul_assoc] at h1; nth_rw 2 [← h1] at h2; simp [ha] at h2
      replace h2 := (mul_eq_mul_right_iff (c := -I)).mpr (Or.inl h2)
      simp [add_mul, mul_assoc] at h2; exact Or.inr h2.symm
  · rintro (rfl | rfl)
    · exists 0, -I; simp
    · exists (3 - I) / 10, (-1 - 3 * I) / 5; ring_nf; norm_num

open Complex in
theorem ZadD5 {x₁ x₂ x₃ x₄ : ℂ} : ![x₁, x₂, x₃, x₄] ∈ span ℂ
    {![I, 1, -I, -1], ![I, -I, -1, 1], ![1, 0, 0, -1]} → x₁ + x₂ + x₃ + x₄ = 0 := by
  simp [mem_span_triple]; intro a b c rfl rfl rfl rfl; ring

theorem ZadD6a :
    ∀ v, v ∈ span ℚ {![(1 : ℚ), 1, 1, 1], ![1, 2, 1, 2], ![1, 0, 0, 0], ![0, 1, 0, 0]} := by
  simp [mem_span_insert, mem_span_singleton]; intro v
  exists 2 * v 2 - v 3, v 3 - v 2, v 0 - v 2, v 1 - v 3; funext i; fin_cases i <;> simp <;> ring

theorem ZadD6b : ∀ v, v ∈ span ℚ {![(1 : ℚ), 1, 2, 1, 1], ![1, 2, 3, 1, 1], ![1, 2, 4, 2, 1],
    ![1, 1, 1, 1, 1], ![1, 0, 0, 0, 0]} := by
  simp [mem_span_insert, mem_span_singleton]; intro v
  exists v 2 - 2 * v 1 - v 3 + 2 * v 4, v 1 - v 3, v 3 - v 4, v 3 + v 1 - v 2, v 0 - v 4
  funext i; fin_cases i <;> simp <;> ring

theorem ZadD7 {s t : ℝ} : LinearIndependent ℝ ![![5, 7, s, 2], ![1, 3, 2, 1], ![2, 2, 4, t]] ↔
    (s ≠ 10 ∨ t ≠ 1 / 2) := by
  simp [linearIndependent_finSucc, Fin.tail_def, mem_span_singleton, mem_span_pair]
  constructor
  · intro ⟨_, h⟩; specialize h 2 1; grind only
  · intro h; and_intros
    · intro x h1 h2; linarith
    · grind only

theorem ZadD8_W1 {s : ℝ} :
    Module.finrank ℝ (span ℝ {![10, 3, 9 + s, 1, 2 - s], ![4, 1, 6, 1, 1], ![2, 1, -1, -1, -2]})
    = if s = 2 then 2 else 3 := by
  split_ifs with h
  case pos =>
    subst s; rw [span_insert_eq_span (by simp [mem_span_pair]; exists 2, 1; norm_num)]
    have h : LinearIndependent ℝ ![![(4 : ℝ), 1, 6, 1, 1], ![2, 1, -1, -1, -2]] := by
      simp [linearIndependent_finSucc, Fin.tail_def, mem_span_singleton]
    convert finrank_span_eq_card h <;> simp [Set.pair_comm]
  case neg =>
    have h : LinearIndependent ℝ ![![10, 3, 9 + s, 1, 2 - s],
        ![(4 : ℝ), 1, 6, 1, 1], ![2, 1, -1, -1, -2]] := by
      simp [linearIndependent_finSucc, Fin.tail_def, mem_span_singleton, mem_span_pair]
      grind only
    convert finrank_span_eq_card h <;> simp [Set.union_comm]

theorem ZadD8_W2 {t : ℝ} :
    Set.finrank ℝ {x : Fin 5 → ℝ | 3 * x 0 - 11 * x 1 + t * x 2 - 8 * x 3 + x 4 = 0
                                 ∧ 2 * x 0 -  4 * x 1 -     x 2 + 3 * x 3 - x 4 = 0
                                 ∧     x 0 -  5 * x 1 +     x 2 - 6 * x 3 + x 4 = 0}
    = if t = 1 then 3 else 2 := by
  split
  case isTrue =>
    subst t
    have h : LinearIndependent ℝ ![![(1 : ℝ), 0, 0, 1, 5],
        ![0, 1, 0, -3, -13], ![0, 0, 1, 0, -1]] := by
      simp [linearIndependent_finSucc, Fin.tail_def, mem_span_singleton, mem_span_pair]
    apply finrank_span_eq_card at h; simp at h; simp [Set.finrank]
    rw [span_eq_of_le]; exact h
    · intro x; simp [mem_span_triple]; intro h1 h2 h3; exists x 2, x 1, x 0
      ext i; fin_cases i <;> simp <;> grind
    · apply span_mono; intro x; simp; intro h; rcases h with h | h | h <;> simp [h] <;> norm_num
  case isFalse ht =>
    have h : LinearIndependent ℝ ![![(1 : ℝ), 0, 0, 1, 5], ![0, 1, 0, -3, -13]] := by
      simp [linearIndependent_finSucc, Fin.tail_def, mem_span_singleton]
    apply finrank_span_eq_card at h; simp at h; simp [Set.finrank]
    rw [span_eq_of_le]; exact h
    · intro x; simp [mem_span_pair]; intro h1 h2 h3; exists x 1, x 0
      ext i; fin_cases i <;> simp <;> grind
    · apply span_mono; intro x; simp; intro h; rcases h with h | h <;> simp [h] <;> norm_num

theorem Zad6_D8 {s t : ℝ} :
    span ℝ {![10, 3, 9 + s, 1, 2 - s], ![4, 1, 6, 1, 1], ![2, 1, -1, -1, -2]}
    = {x : Fin 5 → ℝ | 3 * x 0 - 11 * x 1 + t * x 2 - 8 * x 3 + x 4 = 0
                     ∧ 2 * x 0 -  4 * x 1 -     x 2 + 3 * x 3 - x 4 = 0
                     ∧     x 0 -  5 * x 1 +     x 2 - 6 * x 3 + x 4 = 0} ↔ s ≠ 2 ∧ t = 1 := by
  constructor
  · intro h
    have hi : (if s = 2 then 2 else 3) = if t = 1 then 3 else 2 := by
      rw [← ZadD8_W1, ← ZadD8_W2, ← h]; simp [Set.finrank]; rw [span_span]
    split at hi <;> split at hi <;> (subst_vars; try trivial)
    exfalso; revert h
    simp [Set.ext_iff]; exists ![2, 1, -1, -1, -2]; apply mt Iff.mp; simp; and_intros
    · apply mem_span_of_mem; simp
    · intros; grind
  · rintro ⟨hs, rfl⟩; simp
    suffices span ℝ {![10, 3, 9 + s, 1, 2 - s], ![4, 1, 6, 1, 1], ![2, 1, -1, -1, -2]} =
        span ℝ {x | 3 * x 0 - 11 * x 1 + 1 * x 2 - 8 * x 3 + x 4 = 0
        ∧ 2 * x 0 - 4 * x 1 - x 2 + 3 * x 3 - x 4 = 0 ∧ x 0 - 5 * x 1 + x 2 - 6 * x 3 + x 4 = 0} by
      rw [this]; ext x; simp only [one_mul]; constructor
      · apply span_induction; · tauto
        · simp
        · intro x y hxs hys; simp; grind only
        · intro a x hxs; simp; grind only
      · exact mem_span_of_mem
    apply eq_of_le_of_finrank_eq
    · apply span_mono; intro x; simp; intro h; rcases h with h | h | h <;> (simp [h]; grind only)
    · rw [ZadD8_W1, ← Set.finrank, ZadD8_W2]; simpa

variable {x₁ x₂ x₃ x₄ x₅ : ℝ}

theorem ZadD9_V : (x₁ + x₂ + x₃ = 0 ∧ x₂ + x₃ + x₄ = 0) ↔
    ![x₁, x₂, x₃, x₄, x₅] ∈ span ℝ {![1, -1, 0, 1, 0], ![1, 0, -1, 1, 0], ![0, 0, 0, 0, 1]} := by
  simp [mem_span_triple]; constructor
  · intro ⟨h1, h2⟩; exists -x₂, -x₃; grind only
  · intro ⟨a, b, h1, h2, h3, h4⟩; grind only

theorem ZadD9_W : (x₁ + x₃ + x₅ = 0 ∧ x₁ + x₂ + x₄ = 0) ↔ ![x₁, x₂, x₃, x₄, x₅] ∈ span ℝ
    {![1, -1, -1, 0, 0], ![1, 0, -1, -1, 0], ![1, 0, 0, -1, -1]} := by
  simp [mem_span_triple]; constructor
  · intro ⟨h1, h2⟩; exists -x₂, x₂ - x₃, -x₅; grind only
  · intro ⟨a, b, h1, h2, h3, h4⟩; grind only

theorem ZadD9_VW : (x₁ + x₂ + x₃ = 0 ∧ x₂ + x₃ + x₄ = 0 ∧ x₁ + x₃ + x₅ = 0 ∧ x₁ + x₂ + x₄ = 0) ↔
    ![x₁, x₂, x₃, x₄, x₅] ∈ span ℝ {![1, -2, 1, 1, -2]} := by
  simp [mem_span_singleton]; grind only
