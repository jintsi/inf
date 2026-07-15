import Mathlib.Analysis.Real.Sqrt
import Mathlib.SetTheory.ZFC.Basic

namespace Elitm.Cwi3

open Real in
theorem Zad1 : Finset.card (α := Set ℝ) {{1, 2, 3, 1, 3, 2, 4}, {1, 3, 4, √4, 2 * 3},
    {9 / 3, 2, 3, 4, (-1) ^ 2, 3 + 1}, {1, 2, 3, 4}} = 2 := by
  norm_num [show √4 = 2 by rw [sqrt_eq_iff_eq_sq] <;> norm_num]
  rw [Finset.card_insert_of_mem, Finset.card_insert_of_notMem, Finset.card_insert_of_mem]; simp
  · simp; ext; simp; tauto
  · simp [Set.ext_iff]; use! 6; simp; use! 6; simp
  · simp; right; right; ext; simp; tauto

theorem Zad3a : ¬{∅, {∅}} ⊆ ({∅, {{∅}}, {{∅, {∅}}}} : ZFSet.{u}) := by
  simp [ZFSet.subset_def, eq_comm (a := ∅)]
  and_intros <;> rw [ZFSet.eq_empty] <;> simp; use ∅; simp

theorem Zad3b : {∅, {∅}} ∈ ({∅, {{∅}}, {∅, {∅}}} : ZFSet.{u}) := by simp

theorem Zad3c : ¬{∅, {∅}} ⊆ ({∅, {{∅}}, {∅, {∅}}} : ZFSet.{u}) := by
  simp [ZFSet.subset_def, eq_comm (a := ∅)]; rw [ZFSet.eq_empty]; simp

theorem Zad3d : ¬{∅, {∅}} ∈ ({∅, {{∅}}, {{∅, {∅}}}} : ZFSet.{u}) := by
  simp [eq_comm (a := ∅)]; simp_rw [ZFSet.eq_empty]; simp; use ∅; simp

theorem Zad3e : ¬{∅, {{∅}}} ∈ ({∅, {{∅}}, {{∅, {∅}}}} : ZFSet.{u}) := by
  simp [eq_comm (a := ∅)]; simp_rw [ZFSet.eq_empty]; simp; use ∅; simp

theorem Zad5 : ∀ x ∈ ({∅, {∅}} : ZFSet.{u}), x ⊆ {∅, {∅}} := by simp [ZFSet.subset_def]

theorem Zad6a : ¬∀ a A B : ZFSet.{u}, a ∈ A → A ∈ B → a ∈ B := by
  simp; use ∅, {∅}, ZFSet.mem_singleton.mpr rfl, {{∅}}; simp; rw [eq_comm, ZFSet.eq_empty]; simp

theorem Zad6b {A B : Set α} : a ∈ A → A = B → a ∈ B := by intro h rfl; assumption

theorem Zad6c [Nontrivial α] : ¬∀ a, ∀ A B : Set α, a ∈ A → A ≠ B → a ∉ B := by
  have ⟨a, b, hab⟩ := exists_pair_ne α
  simp; use a, {a}, Set.mem_singleton a, {a, b}, (by simpa [Set.ext_iff] using hab.symm); simp

theorem Zad6d [Nontrivial α] : ¬∀ a, ∀ A B : Set α, a ∉ A → A ≠ B → a ∈ B := by
  have ⟨a, b, hab⟩ := exists_pair_ne α
  simp; use a, ∅, Set.notMem_empty a, {b}, Set.empty_ne_singleton b; simpa

alias Zad6e := Set.mem_of_subset_of_mem

theorem Zad6f [Nonempty α] : ¬∀ a A, ∀ B : Set (Set α), a ⊆ A → A ∈ B → a ∈ B := by
  have a := Classical.arbitrary α
  simp; use ∅, {a}, Set.empty_subset {a}, {{a}}, Set.mem_singleton {a}; simp

alias Zad7a := Set.union_eq_left
alias ⟨_, Zad7c⟩ := Set.union_subset_iff
alias ⟨_, Zad7d⟩ := Set.subset_inter_iff
alias ⟨_, Zad7e⟩ := Set.subset_sdiff

theorem Zad7f {s t u : Set α} : s ∩ t ⊆ u ↔ s ⊆ tᶜ ∪ u := by
  simp [Set.subset_def, ← imp_iff_not_or]

alias Zad7g := Set.sdiff_subset_iff
alias Zad8a := Set.disjoint_iff_inter_eq_empty
alias Zad8b := Set.sdiff_eq_empty
alias Zad8c := sdiff_eq_sdiff_iff

theorem Zad9a {a b c : Set α} : a \ (b \ c ∪ c \ b) = a ∩ (b ∪ cᶜ) ∩ (c ∪ bᶜ) := by tauto_set

theorem Zad9b {a b c : Set α} : a \ c ∪ b ∩ c = (a ∪ c) ∩ (b ∪ a) ↔ a ∩ c ⊆ b := by
  simp [Set.ext_iff, Set.subset_def]; congr!; tauto

theorem Zad9c {a b c : Set α} : a ∪ b \ c = (a ∪ b) \ c ∪ (a ∩ c) := by tauto_set

theorem Zad9d {a b c : Set α} : (a ∩ b) \ c ∪ (a ∩ c) \ b = (a ∩ (b ∪ c)) \ (b ∩ c) := by tauto_set

theorem Zad9e {a b c d : Set α} : (a ∪ d) ∩ c ∪ b \ d = a \ d ∩ c ∪ b \ d ↔ Disjoint d c := by
  simp [Set.disjoint_iff, Set.ext_iff]; congr!; tauto

theorem Zad9f {a b c d : Set α} : ((a ∩ d ∪ c) ∩ b) \ d = (a \ d ∪ c) ∩ (b \ d) ↔ a ∩ b ⊆ c ∪ d := by
  simp [Set.ext_iff, Set.subset_def]; congr!; tauto

theorem Zad9g {a b c d : Set α} : (a ∩ b ∪ c \ d) ∩ (d \ a) = (c ∩ d) \ (a ∪ b) ↔ c ∩ d ⊆ a ∪ b := by
  simp [Set.ext_iff, Set.subset_def]; congr!; tauto

alias Zad9h := Set.prod_union
alias Zad9i := Set.prod_inter

theorem Zad9j {s : Set α} {t₁ t₂ : Set β} : s ×ˢ (t₁ \ t₂) = s ×ˢ t₁ \ s ×ˢ t₂ := by
  ext x; simp; tauto

theorem Zad9k {a x : Set α} {b y : Set β} (ha : a ⊆ x) (hb : b ⊆ y) :
    a ×ˢ y ∩ x ×ˢ b = a ×ˢ b := by rw [Set.prod_inter_prod]; congr <;> simpa

theorem Zad9l {a b : Set α} : a ×ˢ b = b ×ˢ a ↔ a = b ∨ a = ∅ ∨ b = ∅ := by
  simp [Set.prod_eq_prod_iff, eq_comm, or_comm]

alias Zad9n := Set.powerset_inter

theorem Zad9o {s t : Set α} : 𝒫 (s ∪ t) = 𝒫 s ∪ 𝒫 t ↔ s ⊆ t ∨ t ⊆ s := by
  constructor
  · contrapose!; simp [Set.subset_def, Set.ext_iff]
    intro a has hat b hbt hbs; use {a, b}; simp [iff_def, *]
  · rintro (h | h); rw [s.union_comm, (𝒫 s).union_comm]; all_goals
    rw [Set.union_eq_self_of_subset_right h, Set.union_eq_self_of_subset_right]; simpa

alias Zad10a := Set.symmDiff_eq_empty

theorem Zad10b {a b c : Set α} : symmDiff a c ⊆ symmDiff a b ∪ symmDiff b c :=
  symmDiff_triangle a b c

alias Zad10c := symmDiff_assoc

theorem Zad10d {a b  : Set α} : symmDiff a b ∪ a ∩ b = a ∪ b := by tauto_set

alias Zad12 := Set.compl_prod_eq_union
