import Mathlib.Algebra.Order.Ring.Unbundled.Basic

namespace Elitm.Cwi2

theorem Zad1a [Semiring R] [LinearOrder R] [ExistsAddOfLE R] [PosMulMono R] [AddLeftMono R] :
    ¬∃ y : R, y ^ 2 < 0 := by simp [sq_nonneg]

theorem Zad1b [MulOneClass M] : ∀ x : M, ∃ y, x * y = x := fun x => ⟨1, mul_one x⟩

theorem Zad1c [MulZeroClass M₀] : ∀ x : M₀, ∃ y, x * y = y := fun x => ⟨0, mul_zero x⟩

theorem Zad1d [MulOneClass M] : ∃ y : M, ∀ x, x * y = x := ⟨1, mul_one⟩

theorem Zad1e [MulZeroClass M₀] : ∃ y : M₀, ∀ x, x * y = y := ⟨0, mul_zero⟩

theorem Zad1f [MulZeroClass M₀] [One M₀] [NeZero (1 : M₀)] : ¬(∀ x : M₀, ∃ y, x * y = 1) := by
  intro h; simpa using h 0

theorem Zad1g [MulZeroClass M₀] : ∃ y : M₀, ∀ x, x * y = 0 := ⟨0, mul_zero⟩

theorem Zad1h [MulZeroClass M₀] [One M₀] [NeZero (1 : M₀)] : ¬(∃ y : M₀, ∀ x, x * y = 1) := by
  intro ⟨y, h⟩; simpa using h 0

theorem Zad1i [MulZeroClass M₀] [OfNat M₀ 7] [NeZero (7 : M₀)] {y : M₀} :
    ¬(∀ x : M₀, x * y = 7) := by intro h; simpa [NeZero.ne'] using h 0

theorem Zad1j [Zero α] [LT α] : ∀ x ∈ (∅ : Set α), 0 < x := by simp

alias Zad2a := forall_imp
alias Zad2b := forall_congr'
alias ⟨Zad2c, _⟩ := forall_imp_iff_exists_imp

theorem Zad4 {p q : α → Prop} : ((∀ x, p x) → ∃ x, q x) ↔ ∃ x, p x → q x where
  mp h := by
    by_cases! hp : ∀ x, p x
    · specialize h hp; rcases h with ⟨x, h⟩; exact ⟨x, fun _ => h⟩
    · rcases hp with ⟨x, hx⟩; exact ⟨x, fun h => (hx h).elim⟩
  mpr := fun ⟨x, hx⟩ hp => ⟨x, hx (hp x)⟩

theorem Zad5a [Nonempty X] [Nonempty Y] {p : X → Y → Prop} :
    ((∀ x, ∃ y, p x y) → ∃ y, ∀ x, p x y) ↔ ∃ x, ∀ y, ∃ y', ∀ x', (p x y → p x' y') := by
  contrapose!; simp [forall_and_left, forall_and_right]

theorem Zad5b [Nonempty X] {p q : X → Prop} :
    ((∃ x, p x → q x) → (∃ x, p x) → ∃ x, q x) ↔ ∀ x y, ∃ z, (p x → q x) → p y → q z := by
  contrapose!; simp [forall_and_left]

theorem Zad5c [Nonempty X] {p : X → Prop} {q : X → Y → Prop} {y : Y} :
    ((∃ x, p x) ↔ ∀ x, q x y) ↔ ∀ x x', ∃ x'' x''', (p x → q x' y) ∧ (q x'' y → p x''') := by
  contrapose! +distrib; simp [forall_or_left, forall_and, exists_or]; tauto

theorem Zad6 {p q : X → Y → Z → Prop} : ¬(∀ x, ∃ y, ∀ z, (p x y z → q x y z) ∨ q x y z) ↔
    ∃ x, ∀ y, ∃ z, p x y z ∧ ¬q x y z := by simp

alias Zad7a := forall₂_and
alias Zad7b := not_exists_mem
