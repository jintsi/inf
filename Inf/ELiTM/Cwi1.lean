import Batteries.Tactic.Alias

/-! It should come to no surprise that this file has the least imports in the whole project. -/

namespace Elitm.Cwi1

theorem Zad1a : (False ∧ True ∨ True ∨ False ↔ (False → True)) = True := by simp

theorem Zad1b : (((True → False) ∧ (False → True)) → (False ↔ True)) = True := by simp

theorem Zad1c : ((False → True) → (True → False) ∧ ¬(True → False)) = False := by simp

theorem Zad2a : ((x ∨ y → x ∧ y) ∧ x) = True ↔ x ∧ y := by constructor <;> simp +contextual

theorem Zad2b : (x ∨ y → x ↔ y) = False ↔ ¬x ∨ ¬y := by by_cases x <;> simp [*]

theorem Zad2c : (x ∨ y → x ↔ x) = True ↔ x ∨ y := by simpa using Or.inl

theorem Zad2d : (x ∨ z → y ↔ y ∧ (x ∨ z)) = False ↔ ¬x ∧ ¬z := by by_cases y <;> simp [*]

theorem Zad2e : (¬(u → x ∨ ¬y) ∧ (z ↔ ¬x) ∧ (¬u ↔ v)) = True ↔ ¬x ∧ y ∧ z ∧ u ∧ ¬v := by
  constructor <;> simp +contextual

theorem Zad2f : ((x → y) ∨ (y → z) ∨ (z → t) ∨ (t → x)) = False ↔ False := by simp +contextual

theorem Zad3a : ((p ∨ ¬q) ∧ (¬p ∨ q) ∧ (p ∨ q) ∧ (¬p ∨ ¬q)) = False := by by_cases p <;> simp [*]

theorem Zad3b {p q r : Prop} : ((p → q → r) → (p → q) → p → r) = True := by simp +contextual

theorem Zad3c {p q r : Prop} : (((p → q) → r) → (p → r) → q → r) = True := by simp +contextual

theorem Zad3d : (((p → q) → r → q) → (p → r) → q) = (p ∧ ¬r ∨ ¬p ∧ r ∨ q) := by
  by_cases p <;> by_cases q <;> simp [*]

theorem Zad3e : (((p → q) → ¬(p → r)) → ¬(p → r) → p → q) = (¬p ∨ q ∨ r) := by
  by_cases p <;> by_cases q <;> simp [*]

theorem Zad3f : (((p → ¬q) → ¬p) → p → q → p) = True := by simp +contextual

theorem Zad3g : (¬(p ∨ q ∨ r → ¬p ∧ ¬q ∧ ¬r)) = (p ∨ q ∨ r) := by simp; simp +contextual [or_imp]

theorem Zad3h : (p ∧ q ∧ ¬r ↔ (¬p → ¬q) ∨ r) = (q ∧ ¬r) := by by_cases p <;> simp [*]

def Zad4.Φ : Nat → Prop → Prop
| 0,       _ => True
| .succ n, p => Φ n p → p

theorem Zad4.Φ_even : Φ (2 * n) p = True := by
  induction n with
  | zero => rfl
  | succ n ih => simp [Nat.mul_add, Φ, ih]

theorem Zad4.Φ_odd : Φ (2 * n + 1) p = p := by simp [Φ, Φ_even]

theorem Zad5 {α β γ : Prop} (h : α → ¬β) : α ∧ β → γ := fun x => (h x.1 x.2).elim

alias Zad6 := iff_congr
