import Mathlib.Algebra.Field.Basic
import Mathlib.Data.ZMod.Basic

namespace ALG1.Cwi3

variable [Field K] [CharZero K] {x y z t x₁ x₂ x₃ x₄ x₅ : K}

theorem Zad1a : 2 * x - y - z = 4 ∧ 3 * x + 4 * y - 2 * z = 11 ∧ 3 * x + 2 * y + 4 * z = 11 ↔
    x = 21 / 8 ∧ y = 15 / 16 ∧ z = 5 / 16 := by grind only

theorem Zad1b :
    x₁ + x₂ + 2 * x₃ + 3 * x₄ = 1 ∧ 3 * x₁ + 2 * x₂ - x₃ - 2 * x₄ = 1 ∧ 2 * x₁ + 2 * x₂ + x₃ = 2 ↔
    x₁ = -2 * x₄ - 1 ∧ x₂ = 3 * x₄ + 2 ∧ x₃ = -2 * x₄ := by grind only

theorem Zad1c : 8 * x₁ + 6 * x₂ + 5 * x₃ + 2 * x₄ = 21 ∧ 3 * x₁ + 3 * x₂ + 2 * x₃ + x₄ = 10 ∧
                4 * x₁ + 2 * x₂ + 3 * x₃ +     x₄ = 8  ∧ 3 * x₁ + 5 * x₂ +     x₃ + x₄ = 14 ∧
                7 * x₁ + 4 * x₂ + 5 * x₃ + 2 * x₄ = 18 ↔ False := by grind only

theorem Zad1d [NonUnitalNonAssocRing R] {x₁ x₂ x₃ x₄ x₅ x₆ : R} :
    x₁ - x₃ + x₅ = 0 ∧ x₂ - x₄ + x₆ = 0 ∧ x₁ - x₂ + x₅ - x₆ = 0 ∧
    x₂ - x₃ + x₆ = 0 ∧ x₁ - x₄ + x₅ = 0 ↔ x₃ = x₄ ∧ x₁ + x₅ = x₃ ∧ x₂ + x₆ = x₃ := by grind only

theorem Zad1e : 2 * x - y + 3 * z = 9 ∧ 3 * x - 5 * y + z = -4 ∧ 4 * x - 7 * y + z = 5 ↔
    False := by grind only

theorem Zad1f : x₁ + 2 * x₂ + 3 * x₃ - 2 * x₄ +     x₅ = 4 ∧
            3 * x₁ + 6 * x₂ + 5 * x₃ - 4 * x₄ + 3 * x₅ = 5 ∧
                x₁ + 2 * x₂ + 7 * x₃ - 4 * x₄ +     x₅ = 11 ∧
            2 * x₁ + 4 * x₂ + 2 * x₃ - 3 * x₄ + 3 * x₅ = 6 ↔
            x₁ + 2 * x₂ + x₃ + 9 / 2 = 0 ∧ x₄ = 2 * x₃ - 7 / 2 ∧ x₅ = x₄ + 5 := by grind only

theorem Zad1g : -6 * x + 9 * y + 3 * z + 2 * t = 4 ∧ -2 * x + 3 * y + 5 * z + 4 * t = 2 ∧
                -4 * x + 6 * y + 4 * z + 3 * t = 3 ↔
                 6 * z + 5 * t = 1 ∧ y = (2 * x + z + t + 1) / 3 := by grind only

theorem Zad1h : x + y + 2 * z + 3 * t = 1 ∧ 3 * x - y - z - 2 * t = -4 ∧
    2 * x + 3 * y - z - t = -6 ∧ x + 2 * y + 3 * z - t = -4 ↔
    x = -1 ∧ y = -1 ∧ z = 0 ∧ t = 1 := by grind only

theorem Zad1i : x + 2 * y + 3 * z - 2 * t = 6 ∧ 2 * x - y - 2 * z - 3 * t = 8 ∧
    3 * x - y + 2 * z + 2 * t = 4 ∧ 2 * x - 3 * y + 2 * z + t = -8 ↔
    x = 4 ∧ y = 4 ∧ z = -2 ∧ t = 0 := by grind only

theorem Zad3 {x y z : ZMod 11} :
    x + 3 * y - z = 0 ∧ 2 * x + 7 * y + 4 * z = 3 ∧ 3 * x + 7 * y + 4 * z = 6 ↔
    (x = 3 ∧ y = 5 ∧ z = 7) := by grind only
