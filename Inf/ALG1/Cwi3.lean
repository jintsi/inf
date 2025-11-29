import Mathlib.Tactic

namespace ALG1

variable {x y z t x1 x2 x3 x4 x5 x6 : ℚ}

theorem Zad3_1a : 2 * x - y - z = 4 ∧ 3 * x + 4 * y - 2 * z = 11 ∧ 3 * x + 2 * y + 4 * z = 11 ↔
    x = 21 / 8 ∧ y = 15 / 16 ∧ z = 5 / 16 := by grind

theorem Zad3_1b : x1 + x2 + 2 * x3 + 3 * x4 = 1 ∧ 3 * x1 + 2 * x2 - x3 - 2 * x4 = 1 ∧ 2 * x1 + 2 * x2 + x3 = 2 ↔
    x1 = -2 * x4 - 1 ∧ x2 = 3 * x4 + 2 ∧ x3 = -2 * x4 := by grind

theorem Zad3_1c : 8 * x1 + 6 * x2 + 5 * x3 + 2 * x4 = 21 ∧ 3 * x1 + 3 * x2 + 2 * x3 + x4 = 10 ∧
                  4 * x1 + 2 * x2 + 3 * x3 +     x4 = 8  ∧ 3 * x1 + 5 * x2 +     x3 + x4 = 14 ∧
                  7 * x1 + 4 * x2 + 5 * x3 + 2 * x4 = 18 ↔ False := by grind

theorem Zad3_3 {x y z : ZMod 11} : x + 3 * y - z = 0 ∧ 2 * x + 7 * y + 4 * z = 3 ∧ 3 * x + 7 * y + 4 * z = 6 ↔
    (x = 3 ∧ y = 5 ∧ z = 7) := by
  grind
