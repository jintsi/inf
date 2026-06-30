import Mathlib.LinearAlgebra.Matrix.Defs

/-- Replaces the element at index `i` with the result of applying `f` to it. If the index is
invalid, returns the vector unchanged.

TODO: upstream this? -/
@[inline] def Vector.modify (xs : Vector α n) (i : ℕ) (f : α → α) : Vector α n :=
  ⟨xs.toArray.modify i f, by simp⟩

@[simp]
theorem Vector.getElem_modify_self {xs : Vector α n} {i : ℕ} (f : α → α) (h : i < n) :
  (xs.modify i f)[i] = f (xs[i]) := by simp [modify, Array.getElem_modify_self]

@[simp]
theorem Vector.getElem_modify_ne {xs : Vector α n} {i : ℕ} (h : i ≠ j) (f : α → α) (hj : j < n) :
  (xs.modify i f)[j] = xs[j] := by simp [modify, Array.getElem_modify_of_ne h]

/-- `Vec m n R` is an `m`-by-`n` matrix over `R`, stored as a two-dimensional array. -/
abbrev VecMatrix (m n : ℕ) (R : Type u) := Vector (Vector R n) m

namespace VecMatrix

instance [Zero R] [One R] : One (VecMatrix n n R) where
  one := Vector.ofFn fun i => Vector.set 0 i 1

def ofMatrix (M : Matrix (Fin m) (Fin n) R) : VecMatrix m n R :=
  Vector.ofFn fun i => Vector.ofFn fun j => M i j

def toMatrix (A : VecMatrix m n R) : Matrix (Fin m) (Fin n) R :=
  Matrix.of fun i j => A[i][j]

@[simp]
theorem toMatrix_apply (A : VecMatrix m n R) (i : Fin m) (j : Fin n) :
  A.toMatrix i j = A[i][j] := by simp [toMatrix]

/-- Subtract row `j` multiplied by `c` from row `i`. -/
@[inline]
def transvectSub [Mul R] [Sub R] (A : VecMatrix m n R) (i j : Fin m) (c : R) :
    VecMatrix m n R :=
  A.modify i fun row => row.mapFinIdx fun idx a h => a - c * A[j][idx]

@[simp]
theorem getElem_transvectSub_self [Mul R] [Sub R] {A : VecMatrix m n R} {i j : Fin m} {c : R}
    (h : k < n) : (A.transvectSub i j c)[i.val][k] = A[i][k] - c * A[j][k] := by simp [transvectSub]

@[simp]
theorem getElem_transvectSub_ne [Mul R] [Sub R] {A : VecMatrix m n R} {i j : Fin m} {c : R}
    (h : i.val ≠ a) (ha : a < m) (hb : b < n) : (A.transvectSub i j c)[a][b] = A[a][b] := by
  simp [transvectSub, h]
