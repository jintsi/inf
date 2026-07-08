import Inf.Util.Gauss

variable (n : ℕ) (R M : Type*) [Semiring R] [AddCommMonoid M] [Module R M]

/-- `Finbasis n R M` is the type of `Fin n`-indexed bases of `M` over `R`, intended to be
computable as opposed to the otherwise equivalent `Module.Basis (Fin n) R M`. -/
structure Finbasis where
  ofRepr ::
  repr : M ≃ₗ[R] Fin n → R

namespace Finbasis

instance : FunLike (Finbasis n R M) (Fin n) M where
  coe b i := b.repr.symm (Pi.single i 1)
  coe_injective b c h := by
    rcases b with ⟨f⟩; rcases c with ⟨g⟩; congr
    apply LinearEquiv.symm_bijective.injective
    apply LinearEquiv.toLinearMap_injective; ext; exact congr_fun h _

/-- Make a matrix whose columns are vectors from `v` written in basis `b`. -/
def toMatrix (b : Finbasis n R M) (v : ι → M) : Matrix (Fin n) ι R :=
  .of fun i j => b.repr (v j) i

/-- The standard basis on `Fin n → R`. -/
def stdPi (n : ℕ) (R : Type*) [Semiring R] : Finbasis n R (Fin n → R) :=
  .ofRepr (.refl _ _)

/-- Construct a basis whose basis vectors, in basis `b`, are the columns of matrix `A`. -/
def mapMatrix {n K V} [Field K] [DecidableEq K] [AddCommGroup V] [Module K V]
    (b : Finbasis n K V) (A : Matrix (Fin n) (Fin n) K) (hA : A.det ≠ 0) : Finbasis n K V where
  repr := b.repr.trans (A.toLinearEquiv' (A.invertibleOfDetNeZero hA)).symm

/-- Construct a basis out of basis vectors, checking their independence in a different basis
(typically `Pi.basisFun`). -/
def ofVectors {n K V} [Field K] [DecidableEq K] [AddCommGroup V] [Module K V]
    (b : Finbasis n K V) (v : (Fin n) → V)
    (h : (Matrix.of fun i => b.repr (v i)).det ≠ 0 := by native_decide) :
    Finbasis n K V := b.mapMatrix (Matrix.of fun i => b.repr (v i)).transpose (by simpa)
