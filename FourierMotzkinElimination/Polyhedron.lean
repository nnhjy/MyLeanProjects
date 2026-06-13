import FourierMotzkinElimination.Common

import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Fin.Basic

/- **Definition 1. Polyhedron**
  A polyhedron in `K^n` described by linear inequalities `A x ≥ b`.

  The data type is polymorphic over the scalar field `K`. Instantiating at `K = ℝ` recovers the
  classical (noncomputable) polyhedron; instantiating at `K = ℚ` gives a *computable* polyhedron
  (see `ComputablePolyhedron` below). -/
structure Polyhedron (K : Type*) (m n : Nat) where
  A : Matrix (Fin m) (Fin n) K
  b : Fin m → K

namespace Polyhedron

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/- Feasible set: `{ x | ∀ i, ∑ j, A i j * x j ≥ b i }`. -/
def carrier {m n : Nat} (P : Polyhedron K m n) :
  Set (Fin n → K) :=
  { x | ∀ i : Fin m, ∑ j : Fin n, P.A i j * x j ≥ P.b i }

end Polyhedron

#check @Polyhedron.carrier

def memPolyhedron {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {m n : Nat} (P : Polyhedron K m n) (x : Fin n → K) : Prop :=
  ∀ i : Fin m, ∑ j : Fin n, P.A i j * x j ≥ P.b i

lemma memPolyhedron_iff {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {m n : ℕ} (P : Polyhedron K m n) (x : Fin n → K) :
  memPolyhedron P x ↔ x ∈ P.carrier := by
  simp [memPolyhedron, Polyhedron.carrier]

/- # Deterministic conversion of a `Finset (Fin m)` to a `List (Fin m)`

`Finset.toList` is `noncomputable` and has an arbitrary (choice-based) order. For the
Fourier–Motzkin algorithm we instead use the deterministic order obtained by filtering
`List.finRange m`. This makes the algorithm computable and gives a *canonical* row order that is
shared between the real and rational versions of the algorithm. -/
def finsetToList {m : Nat} (s : Finset (Fin m)) : List (Fin m) :=
  (List.finRange m).filter (fun i => decide (i ∈ s))

@[simp] lemma mem_finsetToList {m : Nat} {s : Finset (Fin m)} {i : Fin m} :
    i ∈ finsetToList s ↔ i ∈ s := by
  simp [finsetToList, List.mem_filter, List.mem_finRange]

lemma nodup_finsetToList {m : Nat} (s : Finset (Fin m)) : (finsetToList s).Nodup :=
  (List.nodup_finRange m).filter _

@[simp] lemma toFinset_finsetToList {m : Nat} (s : Finset (Fin m)) :
    (finsetToList s).toFinset = s := by
  ext i; simp [List.mem_toFinset]

lemma length_finsetToList {m : Nat} (s : Finset (Fin m)) :
    (finsetToList s).length = s.card := by
  rw [← List.toFinset_card_of_nodup (nodup_finsetToList s), toFinset_finsetToList]

/- **Computable Polyhedron**: a polyhedron with rational coefficients.

This is just `Polyhedron ℚ`. Because `ℚ` is a computable field with decidable order, membership
can be tested with `#eval` and the Fourier–Motzkin algorithm executes on actual data. -/
abbrev ComputablePolyhedron (m n : Nat) := Polyhedron ℚ m n

def ComputablePolyhedron.satisfiesConstraint {m n : Nat}
    (P : ComputablePolyhedron m n) (x : Fin n → ℚ) (i : Fin m) : Bool :=
  decide (∑ j : Fin n, P.A i j * x j ≥ P.b i)

def ComputablePolyhedron.mem {m n : Nat}
    (P : ComputablePolyhedron m n) (x : Fin n → ℚ) : Bool :=
  List.all (List.finRange m) (fun i => P.satisfiesConstraint x i)

def ComputablePolyhedron.memProp {m n : Nat}
    (P : ComputablePolyhedron m n) (x : Fin n → ℚ) : Prop :=
  ∀ i : Fin m, ∑ j : Fin n, P.A i j * x j ≥ P.b i

-- Decidable instance for membership
instance {m n : Nat} (P : ComputablePolyhedron m n) (x : Fin n → ℚ) :
    Decidable (P.memProp x) := by
  unfold ComputablePolyhedron.memProp
  infer_instance

/- Example: A simple 2D polyhedron representing the square [0,1] × [0,1]
   Constraints:
     x₀ ≥ 0  (equivalently: -x₀ ≤ 0, or written as x₀ ≥ 0)
     x₁ ≥ 0
     x₀ ≤ 1  (equivalently: x₀ ≥ -1 doesn't work, we need -x₀ ≥ -1)
     x₁ ≤ 1  (equivalently: -x₁ ≥ -1)
   Written as A x ≥ b:
     [1   0] [x₀]   [0]
     [0   1] [x₁] ≥ [0]
     [-1  0]        [-1]
     [0  -1]        [-1]
-/
def exampleSquare : ComputablePolyhedron 4 2 :=
  { A := !![1, 0; 0, 1; -1, 0; 0, -1]
    b := ![0, 0, -1, -1] }
#eval exampleSquare

-- Test point (1/2, 1/2) - should be inside
def point1 : Fin 2 → ℚ := ![1/2, 1/2]
#eval exampleSquare.mem point1  -- Expected: true

-- Test point (2, 1/2) - should be outside (x₀ > 1)
def point2 : Fin 2 → ℚ := ![2, 1/2]
#eval exampleSquare.mem point2  -- Expected: false

-- Test point (0, 0) - should be on the boundary (inside)
def point3 : Fin 2 → ℚ := ![0, 0]
#eval exampleSquare.mem point3  -- Expected: true

-- Test point (1, 1) - should be on the boundary (inside)
def point4 : Fin 2 → ℚ := ![1, 1]
#eval exampleSquare.mem point4  -- Expected: true

-- Test point (-1/4, 1/2) - should be outside (x₀ < 0)
def point5 : Fin 2 → ℚ := ![-1/4, 1/2]
#eval exampleSquare.mem point5  -- Expected: false
