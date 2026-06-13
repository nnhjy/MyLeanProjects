import FourierMotzkinElimination.Common
import FourierMotzkinElimination.Polyhedron

/- # Projection machineries
- We work with vectors `x` as functions `Fin n → ℝ`.
  The projection onto the first `k` coordinates is implemented by
  precomposing with `Fin.castLEEmb h : Fin k ↪ Fin n`, available when `h : k ≤ n`.
-/

/- **Definition 2. Projection of vector**
The coordinate projection `π : (Fin n → K) → (Fin k → K)` onto the first `k` coordinates,
defined when `h : k ≤ n`, by precomposition with `Fin.castLEEmb h`. -/
def proj {K : Type*} (k n : Nat) (h : k ≤ n) (x : Fin n → K) : Fin k → K :=
  fun i ↦ x ((Fin.castLEEmb h) i)

-- notation: max "π_" k:arg => proj k _ _

/- A lemma about how `proj` acts on coordinates `i`: -/
@[simp]
lemma proj_coords {K : Type*} (k n : Nat) (h_le : k ≤ n) (x : Fin n → K) (i : Fin k) :
  proj k n h_le x i = x ((Fin.castLEEmb h_le) i) := rfl

/- **Definition 3. Projection of set**
The projection of a set `S ⊆ K^n` to its first `k` coordinates, `Π_k(S) ⊆ (Fin k → K)`:
`Π_k(S) = { π_k(x) | x ∈ S }`, is its image under the map `proj k n h`, assuming `h : k ≤ n`. -/
def setProj {K : Type*} (k n : Nat) (h : k ≤ n) (S : Set (Fin n → K)) : Set (Fin k → K) :=
  { y | ∃ x ∈ S, y = proj k n h x }

/- Membership of set projection by definition -/
@[simp]
lemma mem_setProj_iff {K : Type*} {k n : Nat} {h_le : k ≤ n} {S : Set (Fin n → K)} {y : Fin k → K} :
  y ∈ setProj k n h_le S
  ↔ ∃ x ∈ S, y = proj k n h_le x := Iff.rfl

/- Membership of set projection in terms of coordinates `i`:
  `y ∈ Π_k(S)` iff there exists `x ∈ S` whose first `k` coordinates equal `y`. -/
@[simp]
lemma mem_setProj_iff_coords {K : Type*} {k n : Nat} {h_le : k ≤ n} {S : Set (Fin n → K)}
    {y : Fin k → K} :
  y ∈ setProj k n h_le S
  ↔ ∃ x ∈ S, ∀ i : Fin k, y i = proj k n h_le x i := by
  -- `↔ ∃ x ∈ S, ∀ i : Fin k, y i = x ((Fin.castLEEmb h) i) := by`
  constructor
  · rintro ⟨x, hxS, rfl⟩
    exact ⟨x, hxS, by intro i; rfl⟩
  · rintro ⟨x, hxS, hyx⟩
    refine ⟨x, hxS, ?_⟩
    funext i
    simpa using hyx i

/- **Definition 5. Projection of polyhedron**
  The projection of the feasible set onto the first `k` coordinates.
-/
def polyhedronProj {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {m n k : Nat} (h : k ≤ n)
  (P : Polyhedron K m n) : Set (Fin k → K) := setProj k n h P.carrier

/- `simp`-friendly membership form for the projected feasible set. -/
@[simp]
lemma Polyhedron.mem_projectCarrier_iff {K : Type*}
  [Field K] [LinearOrder K] [IsStrictOrderedRing K]
  {m n k : Nat} {h_le : k ≤ n}
  {P : Polyhedron K m n} {y : Fin k → K} :
  y ∈ polyhedronProj h_le P ↔ ∃ x ∈ P.carrier, y = proj k n h_le x := Iff.rfl

/-! # Computable Projections

These are computable versions of the projections above, operating on `ℚ` instead of `ℝ`
and on `ComputablePolyhedron` instead of `Polyhedron`.
-/

/- **Computable Definition 2. Projection of vector (ℚ version)**
The coordinate projection `π : (Fin n → ℚ) → (Fin k → ℚ)` onto the first `k` coordinates,
defined when `h : k ≤ n`, by restriction to the first `k` indices. -/
def computableProj (k n : Nat) (h : k ≤ n) (x : Fin n → ℚ) : Fin k → ℚ :=
  fun i ↦ x ⟨i.val, Nat.lt_of_lt_of_le i.isLt h⟩

/- A lemma about how `computableProj` acts on coordinates `i`: -/
@[simp]
lemma computableProj_coords (k n : Nat) (h_le : k ≤ n) (x : Fin n → ℚ) (i : Fin k) :
  computableProj k n h_le x i = x ⟨i.val, Nat.lt_of_lt_of_le i.isLt h_le⟩ := rfl

/- **Computable Definition 3. Projection of set**
The projection of a set `S ⊆ ℚ^n` to its first `k` coordinates,
`Π_k(S) ⊆ (Fin k → ℚ)`: `Π_k(S) = { π_k(x) | x ∈ S }`,
is its image under the map `computableProj k n h`, assuming `h : k ≤ n`. -/
def computableSetProj (k n : Nat) (h : k ≤ n) (S : Set (Fin n → ℚ)) : Set (Fin k → ℚ) :=
  { y | ∃ x ∈ S, y = computableProj k n h x }

/- Membership of computable set projection by definition -/
@[simp]
lemma mem_computableSetProj_iff {k n : Nat} {h_le : k ≤ n} {S : Set (Fin n → ℚ)} {y : Fin k → ℚ} :
    y ∈ computableSetProj k n h_le S
    ↔ ∃ x ∈ S, y = computableProj k n h_le x := Iff.rfl

/- Membership of computable set projection in terms of coordinates `i`:
  `y ∈ Π_k(S)` iff there exists `x ∈ S` whose first `k` coordinates equal `y`. -/
@[simp]
lemma mem_computableSetProj_iff_coords {k n : Nat}
    {h_le : k ≤ n} {S : Set (Fin n → ℚ)} {y : Fin k → ℚ} :
    y ∈ computableSetProj k n h_le S
    ↔ ∃ x ∈ S, ∀ i : Fin k, y i = computableProj k n h_le x i := by
  constructor
  · rintro ⟨x, hxS, rfl⟩
    exact ⟨x, hxS, by intro i; rfl⟩
  · rintro ⟨x, hxS, hyx⟩
    refine ⟨x, hxS, ?_⟩
    funext i
    simpa using hyx i

/- **Computable Definition 5. Projection of ComputablePolyhedron**
The projection of the feasible set onto the first `k` coordinates.

Note: This returns a `Set`, not a `ComputablePolyhedron`. For a computable polyhedron
representation of the projection, use `FourierMotzkin.eliminationIteration` (at `K = ℚ`)
from `AlgorithmFME.lean`. -/
def computablePolyhedronProj {m n k : Nat} (h : k ≤ n)
    (P : ComputablePolyhedron m n) : Set (Fin k → ℚ) :=
  computableSetProj k n h { x | P.memProp x }

/- `simp`-friendly membership form for the projected feasible set. -/
@[simp]
lemma ComputablePolyhedron.mem_projectCarrier_iff {m n k : Nat} {h_le : k ≤ n}
    {P : ComputablePolyhedron m n} {y : Fin k → ℚ} :
    y ∈ computablePolyhedronProj h_le P ↔ ∃ x, P.memProp x ∧ y = computableProj k n h_le x := by
  simp [computablePolyhedronProj]

/-! ## Examples for computable projections -/

/- Example: Project a 3D point to 2D -/
def examplePoint3D : Fin 3 → ℚ := ![1, 2, 3]
#eval computableProj 2 3 (by omega) examplePoint3D  -- Should give [1, 2]

/- Example: Project a list of points -/
def examplePoints : List (Fin 3 → ℚ) := [![1, 2, 3], ![4, 5, 6], ![7, 8, 9]]
#eval examplePoints.map (computableProj 2 3 (by omega))  -- Project all to 2D

/- Example: Set projection
   Project the set { (1,2,3), (4,5,6) } ⊆ ℚ³ onto the first 2 coordinates.
   Result should be { (1,2), (4,5) } ⊆ ℚ². -/
def exampleSet : Set (Fin 3 → ℚ) := { ![1, 2, 3], ![4, 5, 6] }
def projectedSet : Set (Fin 2 → ℚ) := computableSetProj 2 3 (by omega) exampleSet

-- Verify membership: (1,2) should be in the projected set
example : ![1, 2] ∈ projectedSet := by
  simp only [projectedSet, mem_computableSetProj_iff]
  refine ⟨![1, 2, 3], by simp [exampleSet], ?_⟩
  decide

-- Verify membership: (4,5) should be in the projected set
example : ![4, 5] ∈ projectedSet := by
  simp only [projectedSet, mem_computableSetProj_iff]
  refine ⟨![4, 5, 6], by simp [exampleSet], ?_⟩
  decide

/- Example: Polyhedron projection
   Project the unit square [0,1] × [0,1] ⊆ ℚ² onto the first coordinate.
   Result should be the interval [0,1] ⊆ ℚ. -/
def unitSquare : ComputablePolyhedron 4 2 :=
  { A := !![1, 0; 0, 1; -1, 0; 0, -1]
    b := ![0, 0, -1, -1] }

def projectedInterval : Set (Fin 1 → ℚ) := computablePolyhedronProj (by omega : 1 ≤ 2) unitSquare

-- Verify: (1/2) is in the projected interval (witness: (1/2, 1/2) is in the unit square)
example : ![(1:ℚ)/2] ∈ projectedInterval := by
  simp only [projectedInterval, ComputablePolyhedron.mem_projectCarrier_iff]
  use ![(1:ℚ)/2, (1:ℚ)/2]
  constructor
  · intro i
    fin_cases i <;> simp [unitSquare, Fin.sum_univ_succ] <;> norm_num
  · funext i; fin_cases i ; simp [computableProj]

-- Verify: (0) is in the projected interval (witness: (0, 0) is in the unit square)
example : ![(0:ℚ)] ∈ projectedInterval := by
  simp only [projectedInterval, ComputablePolyhedron.mem_projectCarrier_iff]
  use ![(0:ℚ), (0:ℚ)]
  constructor
  · intro i
    fin_cases i <;> simp [unitSquare, Fin.sum_univ_succ]
  · funext i; fin_cases i ; simp [computableProj]

/- Example: 3D box projected to 2D
   Project the unit cube [0,1]³ ⊆ ℚ³ onto the first two coordinates.
   Result should be the unit square [0,1]² ⊆ ℚ². -/
def unitCube : ComputablePolyhedron 6 3 :=
  { A := !![1, 0, 0; 0, 1, 0; 0, 0, 1; -1, 0, 0; 0, -1, 0; 0, 0, -1]
    b := ![0, 0, 0, -1, -1, -1] }

def projectedSquare : Set (Fin 2 → ℚ) := computablePolyhedronProj (by omega : 2 ≤ 3) unitCube

-- Verify: (1/2, 1/2) is in the projected square (witness: (1/2, 1/2, 0) is in the unit cube)
example : ![(1:ℚ)/2, (1:ℚ)/2] ∈ projectedSquare := by
  simp only [projectedSquare, ComputablePolyhedron.mem_projectCarrier_iff]
  use ![(1:ℚ)/2, (1:ℚ)/2, (0:ℚ)]
  constructor
  · intro i
    fin_cases i <;> simp [unitCube, Fin.sum_univ_succ] <;> norm_num
  · funext i; fin_cases i <;> simp [computableProj]
