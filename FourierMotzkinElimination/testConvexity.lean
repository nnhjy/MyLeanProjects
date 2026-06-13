import FourierMotzkinElimination.Common
import FourierMotzkinElimination.Polyhedron
import FourierMotzkinElimination.Projection
import Mathlib.Analysis.Convex.Basic

/- # Polyhedron is convex
For any polyhedron `P`, its `carrier set` is convex in the sense of Mathlib's Convex definition.
Convexity means: For any two points x, y in the polyhedron and any a, b ≥ 0 with a + b = 1,
the convex combination a • x + b • y is also in the polyhedron. -/
theorem Polyhedron.convex_carrier {m n : Nat} (P : Polyhedron ℝ m n) :
  Convex ℝ P.carrier := by
  unfold Convex
  intro x hx
  unfold StarConvex
  intro y hy a b ha hb hab
  -- Need to show: a • x + b • y ∈ P.carrier
  unfold Polyhedron.carrier
  intro i
  -- Need to show: ∑ j, P.A i j * (a • x + b • y) j ≥ P.b i
  calc
    ∑ j : Fin n, P.A i j * (a • x + b • y) j
      = ∑ j : Fin n, P.A i j * (a * x j + b * y j) := by simp [Pi.add_apply, Pi.smul_apply]
    _ = ∑ j : Fin n, (P.A i j * (a * x j) + P.A i j * (b * y j)) := by
        congr 1; ext j; ring
    _ = ∑ j : Fin n, P.A i j * (a * x j) + ∑ j : Fin n, P.A i j * (b * y j) := by
        rw [Finset.sum_add_distrib]
    _ = a * ∑ j : Fin n, P.A i j * x j + b * ∑ j : Fin n, P.A i j * y j := by
        congr 1
        · rw [Finset.mul_sum]; congr 1; ext j; ring
        · rw [Finset.mul_sum]; congr 1; ext j; ring
    _ ≥ a * P.b i + b * P.b i := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left (hx i) ha
        · exact mul_le_mul_of_nonneg_left (hy i) hb
    _ = (a + b) * P.b i := by ring
    _ = P.b i := by rw [hab, one_mul]

/- # Projection of set preserves convexity
If `S` is convex in `ℝ^n`, then its projection onto the first `k` coordinates is convex in `ℝ^k`. -/
lemma convex_setProj {k n : Nat} {h : k ≤ n} {S : Set (Fin n → ℝ)}
    (hS : Convex ℝ S) : Convex ℝ (setProj k n h S) := by
  classical
  -- Use the "a,b≥0, a+b=1" definition of convexity
  intro y₁ hy₁ y₂ hy₂ a b ha hb hab
  rcases hy₁ with ⟨x₁, hx₁S, rfl⟩
  rcases hy₂ with ⟨x₂, hx₂S, rfl⟩
  -- Candidate witness in the preimage: `a • x₁ + b • x₂`
  refine ⟨a • x₁ + b • x₂, ?_, ?_⟩
  · -- Membership in `S` by convexity of `S`
    exact hS hx₁S hx₂S ha hb hab
  · -- The projection commutes with affine combination (pointwise)
    ext i
    simp [proj, Pi.add_apply, Pi.smul_apply]

/- The projection of a polyhedron's feasible set is convex. -/
lemma convex_polyhedronProj {m n k : Nat} {h : k ≤ n}
    (P : Polyhedron ℝ m n) : Convex ℝ (polyhedronProj h P) := by
  have hPc : Convex ℝ P.carrier := by exact P.convex_carrier
  simpa [polyhedronProj, setProj] using
    (convex_setProj (k:=k) (n:=n) (h:=h) (S:=P.carrier) hPc)
