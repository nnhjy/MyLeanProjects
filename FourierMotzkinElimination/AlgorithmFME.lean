import FourierMotzkinElimination.Common
import FourierMotzkinElimination.Polyhedron
import FourierMotzkinElimination.Projection

import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic
import Mathlib.Algebra.Order.Field.Basic

import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Data.Real.Archimedean

/- # Fourier–Motzkin Elimination (FME) algorithm -/
namespace FourierMotzkinSet
/- ## Naive Fourier-Motzkin Elimination procedure
  - Input: a `Polyhedron`
  - Output: a `Set` of index
  - Only for FME procedure demo, not for correctness analysis
-/

/- Drops the coordinate `ℓ : Fin (n+1)`:
it maps `Fin n` into `Fin (n+1)` skipping `ℓ`. -/
@[simp, grind] def dropIndex {n : Nat} (ℓ : Fin (n + 1)) : Fin n → Fin (n+1) :=
  Fin.succAbove ℓ

/- Or use the concept of embedding -/
-- def dropIndexEmb {n : Nat} (ℓ : Fin (n+1)) : Fin n ↪ Fin (n+1) :=
--   Fin.succAboveEmb ℓ

/- Positive-index set for the column `ℓ`: constraints with `A i ℓ > 0`. -/
def Ipos {m n : Nat} (P : Polyhedron ℝ m (n + 1)) (ℓ : Fin (n + 1)) : Set (Fin m) :=
  { i | 0 < P.A i ℓ }

/- Negative-index set for the column `ℓ`: constraints with `A i ℓ < 0`. -/
def Ineg {m n : Nat} (P : Polyhedron ℝ m (n + 1)) (ℓ : Fin (n + 1)) : Set (Fin m) :=
  { i | P.A i ℓ < 0 }

/- Zero-index set for the column `ℓ`: constraints with `A i ℓ = 0`. -/
def Izero {m n : Nat} (P : Polyhedron ℝ m (n + 1)) (ℓ : Fin (n + 1)) : Set (Fin m) :=
  { i | P.A i ℓ = 0 }

/- The eliminated set `Q ⊆ ℝ^n` obtained by eliminating variable `ℓ : Fin (n+1)`.
This is the standard FME output:
- For every `i0 ∈ I0` (zero coefficient), keep `∑_{j≠ℓ} a_{i0, j} y_j ≥ b_{i0}`.
- For every pair `(i+, i-) ∈ I+ × I-`, require
  `b_{i-}/a_{i-,ℓ} - Σ (a_{i-,j}/a_{i-,ℓ}) y_j ≥ b_{i+}/a_{i+,ℓ} - Σ (a_{i+,j}/a_{i+,ℓ}) y_j`.
-/
def elimIndexSet {m n : Nat} (P : Polyhedron ℝ m (n + 1)) (ℓ : Fin (n + 1)) :
    Set (Fin n → ℝ) :=
  let ι := dropIndex ℓ
  { y |
    -- constraints coming from rows with zero coefficient in `ℓ`
    (∀ i : Fin m, P.A i ℓ = 0 →
        (∑ j : Fin n, P.A i (ι j) * y j) ≥ P.b i) ∧
    -- pairwise constraints from positive + negative rows
    (∀ (iPos iNeg : Fin m),
        0 < P.A iPos ℓ → P.A iNeg ℓ < 0 →
        (P.b iNeg) / (P.A iNeg ℓ)
          - ∑ j : Fin n, (P.A iNeg (ι j)) / (P.A iNeg ℓ) * y j
        ≥
        (P.b iPos) / (P.A iPos ℓ)
          - ∑ j : Fin n, (P.A iPos (ι j)) / (P.A iPos ℓ) * y j) }

/- Specialization: eliminate the **last** coordinate of `ℝ^{n+1}`,
producing a set in `ℝ^n`. -/
def elimLastSet {m n : Nat} (P : Polyhedron ℝ m (n + 1)) : Set (Fin n → ℝ) :=
  elimIndexSet P (Fin.last (n := n))
  -- Note: `Fin.last` is the index `⟨n, n < n+1⟩`.

end FourierMotzkinSet

namespace FourierMotzkin
/- ## Formal Fourier-Motzkin Elimination procedure
  - Input and output are both a `Polyhedron`

  The procedure is polymorphic over the scalar field `K`. At `K = ℝ` it is the classical
  algorithm; at `K = ℚ` it is computable (see the `ComputablePolyhedron` examples at the end of
  this file).
-/

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/- **Algorithm 1 Step 2: Indices partition based on coefficient of last variable** -/
@[simp, grind]
def partitionIndices {m n : Nat} (hn : n > 0) (P : Polyhedron K m n) :
  Finset (Fin m) × Finset (Fin m) × Finset (Fin m) :=
  let lastIdx : Fin n := ⟨n - 1, Nat.sub_lt hn (by omega)⟩
  let I_pos := Finset.univ.filter (fun i ↦ P.A i lastIdx > 0)
  let I_neg := Finset.univ.filter (fun i ↦ P.A i lastIdx < 0)
  let I_zero := Finset.univ.filter (fun i ↦ P.A i lastIdx = 0)
  (I_pos, I_neg, I_zero)

/- Helper: Embed Fin (n-1) into Fin n for n > 0 -/
@[simp, grind]
def Fin.embedPred {n : Nat} (hn : n > 0) (i : Fin (n - 1)) : Fin n :=
  ⟨i.val, by
    have h1 : i.val < n - 1 := i.isLt
    have h2 : n - 1 < n := Nat.sub_lt hn (by omega)
    exact Nat.lt_trans h1 h2
  ⟩

/- **Algorithm 1 Step 3&4: eliminate xₙ to project from n to n-1 dimensions**
  Given polyhedron P in ℝ^n defined by constraints:
    ∑_{j=1}^n a_{ij} x_j ≥ b_i, ∀ i ∈ [m]

  Eliminate variable x_n to obtain polyhedron Q in ℝ^{n-1} defined by:

  (1) For each pair (i₊, i₋) ∈ I₊ × I₋:
      (b_{i₋}/a_{i₋,n} - ∑_{j=1}^{n-1} a_{i₋,j}/a_{i₋,n} · x_j) ≥
      (b_{i₊}/a_{i₊,n} - ∑_{j=1}^{n-1} a_{i₊,j}/a_{i₊,n} · x_j)

      Equivalently:
      ∑_{j=1}^{n-1} (a_{i₊,n}·a_{i₋,j} - a_{i₋,n}·a_{i₊,j}) x_j
      ≥ a_{i₊,n}·b_{i₋} - a_{i₋,n}·b_{i₊}

  (2) For each i₀ ∈ I₀:
      0 ≥ b_{i₀} - ∑_{j=1}^{n-1} a_{i₀,j} · x_j

      Equivalently: ∑_{j=1}^{n-1} a_{i₀,j} x_j ≥ b_{i₀}
-/
@[simp, grind]
def eliminationCycle {m n : Nat} (hn : n > 0) (P : Polyhedron K m n) :
  Σ m' : Nat, Polyhedron K m' (n - 1) :=
  let (I_pos, I_neg, I_zero) := partitionIndices hn P
  let lastIdx : Fin n := ⟨n - 1, Nat.sub_lt hn (by omega)⟩
  let m' := I_pos.card * I_neg.card + I_zero.card
  -- Convert Finsets to lists for indexing (deterministic order)
  let posIndices := finsetToList I_pos
  let negIndices := finsetToList I_neg
  let zeroIndices := finsetToList I_zero
  let numPairs := I_pos.card * I_neg.card
  ⟨m', {
    A := fun (idx : Fin m') (j : Fin (n - 1)) ↦
      let j' := Fin.embedPred hn j
      if h : idx.val < numPairs then
        -- Pair constraint (i₊, i₋) ∈ I₊ × I₋
        -- Index i₊ = idx.val / |I_neg|, i₋ = idx.val % |I_neg|
        if h_neg_nonempty : I_neg.card > 0 then
          let i_pos_idx := idx.val / I_neg.card
          let i_neg_idx := idx.val % I_neg.card
          if h_pos_valid : i_pos_idx < posIndices.length then
            if h_neg_valid : i_neg_idx < negIndices.length then
              let i_pos := posIndices[i_pos_idx]
              let i_neg := negIndices[i_neg_idx]
              -- Coefficient: a_{i₊,n} · a_{i₋,j} - a_{i₋,n} · a_{i₊,j}
              let a_neg_j := P.A i_neg j'
              let a_pos_j := P.A i_pos j'
              let a_pos_n := P.A i_pos lastIdx
              let a_neg_n := P.A i_neg lastIdx
              a_pos_n * a_neg_j - a_neg_n * a_pos_j
            else 0
          else 0
        else 0
      else
        -- Zero-coefficient constraint from I₀
        let i_zero_idx := idx.val - numPairs
        if h_zero_valid : i_zero_idx < zeroIndices.length then
          let i_zero := zeroIndices[i_zero_idx]
          P.A i_zero j'
        else 0

    b := fun (idx : Fin m') ↦
      if h : idx.val < numPairs then
        -- Pair constraint RHS: a_{i₊,n} · b_{i₋} - a_{i₋,n} · b_{i₊}
        if h_neg_nonempty : I_neg.card > 0 then
          let i_pos_idx := idx.val / I_neg.card
          let i_neg_idx := idx.val % I_neg.card
          if h_pos_valid : i_pos_idx < posIndices.length then
            if h_neg_valid : i_neg_idx < negIndices.length then
              let i_pos := posIndices[i_pos_idx]
              let i_neg := negIndices[i_neg_idx]
              let b_pos := P.b i_pos
              let b_neg := P.b i_neg
              let a_pos_n := P.A i_pos lastIdx
              let a_neg_n := P.A i_neg lastIdx
              a_pos_n * b_neg - a_neg_n * b_pos
            else 0
          else 0
        else 0
      else
        -- Zero-coefficient constraint RHS: b_{i₀}
        let i_zero_idx := idx.val - numPairs
        if h_zero_valid : i_zero_idx < zeroIndices.length then
          let i_zero := zeroIndices[i_zero_idx]
          P.b i_zero
        else 0
  }⟩

/- **Iteration step: project from n to k dimensions** -/
def eliminationIteration {m n k : Nat} (h : k ≤ n) (P : Polyhedron K m n) :
  Σ m' : Nat, Polyhedron K m' k :=
  match n with
  | 0 =>
    have hk : k = 0 := Nat.eq_zero_of_le_zero h
    ⟨m, hk ▸ P⟩
  | n' + 1 =>
    if hk : k = n' + 1 then
      ⟨m, hk ▸ P⟩
    else
      have h_pos : n' + 1 > 0 := by omega
      have h_le : k ≤ n' := by omega
      let ⟨m', P'⟩ := eliminationCycle h_pos P
      eliminationIteration h_le P'
  termination_by n - k

end FourierMotzkin

/- # Fourier–Motzkin Elimination correctness -/

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/- ## Helper definitions and lemmas -/

/- **Definition 4. Verctor extension**
  Given `y ∈ ℝ^(n-1)` and `xₙ ∈ ℝ`, construct `x = ⟨y, xₙ⟩ ∈ ℝ^n` -/
def extendVector {n : Nat} (hn : n > 0) (y : Fin (n - 1) → K) (xₙ : K) : Fin n → K :=
  fun i ↦
    let lastIdx : Fin n := ⟨n - 1, Nat.sub_lt hn (by omega)⟩
    if h : i = lastIdx then xₙ
    else
      have hi : i.val < n - 1 := by
        by_contra h_neg
        push Not at h_neg
        have : i.val = n - 1 := by omega
        have : i = lastIdx := Fin.ext this
        contradiction
      y ⟨i.val, hi⟩

/- The last element of an extended vector -/
omit [Field K] [LinearOrder K] [IsStrictOrderedRing K] in
lemma extendVector_last {n : Nat} (hn : n > 0) (y : Fin (n - 1) → K) (xₙ : K) :
  let lastIdx : Fin n := ⟨n - 1, Nat.sub_lt hn (by omega)⟩
  extendVector hn y xₙ lastIdx = xₙ := by
  simp [extendVector]

/- **Correctness of the extended vector projection** -/
omit [Field K] [LinearOrder K] [IsStrictOrderedRing K] in
lemma extendVector_proj {n : Nat} (hn : n > 0) (y : Fin (n - 1) → K) (xₙ : K) :
  let h : n - 1 ≤ n := Nat.sub_le n 1
  proj (n - 1) n h (extendVector hn y xₙ) = y := by
  funext i
  simp only [proj, extendVector]
  -- The cast embedding preserves the value
  have hcast : (Fin.castLEEmb (Nat.sub_le n 1) i).val = i.val := by simp [Fin.castLEEmb]
  -- The cast embedding gives us an index with value i.val < n-1, so it can't equal lastIdx
  have hne : (Fin.castLEEmb (Nat.sub_le n 1) i) ≠ ⟨n - 1, Nat.sub_lt hn (by omega)⟩ := by
    intro heq
    have : i.val = n - 1 := by
      have := congr_arg Fin.val heq
      simp only [Fin.castLEEmb, Function.Embedding.coeFn_mk, Fin.val_castLE] at this
      exact this
    have : i.val < n - 1 := i.isLt
    omega
  simp_all

/- Helper: extendVector preserves y values on first n-1 coordinates -/
omit [Field K] [LinearOrder K] [IsStrictOrderedRing K] in
lemma extendVector_apply_embedPred {n : Nat} (hn : n > 0) (y : Fin (n - 1) → K) (xₙ : K)
    (j : Fin (n - 1)) :
  extendVector hn y xₙ (FourierMotzkin.Fin.embedPred hn j) = y j := by
  simp only [extendVector, FourierMotzkin.Fin.embedPred]
  have hj_lt_n : j.val < n := Nat.lt_of_lt_of_le j.isLt (Nat.sub_le n 1)
  have hne : (⟨j.val, hj_lt_n⟩ : Fin n) ≠ ⟨n - 1, Nat.sub_lt hn (by omega)⟩ := by
    intro heq
    have hval : j.val = n - 1 := by
      have := congr_arg Fin.val heq
      simp only at this
      exact this
    have hlt : j.val < n - 1 := j.isLt
    omega
  simp only [dif_neg hne]

/- **Helper lemmas for working with constraints** -/

/- Split a sum over `Fin n` into first `n-1` coordinates and the last one -/
omit [IsStrictOrderedRing K] in
lemma sum_split_last {n : Nat} (hn : n > 0) (f : Fin n → K) :
  let lastIdx : Fin n := ⟨n - 1, Nat.sub_lt hn (by omega)⟩
  ∑ j : Fin n, f j = (∑ j : Fin (n-1), f (FourierMotzkin.Fin.embedPred hn j)) + f lastIdx := by
  let lastIdx : Fin n := ⟨n - 1, Nat.sub_lt hn (by omega)⟩
  -- Use Fin.sum_univ_castSucc to split the sum
  cases n with
  | zero => omega
  | succ n' =>
    have hn' : n' + 1 - 1 = n' := by omega
    rw [Fin.sum_univ_castSucc]
    congr 1

/- When the last coefficient is 0, the sum equals the sum over first n-1 coords -/
omit [IsStrictOrderedRing K] in
lemma sum_with_zero_last {n : Nat} (hn : n > 0) (a : Fin n → K) (x : Fin n → K)
    (h_zero : a ⟨n - 1, Nat.sub_lt hn (by omega)⟩ = 0) :
  ∑ j : Fin n, a j * x j
    = ∑ j : Fin (n-1),
      a (FourierMotzkin.Fin.embedPred hn j) * x (FourierMotzkin.Fin.embedPred hn j) := by
  rw [sum_split_last hn]
  simp [h_zero]

/- Relationship between x and y = proj x on the first n-1 coordinates -/
omit [Field K] [LinearOrder K] [IsStrictOrderedRing K] in
lemma proj_apply_embedPred {n : Nat} (hn : n > 0) (x : Fin n → K) (j : Fin (n - 1)) :
  let h : n - 1 ≤ n := Nat.sub_le n 1
  proj (n - 1) n h x j = x (FourierMotzkin.Fin.embedPred hn j) := by
  dsimp [proj]
  -- show the cast embedding equals our `embedPred` on `Fin (n-1)`
  have hcast : (Fin.castLEEmb (Nat.sub_le n 1) j) = FourierMotzkin.Fin.embedPred hn j := by
    apply Fin.ext
    simp [Fin.castLEEmb, FourierMotzkin.Fin.embedPred]
  simp_all

/- **Constraint relationships** -/

/- Fourier-Motzkin inequality of the pair-wise constraints
- Base form:
  For each pair (i₊, i₋) ∈ I₊ × I₋,
        (b_{i₋} - ∑_{j=1}^{n-1} a_{i₋,j} · x_j) / a_{i₋,n} ≥
        (b_{i₊} - ∑_{j=1}^{n-1} a_{i₊,j} · x_j) / a_{i₊,n}
**Validity of statement (1.5) in the textual Algorithm 1 step 4** -/
lemma derive_FM_inequality_base {n : Nat} (hn : n > 0)
    (a_pos a_neg : Fin n → K) (b_pos b_neg : K)
    (x : Fin n → K) (y : Fin (n - 1) → K)
    (hyx : ∀ j : Fin (n-1), y j = x (FourierMotzkin.Fin.embedPred hn j))
    (h_pos_constraint : ∑ j : Fin n, a_pos j * x j ≥ b_pos)
    (h_neg_constraint : ∑ j : Fin n, a_neg j * x j ≥ b_neg) :
  let lastIdx : Fin n := ⟨n - 1, Nat.sub_lt hn (by omega)⟩
  let a_pos_n := a_pos lastIdx
  let a_neg_n := a_neg lastIdx
  (a_pos_n > 0) → (a_neg_n < 0) →
  (b_neg - ∑ j : Fin (n-1), a_neg (FourierMotzkin.Fin.embedPred hn j) * y j) / a_neg_n ≥
  (b_pos - ∑ j : Fin (n-1), a_pos (FourierMotzkin.Fin.embedPred hn j) * y j) / a_pos_n := by
  let lastIdx : Fin n := ⟨n - 1, Nat.sub_lt hn (by omega)⟩
  let a_pos_n := a_pos lastIdx
  let a_neg_n := a_neg lastIdx
  simp_all only
  intro h_pos_n h_neg_n
  let xₙ := x lastIdx
  -- Split the sums in the constraints
  have h_pos_split : ∑ j : Fin n, a_pos j * x j =
      (∑ j : Fin (n-1),
        a_pos (FourierMotzkin.Fin.embedPred hn j) * x (FourierMotzkin.Fin.embedPred hn j)
      ) +
      a_pos_n * xₙ := by
    rw [sum_split_last hn]
  have h_neg_split : ∑ j : Fin n, a_neg j * x j =
      (∑ j : Fin (n-1),
        a_neg (FourierMotzkin.Fin.embedPred hn j) * x (FourierMotzkin.Fin.embedPred hn j)
      ) +
      a_neg_n * xₙ := by
    rw [sum_split_last hn]
  -- Rewrite constraints using y
  have h_pos_y : ∑ j : Fin (n-1),
    a_pos (FourierMotzkin.Fin.embedPred hn j) * y j + a_pos_n * xₙ ≥ b_pos := by
    rw [h_pos_split] at h_pos_constraint
    convert h_pos_constraint using 2
    apply Finset.sum_congr rfl
    intro j _
    rw [← hyx]
  have h_neg_y : ∑ j : Fin (n-1),
    a_neg (FourierMotzkin.Fin.embedPred hn j) * y j + a_neg_n * xₙ ≥ b_neg := by
    rw [h_neg_split] at h_neg_constraint
    convert h_neg_constraint using 2
    apply Finset.sum_congr rfl
    intro j _
    rw [← hyx]
  -- Rearrange to get bounds on xₙ
  -- From h_pos_y: xₙ ≥ (b_pos - ∑ a_pos j * y j) / a_pos_n
  have bound_pos : xₙ ≥ (b_pos - ∑ j : Fin (n-1),
    a_pos (FourierMotzkin.Fin.embedPred hn j) * y j) / a_pos_n := by
    have : a_pos_n * xₙ ≥ b_pos - ∑ j : Fin (n-1),
      a_pos (FourierMotzkin.Fin.embedPred hn j) * y j := by linarith
    rw [ge_iff_le]
    rw [div_le_iff₀ h_pos_n]
    linarith
    -- rw [mul_comm]
    -- rw [ge_iff_le] at this
    -- exact this

  -- From h_neg_y: xₙ ≤ (b_neg - ∑ a_neg j * y j) / a_neg_n
  -- (note: division reverses due to negative)
  have bound_neg : xₙ ≤ (b_neg - ∑ j : Fin (n-1),
    a_neg (FourierMotzkin.Fin.embedPred hn j) * y j) / a_neg_n := by
    have : a_neg_n * xₙ ≥ b_neg - ∑ j : Fin (n-1),
      a_neg (FourierMotzkin.Fin.embedPred hn j) * y j := by linarith
    rw [le_div_iff_of_neg' h_neg_n]
    linarith

  simp_all only [FourierMotzkin.Fin.embedPred, ge_iff_le, gt_iff_lt, a_pos_n, lastIdx, xₙ, a_neg_n]
  linarith

/- Fourier-Motzkin inequality of the pair-wise constraints
- Convenient form:
  For each pair (i₊, i₋) ∈ I₊ × I₋,
        ∑_{j=1}^{n-1} (a_{i₊,n}·a_{i₋,j} - a_{i₋,n}·a_{i₊,j}) x_j
        ≥ a_{i₊,n}·b_{i₋} - a_{i₋,n}·b_{i₊}
**Lemma 1 conclusion** -/
lemma derive_FM_inequality {n : Nat} (hn : n > 0)
    (a_pos a_neg : Fin n → K) (b_pos b_neg : K)
    (x : Fin n → K) (y : Fin (n - 1) → K)
    (hyx : ∀ j : Fin (n-1), y j = x (FourierMotzkin.Fin.embedPred hn j))
    (h_pos_constraint : ∑ j : Fin n, a_pos j * x j ≥ b_pos)
    (h_neg_constraint : ∑ j : Fin n, a_neg j * x j ≥ b_neg) :
  let lastIdx : Fin n := ⟨n - 1, Nat.sub_lt hn (by omega)⟩
  let a_pos_n := a_pos lastIdx
  let a_neg_n := a_neg lastIdx
  (a_pos_n > 0) → (a_neg_n < 0) →
  -- ∑ (a_pos_n * a_neg[j] - a_neg_n * a_pos[j]) * y[j] ≥ a_pos_n * b_neg - a_neg_n * b_pos
  ∑ j : Fin (n-1), (
    a_pos_n * a_neg (FourierMotzkin.Fin.embedPred hn j)
    - a_neg_n * a_pos (FourierMotzkin.Fin.embedPred hn j)
    ) * y j ≥
  a_pos_n * b_neg - a_neg_n * b_pos := by

  let lastIdx : Fin n := ⟨n - 1, Nat.sub_lt hn (by omega)⟩
  let a_pos_n := a_pos lastIdx
  let a_neg_n := a_neg lastIdx
  simp_all only
  intro h_pos_n h_neg_n
  let xₙ := x lastIdx

  suffices base_form:
  (b_neg - ∑ j : Fin (n-1), a_neg (FourierMotzkin.Fin.embedPred hn j) * y j) / a_neg_n ≥
  (b_pos - ∑ j : Fin (n-1), a_pos (FourierMotzkin.Fin.embedPred hn j) * y j) / a_pos_n by

    simp_all only [
      FourierMotzkin.Fin.embedPred,
      ge_iff_le, gt_iff_lt, tsub_le_iff_right,
      a_neg_n, lastIdx, a_pos_n
    ]

    -- Convert base_form from division to multiplication form
    -- base_form: (b_neg - ∑...) / a_neg_n ≥ (b_pos - ∑...) / a_pos_n

    -- Multiply both sides by a_pos_n (positive)
    rw [div_le_iff₀ h_pos_n] at base_form
    rw [mul_comm, mul_div, mul_sub] at base_form

    -- Multiply both sides by a_neg_n (negative)
    rw [le_div_iff_of_neg' h_neg_n] at base_form
    rw [mul_sub] at base_form

    simp only [← tsub_le_iff_right]
    simp only [sub_le_comm] at base_form
    rw [← sub_add] at base_form
    apply le_sub_right_of_add_le at base_form
    rw [Finset.mul_sum, Finset.mul_sum] at base_form
    rw [← Finset.sum_sub_distrib] at base_form

    -- Apply ring to distribute multiplication over subtraction in each summand
    convert base_form using 2
    ring_nf

  exact derive_FM_inequality_base hn a_pos a_neg b_pos b_neg
        x y hyx h_pos_constraint h_neg_constraint h_pos_n h_neg_n

/- **Lemmas for indices partition** -/

/- Helper: membership in partition sets gives us the coefficient sign -/
lemma mem_partition_trichotomy {m n : Nat} (hn : n > 0) (P : Polyhedron K m n) (i : Fin m) :
  let lastIdx : Fin n := ⟨n - 1, Nat.sub_lt hn (by omega)⟩
  (P.A i lastIdx > 0) ∨ (P.A i lastIdx < 0) ∨ (P.A i lastIdx = 0) := by
  let lastIdx : Fin n := ⟨n - 1, Nat.sub_lt hn (by omega)⟩
  by_cases h1 : P.A i lastIdx > 0
  · left; exact h1
  · by_cases h2 : P.A i lastIdx < 0
    · right; left; exact h2
    · right; right
      push Not at h1 h2
      linarith

/- ## Core helper lemma 1 -/
/- **For direction (2) in the textual math. proof of Thorem 1**
  Given y satisfying Q's constraints, find bounds on the last coordinate xₙ -/
lemma find_feasible_xn {m n : Nat} (hn : n > 0) (P : Polyhedron K m n)
    (y : Fin (n - 1) → K) :
  let lastIdx : Fin n := ⟨n - 1, Nat.sub_lt hn (by omega)⟩
  let (I_pos, I_neg, I_zero) := FourierMotzkin.partitionIndices hn P
  (∀ i ∈ I_zero, ∑ j : Fin (n-1), P.A i (FourierMotzkin.Fin.embedPred hn j) * y j ≥ P.b i) →
  (∀ i_pos ∈ I_pos, ∀ i_neg ∈ I_neg,
    let a_pos_n := P.A i_pos lastIdx
    let a_neg_n := P.A i_neg lastIdx
    ∑ j : Fin (n-1), (a_pos_n * P.A i_neg (FourierMotzkin.Fin.embedPred hn j) -
                      a_neg_n * P.A i_pos (FourierMotzkin.Fin.embedPred hn j)) * y j ≥
    a_pos_n * P.b i_neg - a_neg_n * P.b i_pos) →
  ∃ xₙ : K, ∀ i : Fin m,
    ∑ j : Fin n, P.A i j * (extendVector hn y xₙ) j ≥ P.b i := by

  simp only [FourierMotzkin.partitionIndices, gt_iff_lt, Finset.mem_filter, Finset.mem_univ,
    true_and, FourierMotzkin.Fin.embedPred, ge_iff_le, tsub_le_iff_right]
  -- simp unfolds the let bindings, converting set membership to predicates:
  intro h_zero h_pairs
  -- h_zero : ∀ i ∈ {i | P.A i lastIdx = 0}, ... → ∀ i, P.A i lastIdx = 0 → ...
  -- h_pairs: ∀ i_pos ∈ I_pos, ∀ i_neg ∈ I_neg, ... → ∀ i_pos, coeff > 0 → ∀ i_neg, coeff < 0 → ...

  -- Define lastIdx and partition sets directly using set (not let pattern matching)
  set lastIdx : Fin n := ⟨n - 1, Nat.sub_lt hn (by omega)⟩ with hlastIdx
  set I_pos := Finset.univ.filter (fun i => P.A i lastIdx > 0) with hI_pos
  set I_neg := Finset.univ.filter (fun i => P.A i lastIdx < 0) with hI_neg
  set I_zero := Finset.univ.filter (fun i => P.A i lastIdx = 0) with hI_zero

  -- Prove that these match the partitionIndices definition
  have hpart : FourierMotzkin.partitionIndices hn P = (I_pos, I_neg, I_zero) := by
    simp only [FourierMotzkin.partitionIndices, hI_pos, hI_neg, hI_zero, hlastIdx]

  -- Define lower bound function for positive coefficient constraints
  let LB (i : Fin m) : K :=
    (P.b i - ∑ j : Fin (n-1), P.A i (FourierMotzkin.Fin.embedPred hn j) * y j) / P.A i lastIdx

  -- Define upper bound function for negative coefficient constraints
  let UB (i : Fin m) : K :=
    (P.b i - ∑ j : Fin (n-1), P.A i (FourierMotzkin.Fin.embedPred hn j) * y j) / P.A i lastIdx

  -- Case analysis on whether I_pos and I_neg are nonempty
  by_cases h_pos_nonempty : I_pos.Nonempty
  · by_cases h_neg_nonempty : I_neg.Nonempty
    · -- Both I_pos and I_neg are nonempty
      let lb := I_pos.sup' h_pos_nonempty LB
      let ub := I_neg.inf' h_neg_nonempty UB

      -- Key: FM constraints ensure lb ≤ ub
      have h_lb_le_ub : lb ≤ ub := by
        apply Finset.sup'_le
        intro i_pos hi_pos
        apply Finset.le_inf'
        intro i_neg hi_neg
        -- Extract coefficient signs from partition membership
        have h_pos_coeff : P.A i_pos lastIdx > 0 := by
          rw [hI_pos] at hi_pos
          exact (Finset.mem_filter.mp hi_pos).2
        have h_neg_coeff : P.A i_neg lastIdx < 0 := by
          rw [hI_neg] at hi_neg
          exact (Finset.mem_filter.mp hi_neg).2

        -- h_pairs expects the raw predicates (Lean unfolded the let bindings)
        have hpair := h_pairs i_pos h_pos_coeff i_neg h_neg_coeff
        simp only at hpair

        let S_pos := ∑ j : Fin (n-1), P.A i_pos (FourierMotzkin.Fin.embedPred hn j) * y j
        let S_neg := ∑ j : Fin (n-1), P.A i_neg (FourierMotzkin.Fin.embedPred hn j) * y j
        let a_pos_n := P.A i_pos lastIdx
        let a_neg_n := P.A i_neg lastIdx

        -- hpair: a_pos_n * b_neg ≤ ∑(a_pos_n * A_neg - a_neg_n * A_pos) * y + a_neg_n * b_pos
        -- The sum equals a_pos_n * S_neg - a_neg_n * S_pos
        -- So: a_pos_n * b_neg ≤ a_pos_n * S_neg - a_neg_n * S_pos + a_neg_n * b_pos
        -- Rearranging: a_pos_n * (b_neg - S_neg) ≤ a_neg_n * (b_pos - S_pos)

        -- cf. section "Convert base_form from division to multiplication form"
        -- in the proof of `lemma derive_FM_inequality`
        have h_convenient : a_pos_n * (P.b i_neg - S_neg) ≤ a_neg_n * (P.b i_pos - S_pos) := by
          have h_sum_eq : ∑ j : Fin (n-1), (
                            P.A i_pos lastIdx * P.A i_neg (FourierMotzkin.Fin.embedPred hn j) -
                            P.A i_neg lastIdx * P.A i_pos (FourierMotzkin.Fin.embedPred hn j)
                          ) * y j = P.A i_pos lastIdx * S_neg - P.A i_neg lastIdx * S_pos := by
            simp only [S_pos, S_neg]
            rw [Finset.mul_sum, Finset.mul_sum]
            rw [← Finset.sum_sub_distrib]
            congr 1; ext j; ring
          simp only [a_pos_n, a_neg_n, S_pos, S_neg]
          grind

        simp only [LB, UB]

        have h_base : (P.b i_neg - S_neg) / a_neg_n ≥ (P.b i_pos - S_pos) / a_pos_n := by
          -- Multiply both sides by a_neg_n (negative)
          rw [ge_iff_le, le_div_iff_of_neg' h_neg_coeff]
          -- Multiply both sides by a_pos_n (positive)
          rw [mul_div, le_div_iff₀ h_pos_coeff]
          linarith

        exact h_base

      use lb
      intro i
      rcases mem_partition_trichotomy hn P i with h_pos_coeff | h_neg_coeff | h_zero_coeff

      · -- Case: P.A i lastIdx > 0
        have hi_pos : i ∈ I_pos := by
          rw [hI_pos]
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, h_pos_coeff⟩

        rw [sum_split_last hn]
        simp only [extendVector_last]

        have h_inner : ∑ j : Fin (n-1), P.A i (FourierMotzkin.Fin.embedPred hn j) *
            extendVector hn y lb (FourierMotzkin.Fin.embedPred hn j) =
            ∑ j : Fin (n-1), P.A i (FourierMotzkin.Fin.embedPred hn j) * y j := by
          congr 1; ext j; rw [extendVector_apply_embedPred]

        rw [h_inner]

        have h_lb_ge : lb ≥ LB i := Finset.le_sup' LB hi_pos
        simp only [LB] at h_lb_ge

        let S := ∑ j : Fin (n-1), P.A i (FourierMotzkin.Fin.embedPred hn j) * y j
        have h_bound : P.A i lastIdx * lb ≥ P.b i - S := by
          rw [ge_iff_le] at h_lb_ge ⊢
          rw [div_le_iff₀ h_pos_coeff] at h_lb_ge
          linarith
        linarith

      · -- Case: P.A i lastIdx < 0
        have hi_neg : i ∈ I_neg := by
          rw [hI_neg]
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, h_neg_coeff⟩

        rw [sum_split_last hn]
        simp only [extendVector_last]

        have h_inner : ∑ j : Fin (n-1), P.A i (FourierMotzkin.Fin.embedPred hn j) *
            extendVector hn y lb (FourierMotzkin.Fin.embedPred hn j) =
            ∑ j : Fin (n-1), P.A i (FourierMotzkin.Fin.embedPred hn j) * y j := by
          congr 1; ext j; rw [extendVector_apply_embedPred]

        rw [h_inner]

        have h_ub_le : ub ≤ UB i := Finset.inf'_le UB hi_neg
        have h_lb_le_UB : lb ≤ UB i := le_trans h_lb_le_ub h_ub_le
        simp only [UB] at h_lb_le_UB

        let S := ∑ j : Fin (n-1), P.A i (FourierMotzkin.Fin.embedPred hn j) * y j
        have h_bound : P.A i lastIdx * lb ≥ P.b i - S := by
          rw [le_div_iff_of_neg' h_neg_coeff] at h_lb_le_UB
          linarith
        linarith

      · -- Case: P.A i lastIdx = 0
        have hi_zero : i ∈ I_zero := by
          rw [hI_zero]
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, h_zero_coeff⟩

        rw [sum_split_last hn]
        simp only [extendVector_last, h_zero_coeff, zero_mul, add_zero]

        have h_inner : ∑ j : Fin (n-1), P.A i (FourierMotzkin.Fin.embedPred hn j) *
            extendVector hn y lb (FourierMotzkin.Fin.embedPred hn j) =
            ∑ j : Fin (n-1), P.A i (FourierMotzkin.Fin.embedPred hn j) * y j := by
          congr 1; ext j; rw [extendVector_apply_embedPred]

        rw [h_inner]
        -- h_zero expects the predicate P.A i lastIdx = 0, which is h_zero_coeff
        exact h_zero i h_zero_coeff

    · -- I_pos nonempty, I_neg empty
      let lb := I_pos.sup' h_pos_nonempty LB
      use lb
      intro i
      rcases mem_partition_trichotomy hn P i with h_pos_coeff | h_neg_coeff | h_zero_coeff

      · have hi_pos : i ∈ I_pos := by
          rw [hI_pos]
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, h_pos_coeff⟩

        rw [sum_split_last hn]
        simp only [extendVector_last]

        have h_inner : ∑ j : Fin (n-1), P.A i (FourierMotzkin.Fin.embedPred hn j) *
            extendVector hn y lb (FourierMotzkin.Fin.embedPred hn j) =
            ∑ j : Fin (n-1), P.A i (FourierMotzkin.Fin.embedPred hn j) * y j := by
          congr 1; ext j; rw [extendVector_apply_embedPred]

        rw [h_inner]
        have h_lb_ge : lb ≥ LB i := Finset.le_sup' LB hi_pos
        simp only [LB] at h_lb_ge
        let S := ∑ j : Fin (n-1), P.A i (FourierMotzkin.Fin.embedPred hn j) * y j
        have h_bound : P.A i lastIdx * lb ≥ P.b i - S := by
          rw [ge_iff_le] at h_lb_ge ⊢
          rw [div_le_iff₀ h_pos_coeff] at h_lb_ge
          linarith
        linarith

      · have hi_neg : i ∈ I_neg := by
          rw [hI_neg]
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, h_neg_coeff⟩
        simp only [Finset.not_nonempty_iff_eq_empty] at h_neg_nonempty
        rw [h_neg_nonempty] at hi_neg
        exact absurd hi_neg (Finset.notMem_empty i)

      · have hi_zero : i ∈ I_zero := by
          rw [hI_zero]
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, h_zero_coeff⟩

        rw [sum_split_last hn]
        simp only [extendVector_last, h_zero_coeff, zero_mul, add_zero]

        have h_inner : ∑ j : Fin (n-1), P.A i (FourierMotzkin.Fin.embedPred hn j) *
            extendVector hn y lb (FourierMotzkin.Fin.embedPred hn j) =
            ∑ j : Fin (n-1), P.A i (FourierMotzkin.Fin.embedPred hn j) * y j := by
          congr 1; ext j; rw [extendVector_apply_embedPred]

        rw [h_inner]
        exact h_zero i h_zero_coeff

  · -- I_pos is empty
    by_cases h_neg_nonempty : I_neg.Nonempty
    · let ub := I_neg.inf' h_neg_nonempty UB
      use ub
      intro i
      rcases mem_partition_trichotomy hn P i with h_pos_coeff | h_neg_coeff | h_zero_coeff

      · have hi_pos : i ∈ I_pos := by
          rw [hI_pos]
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, h_pos_coeff⟩
        simp only [Finset.not_nonempty_iff_eq_empty] at h_pos_nonempty
        rw [h_pos_nonempty] at hi_pos
        exact absurd hi_pos (Finset.notMem_empty i)

      · have hi_neg : i ∈ I_neg := by
          rw [hI_neg]
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, h_neg_coeff⟩

        rw [sum_split_last hn]
        simp only [extendVector_last]

        have h_inner : ∑ j : Fin (n-1), P.A i (FourierMotzkin.Fin.embedPred hn j) *
            extendVector hn y ub (FourierMotzkin.Fin.embedPred hn j) =
            ∑ j : Fin (n-1), P.A i (FourierMotzkin.Fin.embedPred hn j) * y j := by
          congr 1; ext j; rw [extendVector_apply_embedPred]

        rw [h_inner]
        have h_ub_le : ub ≤ UB i := Finset.inf'_le UB hi_neg
        simp only [UB] at h_ub_le
        let S := ∑ j : Fin (n-1), P.A i (FourierMotzkin.Fin.embedPred hn j) * y j
        have h_bound : P.A i lastIdx * ub ≥ P.b i - S := by
          rw [le_div_iff_of_neg' h_neg_coeff] at h_ub_le
          linarith
        linarith

      · have hi_zero : i ∈ I_zero := by
          rw [hI_zero]
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, h_zero_coeff⟩

        rw [sum_split_last hn]
        simp only [extendVector_last, h_zero_coeff, zero_mul, add_zero]

        have h_inner : ∑ j : Fin (n-1), P.A i (FourierMotzkin.Fin.embedPred hn j) *
            extendVector hn y ub (FourierMotzkin.Fin.embedPred hn j) =
            ∑ j : Fin (n-1), P.A i (FourierMotzkin.Fin.embedPred hn j) * y j := by
          congr 1; ext j; rw [extendVector_apply_embedPred]

        rw [h_inner]
        exact h_zero i h_zero_coeff

    · -- Both I_pos and I_neg are empty
      use 0
      intro i
      rcases mem_partition_trichotomy hn P i with h_pos_coeff | h_neg_coeff | h_zero_coeff

      · have hi_pos : i ∈ I_pos := by
          rw [hI_pos]
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, h_pos_coeff⟩
        simp only [Finset.not_nonempty_iff_eq_empty] at h_pos_nonempty
        rw [h_pos_nonempty] at hi_pos
        exact absurd hi_pos (Finset.notMem_empty i)

      · have hi_neg : i ∈ I_neg := by
          rw [hI_neg]
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, h_neg_coeff⟩
        simp only [Finset.not_nonempty_iff_eq_empty] at h_neg_nonempty
        rw [h_neg_nonempty] at hi_neg
        exact absurd hi_neg (Finset.notMem_empty i)

      · have hi_zero : i ∈ I_zero := by
          rw [hI_zero]
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, h_zero_coeff⟩

        rw [sum_split_last hn]
        simp only [extendVector_last, h_zero_coeff, zero_mul, add_zero]

        have h_inner : ∑ j : Fin (n-1), P.A i (FourierMotzkin.Fin.embedPred hn j) *
            extendVector hn y 0 (FourierMotzkin.Fin.embedPred hn j) =
            ∑ j : Fin (n-1), P.A i (FourierMotzkin.Fin.embedPred hn j) * y j := by
          congr 1; ext j; rw [extendVector_apply_embedPred]

        rw [h_inner]
        exact h_zero i h_zero_coeff

/- ## Core helper lemma 2 -/
/- **Statement (2.1) in the textual math. proof of Thorem 1**
  Simplify Q's constraints in terms of the partition -/
omit [IsStrictOrderedRing K] in
lemma Q_constraint_characterization {m n : Nat} (hn : n > 0) (P : Polyhedron K m n)
    (y : Fin (n - 1) → K) :
  let ⟨m', Q⟩ := FourierMotzkin.eliminationCycle hn P
  let lastIdx : Fin n := ⟨n - 1, Nat.sub_lt hn (by omega)⟩
  let (I_pos, I_neg, I_zero) := FourierMotzkin.partitionIndices hn P
  y ∈ Q.carrier ↔
    (∀ i ∈ I_zero, ∑ j : Fin (n-1), P.A i (FourierMotzkin.Fin.embedPred hn j) * y j ≥ P.b i) ∧
    (∀ i_pos ∈ I_pos, ∀ i_neg ∈ I_neg,
      let a_pos_n := P.A i_pos lastIdx
      let a_neg_n := P.A i_neg lastIdx
      ∑ j : Fin (n-1), (a_pos_n * P.A i_neg (FourierMotzkin.Fin.embedPred hn j) -
                        a_neg_n * P.A i_pos (FourierMotzkin.Fin.embedPred hn j)) * y j ≥
      a_pos_n * P.b i_neg - a_neg_n * P.b i_pos) := by
  -- Unfold definitions
  simp only [
    Polyhedron.carrier, Set.mem_setOf_eq,
    FourierMotzkin.eliminationCycle, FourierMotzkin.partitionIndices
  ]
  set lastIdx : Fin n := ⟨n - 1, Nat.sub_lt hn (by omega)⟩
  set I_pos := Finset.univ.filter (fun i => P.A i lastIdx > 0)
  set I_neg := Finset.univ.filter (fun i => P.A i lastIdx < 0)
  set I_zero := Finset.univ.filter (fun i => P.A i lastIdx = 0)
  set numPairs := I_pos.card * I_neg.card
  set m' := numPairs + I_zero.card

  constructor
  · -- Forward: Q constraints → partition conditions
    intro hQ
    simp only at hQ
    constructor
    · -- Zero-coefficient constraints
      intro i hi
      have hi_mem : i ∈ I_zero := hi
      -- Find the index in Q corresponding to this zero constraint
      have h_i_in_list : i ∈ finsetToList I_zero := mem_finsetToList.mpr hi_mem
      obtain ⟨k, hk_lt, hk_eq⟩ := List.getElem_of_mem h_i_in_list
      have h_list_len : (finsetToList I_zero).length = I_zero.card := length_finsetToList I_zero
      have hk_lt' : k < I_zero.card := by rw [← h_list_len]; exact hk_lt
      have h_idx_lt_m' : numPairs + k < m' := by simp only [m']; omega
      let idx : Fin m' := ⟨numPairs + k, h_idx_lt_m'⟩
      have h_idx_ge : idx.val ≥ numPairs := by simp only [idx]; omega
      have h_idx_sub : idx.val - numPairs = k := by simp only [idx]; omega
      have h_idx_valid : idx.val - numPairs < (finsetToList I_zero).length := by
        rw [h_idx_sub]; exact hk_lt
      have hQ_idx := hQ idx
      simp only [ge_iff_le] at hQ_idx
      -- The constraint at idx corresponds to the zero constraint for i
      have h_not_pair : ¬(idx.val < numPairs) := by omega
      simp only [h_not_pair, ↓reduceDIte] at hQ_idx
      simp only [h_idx_valid, ↓reduceDIte] at hQ_idx
      have h_idx_eq : (finsetToList I_zero)[idx.val - numPairs]'h_idx_valid = i := by
        simp only [h_idx_sub]; exact hk_eq
      rw [h_idx_eq] at hQ_idx
      exact hQ_idx

    · -- Pair constraints
      intro i_pos hi_pos i_neg hi_neg
      -- Find the index in Q corresponding to this pair
      by_cases h_neg_card : I_neg.card > 0
      · have h_pos_in_list : i_pos ∈ finsetToList I_pos := mem_finsetToList.mpr hi_pos
        have h_neg_in_list : i_neg ∈ finsetToList I_neg := mem_finsetToList.mpr hi_neg
        obtain ⟨k_pos, hk_pos_lt, hk_pos_eq⟩ := List.getElem_of_mem h_pos_in_list
        obtain ⟨k_neg, hk_neg_lt, hk_neg_eq⟩ := List.getElem_of_mem h_neg_in_list
        have h_pos_card : I_pos.card > 0 := Finset.card_pos.mpr ⟨i_pos, hi_pos⟩
        have h_list_len_pos : (finsetToList I_pos).length = I_pos.card := length_finsetToList I_pos
        have h_list_len_neg : (finsetToList I_neg).length = I_neg.card := length_finsetToList I_neg
        let idx_val := k_pos * I_neg.card + k_neg
        have h_idx_lt : idx_val < numPairs := by
          simp only [idx_val, numPairs]
          have : k_pos < I_pos.card := by rw [← h_list_len_pos]; exact hk_pos_lt
          have : k_neg < I_neg.card := by rw [← h_list_len_neg]; exact hk_neg_lt
          calc k_pos * I_neg.card + k_neg
              < k_pos * I_neg.card + I_neg.card := by omega
            _ = (k_pos + 1) * I_neg.card := by ring
            _ ≤ I_pos.card * I_neg.card := by nlinarith
        have h_idx_lt_m' : idx_val < m' := by omega
        let idx : Fin m' := ⟨idx_val, h_idx_lt_m'⟩
        have hQ_idx := hQ idx
        simp only [ge_iff_le] at hQ_idx
        simp only [idx, idx_val, h_idx_lt, ↓reduceDIte, h_neg_card] at hQ_idx
        have h_pos_idx : idx_val / I_neg.card = k_pos := by
          simp only [idx_val]
          -- start with Claude here
          rw [Nat.add_comm, Nat.mul_comm, Nat.add_mul_div_left _ _ h_neg_card]
          have : k_neg / I_neg.card = 0 := Nat.div_eq_zero_iff.mpr (
              Or.inr (by rw [← h_list_len_neg]; exact hk_neg_lt)
            )
          omega
        have h_neg_idx : idx_val % I_neg.card = k_neg := by
          simp only [idx_val]
          rw [Nat.add_comm, Nat.mul_comm, Nat.add_mul_mod_self_left]
          exact Nat.mod_eq_of_lt (by rw [← h_list_len_neg]; exact hk_neg_lt)
        -- Rewrite hQ_idx using the index equations
        rw [h_pos_idx, h_neg_idx] at hQ_idx
        have h_pos_valid : k_pos < (finsetToList I_pos).length := hk_pos_lt
        have h_neg_valid : k_neg < (finsetToList I_neg).length := hk_neg_lt
        simp only [h_pos_valid, h_neg_valid, ↓reduceDIte, hk_pos_eq, hk_neg_eq] at hQ_idx
        exact hQ_idx
      · -- I_neg is empty, so the pair condition is vacuously true
        simp only [Nat.not_lt, Nat.le_zero, Finset.card_eq_zero] at h_neg_card
        rw [h_neg_card] at hi_neg
        exact absurd hi_neg (Finset.notMem_empty i_neg)

  · -- Backward: partition conditions → Q constraints
    intro ⟨h_zero_conds, h_pair_conds⟩ idx
    simp only [ge_iff_le]
    by_cases h_is_pair : idx.val < numPairs
    · -- This is a pair constraint
      simp only [h_is_pair, ↓reduceDIte]
      by_cases h_neg_card : I_neg.card > 0
      · simp only [h_neg_card, ↓reduceDIte]
        let i_pos_idx := idx.val / I_neg.card
        let i_neg_idx := idx.val % I_neg.card
        have h_pos_valid : i_pos_idx < (finsetToList I_pos).length := by
          simp only [i_pos_idx, length_finsetToList]
          have : idx.val < I_pos.card * I_neg.card := h_is_pair
          rw [Nat.mul_comm] at this
          exact Nat.div_lt_of_lt_mul this
        have h_neg_valid : i_neg_idx < (finsetToList I_neg).length := by
          simp only [i_neg_idx, length_finsetToList]
          exact Nat.mod_lt idx.val h_neg_card
        -- Unfold i_pos_idx and i_neg_idx to match the goal
        have h_pos_valid' : idx.val / I_neg.card < (finsetToList I_pos).length := h_pos_valid
        have h_neg_valid' : idx.val % I_neg.card < (finsetToList I_neg).length := h_neg_valid
        simp only [h_pos_valid', h_neg_valid', ↓reduceDIte]
        let i_pos := (finsetToList I_pos)[i_pos_idx]
        let i_neg := (finsetToList I_neg)[i_neg_idx]
        have hi_pos : i_pos ∈ I_pos := mem_finsetToList.mp (List.getElem_mem h_pos_valid)
        have hi_neg : i_neg ∈ I_neg := mem_finsetToList.mp (List.getElem_mem h_neg_valid)
        exact h_pair_conds i_pos hi_pos i_neg hi_neg
      · simp only [h_neg_card, ↓reduceDIte]
        -- numPairs = 0, so idx.val < 0 is false
        simp only [Nat.not_lt, Nat.le_zero, Finset.card_eq_zero] at h_neg_card
        simp only [h_neg_card, Finset.card_empty, mul_zero, numPairs] at h_is_pair
        omega
    · -- This is a zero constraint
      simp only [h_is_pair, ↓reduceDIte]
      let i_zero_idx := idx.val - numPairs
      have h_zero_valid : i_zero_idx < (finsetToList I_zero).length := by
        simp only [i_zero_idx, length_finsetToList]
        have : idx.val < m' := idx.isLt
        omega
      -- Unfold i_zero_idx to match the goal
      have h_zero_valid' : idx.val - numPairs < (finsetToList I_zero).length := h_zero_valid
      simp only [h_zero_valid', ↓reduceDIte]
      let i_zero := (finsetToList I_zero)[i_zero_idx]
      have hi_zero : i_zero ∈ I_zero := mem_finsetToList.mp (List.getElem_mem h_zero_valid)
      exact h_zero_conds i_zero hi_zero


/- ## Main theorems -/

/- **Theorem 1: Correctness of single Fourier-Motzkin Elimination cycle**
  The carrier of Q equals the projection of P onto the first (n-1) coordinates.
-/
theorem correctFourierMotzkinCycle {m n : Nat} (hn : n > 0) (P : Polyhedron K m n) :
  let ⟨_, Q⟩ := FourierMotzkin.eliminationCycle hn P
  let h : n - 1 ≤ n := Nat.sub_le n 1
  Q.carrier = polyhedronProj h P := by
  -- Unfold definitions
  simp only [polyhedronProj, setProj, Polyhedron.carrier]
  ext y
  constructor

  · -- Forward direction: Q.carrier → projection of P.carrier
    -- **Direction (2) in the textual math. proof of Thorem 1**
    intro hy
    -- Get Q explicitly
    let ⟨_, Q⟩ := FourierMotzkin.eliminationCycle hn P
    -- Apply the characterization
    have hy_char := (Q_constraint_characterization hn P y).mp hy
    obtain ⟨h_zero, h_pairs⟩ := hy_char
    -- Find a feasible xₙ using the bounds
    obtain ⟨xₙ, hx⟩ := find_feasible_xn hn P y h_zero h_pairs
    -- Construct x by extending y with xₙ
    use extendVector hn y xₙ
    constructor
    · exact hx
    · exact (extendVector_proj hn y xₙ).symm

  · -- Backward direction: projection of P.carrier → Q.carrier
    -- **Direction (1) in the textual math. proof of Thorem 1**
    intro ⟨x, hx, hyx⟩
    -- Apply the characterization in reverse
    apply (Q_constraint_characterization hn P y).mpr
    constructor
    · -- Show zero-coefficient constraints are satisfied
      intro i hi
      have h_zero : P.A i ⟨n - 1, Nat.sub_lt hn (by omega)⟩ = 0 := by simp_all
      have hxi : ∑ j : Fin n, P.A i j * x j ≥ P.b i := hx i
      rw [sum_with_zero_last hn (P.A i) x h_zero] at hxi
      -- rewrite `y` as `proj _ x` and simplify `proj` on embedded indices
      rw [hyx]
      simp only [FourierMotzkin.Fin.embedPred, proj_coords, Fin.castLEEmb_apply, ge_iff_le]
      exact hxi
    · -- Show pair constraints are satisfied
      intro i_pos hi_pos i_neg hi_neg
      simp only [gt_iff_lt, Finset.mem_filter, Finset.mem_univ, true_and] at hi_pos hi_neg
      let lastIdx : Fin n := ⟨n - 1, Nat.sub_lt hn (by omega)⟩
      have h_pos : P.A i_pos lastIdx > 0 := by grind
      have h_neg : P.A i_neg lastIdx < 0 := by grind
      have hx_pos : ∑ j : Fin n, P.A i_pos j * x j ≥ P.b i_pos := hx i_pos
      have hx_neg : ∑ j : Fin n, P.A i_neg j * x j ≥ P.b i_neg := hx i_neg

      have hyx' : ∀ j : Fin (n-1), y j = x (FourierMotzkin.Fin.embedPred hn j) := by
        intro j
        rw [hyx]
        exact proj_apply_embedPred hn x j

      exact derive_FM_inequality hn (P.A i_pos) (P.A i_neg) (P.b i_pos) (P.b i_neg)
        x y hyx' hx_pos hx_neg h_pos h_neg

/- **Helper lemmas for projection composition** -/

omit [Field K] [LinearOrder K] [IsStrictOrderedRing K] in
/-- Projection composition:
    projecting from n to k equals projecting from n to n-1 then from n-1 to k -/
lemma proj_comp {k n : Nat} (hk : k ≤ n) (x : Fin (n + 1) → K) :
    proj k (n + 1) (Nat.le_succ_of_le hk) x = proj k n hk (proj n (n + 1) (Nat.le_succ n) x) := by
  funext i
  simp only [proj]
  have hi : i.val < n := Nat.lt_of_lt_of_le i.isLt hk
  rfl

omit [Field K] [LinearOrder K] [IsStrictOrderedRing K] in
/-- Set projection composition -/
lemma setProj_comp {k n : Nat} (hk : k ≤ n) (S : Set (Fin (n + 1) → K)) :
    setProj k (n + 1) (Nat.le_succ_of_le hk) S
    = setProj k n hk (setProj n (n + 1) (Nat.le_succ n) S) := by
  ext y
  simp only [setProj]
  constructor
  · rintro ⟨x, hxS, rfl⟩
    use proj n (n + 1) (Nat.le_succ n) x
    constructor
    · exact ⟨x, hxS, rfl⟩
    · exact proj_comp hk x
  · rintro ⟨z, ⟨x, hxS, rfl⟩, rfl⟩
    use x
    constructor
    · exact hxS
    · exact (proj_comp hk x).symm

/-- Polyhedron projection composition -/
lemma polyhedronProj_comp {m k n : Nat} (hk : k ≤ n) (P : Polyhedron K m (n + 1)) :
    polyhedronProj (Nat.le_succ_of_le hk) P =
    polyhedronProj hk (FourierMotzkin.eliminationCycle (Nat.succ_pos n) P).2 := by
  simp only [polyhedronProj]
  rw [setProj_comp hk]
  congr 1
  have h_cycle := correctFourierMotzkinCycle (Nat.succ_pos n) P
  simp only [polyhedronProj] at h_cycle
  exact h_cycle.symm

/- **Theorem 2: Correctness of iterated Fourier-Motzkin Elimination**
  The carrier of the resulting polyhedron equals the projection of P onto the first k coordinates.
-/
theorem correctFourierMotzkinIteration {m n k : Nat} (h : k ≤ n) (P : Polyhedron K m n) :
  let ⟨_, Q⟩ := FourierMotzkin.eliminationIteration h P
  Q.carrier = polyhedronProj h P := by
  induction n generalizing m k with
  | zero =>
    have hk : k = 0 := Nat.eq_zero_of_le_zero h
    subst hk
    -- For n = 0, the polyhedron has dimension 0
    -- Pattern match on the result of eliminationIteration
    match hQ : FourierMotzkin.eliminationIteration h P with
    | ⟨m', Q⟩ =>
      -- By definition of eliminationIteration for n = 0, m' = m and Q = P (with cast)
      simp only [FourierMotzkin.eliminationIteration] at hQ
      -- hQ : ⟨m, h' ▸ P⟩ = ⟨m', Q⟩ where h' : 0 = 0
      have hm' : m' = m := by simp at hQ ⊢; omega
      subst hm'
      simp only [polyhedronProj, setProj]
      ext y
      simp only [Set.mem_setOf_eq, Polyhedron.carrier]
      constructor
      · intro hy
        use y
        constructor
        · intro i
          simp only [Finset.univ_eq_empty, Finset.sum_empty]
          have hy_i := hy i
          simp only [Finset.univ_eq_empty, Finset.sum_empty] at hy_i
          convert hy_i using 1
          congr 1
          simp_all
        · simp_all only [Sigma.mk.injEq, heq_eq_eq, true_and,
            Finset.univ_eq_empty, Finset.sum_empty, ge_iff_le]
          funext i; exact i.elim0
      · intro ⟨x, hx, hxy⟩ i
        simp only [Finset.univ_eq_empty, Finset.sum_empty]
        have hx_i := hx i
        simp only [Finset.univ_eq_empty, Finset.sum_empty] at hx_i
        convert hx_i using 1
        congr 1
        simp only [Sigma.mk.injEq, heq_eq_eq, true_and] at hQ
        cases hQ; rfl
  | succ n' ih =>
    by_cases hk : k = n' + 1
    · -- k = n' + 1, no elimination needed
      subst hk
      -- Pattern match on the result of eliminationIteration
      match hQ : FourierMotzkin.eliminationIteration h P with
      | ⟨m', Q⟩ =>
        -- By definition of eliminationIteration for k = n' + 1, m' = m and Q = P (with cast)
        simp only [FourierMotzkin.eliminationIteration, ↓reduceDIte] at hQ
        have hm' : m' = m := by simp at hQ ⊢; omega
        subst hm'
        simp only [polyhedronProj, setProj]
        ext y
        simp only [Set.mem_setOf_eq, Polyhedron.carrier]
        constructor
        · intro hy
          use y
          constructor
          · intro i
            have hy_i := hy i
            convert hy_i using 2 <;> (
              congr 1; simp only [Sigma.mk.injEq, heq_eq_eq, true_and] at hQ
              cases hQ; rfl)
          · simp_all only [Sigma.mk.injEq, heq_eq_eq, true_and, ge_iff_le]
            funext i; simp
        · intro ⟨x, hx, hxy⟩ i
          have hx_i := hx i
          convert hx_i using 2 <;> (
            congr 1; simp only [Sigma.mk.injEq, heq_eq_eq, true_and] at hQ
            cases hQ; rfl)
          simp_all
    · -- k < n' + 1, need to eliminate
      have h_pos : n' + 1 > 0 := Nat.succ_pos n'
      have h_le : k ≤ n' := Nat.lt_succ_iff.mp (Nat.lt_of_le_of_ne h hk)
      -- Pattern match on the result of eliminationIteration
      match hQ : FourierMotzkin.eliminationIteration h P with
      | ⟨m', Q⟩ =>
        -- For k < n' + 1, eliminationIteration first does one cycle then recurses
        simp only [FourierMotzkin.eliminationIteration, hk, ↓reduceDIte] at hQ
        -- The goal is: Q.carrier = polyhedronProj h P
        change Q.carrier = polyhedronProj h P
        -- First, Q.carrier = (eliminationIteration h_le (eliminationCycle h_pos P).snd).snd.carrier
        have hQ_eq : Q.carrier = (FourierMotzkin.eliminationIteration h_le
          (FourierMotzkin.eliminationCycle h_pos P).snd).snd.carrier := by
          conv_lhs => rw [← congrArg (fun x => x.snd.carrier) hQ]
        rw [hQ_eq]
        -- Apply IH
        have ih_applied := ih h_le (FourierMotzkin.eliminationCycle h_pos P).snd
        simp only at ih_applied
        rw [ih_applied]
        -- Use polyhedronProj_comp
        exact (polyhedronProj_comp h_le P).symm

/- # Backup helper lemmas that are not used in the proof -/

-- /- Helper: i is in I_pos iff coefficient is positive -/
-- lemma mem_I_pos_iff {m n : Nat} (hn : n > 0) (P : Polyhedron K m n) (i : Fin m) :
--   let lastIdx : Fin n := ⟨n - 1, Nat.sub_lt hn (by omega)⟩
--   let (I_pos, _, _) := FourierMotzkin.partitionIndices hn P
--   i ∈ I_pos ↔ P.A i lastIdx > 0 := by
--   simp only [FourierMotzkin.partitionIndices, Finset.mem_filter, Finset.mem_univ, true_and]

-- /- Helper: i is in I_neg iff coefficient is negative -/
-- lemma mem_I_neg_iff {m n : Nat} (hn : n > 0) (P : Polyhedron K m n) (i : Fin m) :
--   let lastIdx : Fin n := ⟨n - 1, Nat.sub_lt hn (by omega)⟩
--   let (_, I_neg, _) := FourierMotzkin.partitionIndices hn P
--   i ∈ I_neg ↔ P.A i lastIdx < 0 := by
--   simp only [FourierMotzkin.partitionIndices, Finset.mem_filter, Finset.mem_univ, true_and]

-- /- Helper: i is in I_zero iff coefficient is zero -/
-- lemma mem_I_zero_iff {m n : Nat} (hn : n > 0) (P : Polyhedron K m n) (i : Fin m) :
--   let lastIdx : Fin n := ⟨n - 1, Nat.sub_lt hn (by omega)⟩
--   let (_, _, I_zero) := FourierMotzkin.partitionIndices hn P
--   i ∈ I_zero ↔ P.A i lastIdx = 0 := by
--   simp only [FourierMotzkin.partitionIndices, Finset.mem_filter, Finset.mem_univ, true_and]

-- /- Helper: partition sets are disjoint and cover all indices -/
-- lemma partition_complete {m n : Nat} (hn : n > 0) (P : Polyhedron K m n) (i : Fin m) :
--   let lastIdx : Fin n := ⟨n - 1, Nat.sub_lt hn (by omega)⟩
--   let (I_pos, I_neg, I_zero) := FourierMotzkin.partitionIndices hn P
--   (i ∈ I_pos → P.A i lastIdx > 0) ∧
--   (i ∈ I_neg → P.A i lastIdx < 0) ∧
--   (i ∈ I_zero → P.A i lastIdx = 0) := by
--   simp only [FourierMotzkin.partitionIndices, Finset.mem_filter, Finset.mem_univ, true_and]
--   exact ⟨id, id, id⟩

/-!
# Correctness of the computable (ℚ-valued) Fourier–Motzkin elimination

The computable algorithm is simply the generic `FourierMotzkin.eliminationCycle` /
`eliminationIteration` instantiated at the computable field `K = ℚ` (recall
`ComputablePolyhedron m n = Polyhedron ℚ m n`). Because the generic correctness theorems above are
proved over an arbitrary linear-ordered field, the ℚ correctness statements below follow by direct
instantiation — **no `rational_witness` axiom is needed**: the witness produced by the generic
proof (a `Finset.sup'`/`inf'` of the rational bounds) is automatically rational.

We also record `eliminationCycle_toPolyhedron_eq`: the ℚ-algorithm and the ℝ-algorithm produce the
*same* polyhedron once the rational data is cast to the reals. This is a genuine theorem (not just
up to row permutation), because both algorithms share the deterministic `finsetToList` row order.
-/

/- Conversion from `ComputablePolyhedron` (ℚ) to `Polyhedron ℝ` by casting each entry. -/
def ComputablePolyhedron.toPolyhedron {m n : Nat} (P : ComputablePolyhedron m n) :
    Polyhedron ℝ m n :=
  { A := fun i j => (P.A i j : ℝ)
    b := fun i => (P.b i : ℝ) }

/- Helper: the coordinate index `⟨j.val, _⟩` used in the projection statements equals the
embedding `Fin.castLEEmb` used by `proj`. -/
lemma proj_eq_coord {n : Nat} {k : Nat} (h : k ≤ n) (x : Fin n → ℚ) (j : Fin k) :
    proj k n h x j = x ⟨j.val, Nat.lt_of_lt_of_le j.isLt h⟩ := by
  simp only [proj_coords]
  rfl

/- Conversion preserves membership: `P.memProp x ↔ (cast x) ∈ P.toPolyhedron.carrier`. -/
lemma memProp_toPolyhedron {m n : Nat} (P : ComputablePolyhedron m n) (x : Fin n → ℚ) :
    P.memProp x ↔ (fun j => (x j : ℝ)) ∈ P.toPolyhedron.carrier := by
  unfold ComputablePolyhedron.memProp Polyhedron.carrier ComputablePolyhedron.toPolyhedron
  simp only
  constructor
  · intro h i
    specialize h i
    calc (P.b i : ℝ)
      _ ≤ (∑ j, P.A i j * x j : ℚ) := Rat.cast_le.mpr h
      _ = ∑ j, (P.A i j : ℝ) * (x j : ℝ) := by
        rw [Rat.cast_sum]; congr 1; funext j; exact Rat.cast_mul (P.A i j) (x j)
  · intro h i
    specialize h i
    have h_eq : ∑ j, (P.A i j : ℝ) * (x j : ℝ) = ((∑ j, P.A i j * x j) : ℚ) := by
      rw [Rat.cast_sum]; congr 1; funext j; rw [Rat.cast_mul]
    rw [h_eq] at h
    exact Rat.cast_le.mp h

/- **Correctness of a single computable elimination cycle.**
`Q.memProp y` holds iff `y` is the projection (dropping the last coordinate) of some rational
point `x` feasible for `P`. -/
theorem correctComputableFourierMotzkinCycle {m n : Nat} (hn : n > 0)
    (P : ComputablePolyhedron m n) :
    let ⟨_, Q⟩ := FourierMotzkin.eliminationCycle hn P
    ∀ y : Fin (n - 1) → ℚ, ComputablePolyhedron.memProp Q y ↔
      ∃ x : Fin n → ℚ, P.memProp x ∧ ∀ j : Fin (n - 1), y j
      = x ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.sub_le n 1)⟩ := by
  intro y
  have hcorrect : (FourierMotzkin.eliminationCycle hn P).2.carrier
      = polyhedronProj (Nat.sub_le n 1) P := correctFourierMotzkinCycle hn P
  have hmem : y ∈ (FourierMotzkin.eliminationCycle hn P).2.carrier
      ↔ ∃ x : Fin n → ℚ, P.memProp x ∧ ∀ j : Fin (n - 1), y j
        = x ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.sub_le n 1)⟩ := by
    rw [hcorrect]
    simp only [polyhedronProj, mem_setProj_iff_coords]
    constructor
    · rintro ⟨x, hx, hxy⟩
      exact ⟨x, hx, fun j => by rw [hxy j, proj_eq_coord]⟩
    · rintro ⟨x, hx, hxy⟩
      exact ⟨x, hx, fun j => by rw [proj_eq_coord]; exact hxy j⟩
  exact hmem

/- **Correctness of the iterated computable elimination.**
`Q.memProp y` holds iff `y` is the projection onto the first `k` coordinates of some rational
point `x` feasible for `P`. -/
theorem correctComputableFourierMotzkinIteration {m n k : Nat} (h : k ≤ n)
    (P : ComputablePolyhedron m n) :
    let ⟨_, Q⟩ := FourierMotzkin.eliminationIteration h P
    ∀ y : Fin k → ℚ, ComputablePolyhedron.memProp Q y ↔
      ∃ x : Fin n → ℚ, P.memProp x ∧ ∀ j : Fin k, y j = x ⟨j.val, Nat.lt_of_lt_of_le j.isLt h⟩ := by
  intro y
  have hcorrect : (FourierMotzkin.eliminationIteration h P).2.carrier
      = polyhedronProj h P := correctFourierMotzkinIteration h P
  have hmem : y ∈ (FourierMotzkin.eliminationIteration h P).2.carrier
      ↔ ∃ x : Fin n → ℚ, P.memProp x ∧ ∀ j : Fin k, y j
        = x ⟨j.val, Nat.lt_of_lt_of_le j.isLt h⟩ := by
    rw [hcorrect]
    simp only [polyhedronProj, mem_setProj_iff_coords]
    constructor
    · rintro ⟨x, hx, hxy⟩
      exact ⟨x, hx, fun j => by rw [hxy j, proj_eq_coord]⟩
    · rintro ⟨x, hx, hxy⟩
      exact ⟨x, hx, fun j => by rw [proj_eq_coord]; exact hxy j⟩
  exact hmem

/- The index partition is identical whether computed over ℚ or over the cast-to-ℝ polyhedron,
because `Rat.cast` reflects the sign of each coefficient. -/
lemma partitionIndices_toPolyhedron {m n : Nat} (hn : n > 0) (P : ComputablePolyhedron m n) :
    FourierMotzkin.partitionIndices hn P.toPolyhedron
      = FourierMotzkin.partitionIndices hn P := by
  simp only [FourierMotzkin.partitionIndices, ComputablePolyhedron.toPolyhedron]
  refine Prod.ext ?_ (Prod.ext ?_ ?_) <;>
    · apply Finset.filter_congr
      intro i _
      norm_cast

/- **Naturality of `eliminationCycle` under the cast `ℚ → ℝ`.**
Running the algorithm over ℝ on the cast polyhedron yields exactly the cast of the result of
running it over ℚ. Both share the deterministic `finsetToList` row order and the same index
partition (`partitionIndices_toPolyhedron`), so the only difference is the entrywise cast, which
commutes with the field operations. -/
lemma elimCycle_toPolyhedron_natural {m n : Nat} (hn : n > 0) (P : ComputablePolyhedron m n) :
    FourierMotzkin.eliminationCycle hn P.toPolyhedron
      = ⟨(FourierMotzkin.eliminationCycle hn P).1,
         ComputablePolyhedron.toPolyhedron (FourierMotzkin.eliminationCycle hn P).2⟩ := by
  simp only [FourierMotzkin.eliminationCycle]
  rw [partitionIndices_toPolyhedron hn P]
  congr 1
  simp only [ComputablePolyhedron.toPolyhedron]
  congr 1
  · funext idx j
    simp only [apply_dite (Rat.cast (K := ℝ)), Rat.cast_sub, Rat.cast_mul, Rat.cast_zero]
  · funext idx
    simp only [apply_dite (Rat.cast (K := ℝ)), Rat.cast_sub, Rat.cast_mul, Rat.cast_zero]

/- **Structural agreement (Theorem).** The computable (ℚ) cycle and the real (ℝ) cycle produce
the *same* polyhedron once the rational data is cast to ℝ — not merely up to a permutation of
rows, thanks to the shared deterministic ordering. -/
theorem eliminationCycle_toPolyhedron_eq {m n : Nat} (hn : n > 0)
    (P : ComputablePolyhedron m n) :
    let ⟨m_q, Q_q⟩ := FourierMotzkin.eliminationCycle hn P
    let ⟨m_r, Q_r⟩ := FourierMotzkin.eliminationCycle hn P.toPolyhedron
    ∃ (h : m_q = m_r), ComputablePolyhedron.toPolyhedron Q_q = h ▸ Q_r := by
  rw [elimCycle_toPolyhedron_natural hn P]
  exact ⟨rfl, rfl⟩

/-! ## Examples (computable, at `K = ℚ`)

These `#eval`s exercise the algorithm concretely on `ComputablePolyhedron = Polyhedron ℚ`,
confirming the determinized procedure actually computes. -/

/- Example 1: Eliminate one variable from the unit square `[0,1]²` to get the interval `[0,1]`. -/
def exampleSquare2D : ComputablePolyhedron 4 2 :=
  { A := !![1, 0; 0, 1; -1, 0; 0, -1]
    b := ![0, 0, -1, -1] }

def projectedIntervalFME :=
  FourierMotzkin.eliminationCycle (by omega : 2 > 0) exampleSquare2D

#eval projectedIntervalFME.1  -- Number of constraints in projected polyhedron

def testPoint1D : Fin 1 → ℚ := ![1/2]
#eval ComputablePolyhedron.mem projectedIntervalFME.2 testPoint1D  -- Should be true

def testPoint1D_outside : Fin 1 → ℚ := ![2]
#eval ComputablePolyhedron.mem projectedIntervalFME.2 testPoint1D_outside  -- Should be false

/- Example 2: Eliminate all variables of the box `[0,1]³` to check feasibility. -/
def example3DBox : ComputablePolyhedron 6 3 :=
  { A := !![1, 0, 0; 0, 1, 0; 0, 0, 1; -1, 0, 0; 0, -1, 0; 0, 0, -1]
    b := ![0, 0, 0, -1, -1, -1] }

def feasibilityCheck :=
  FourierMotzkin.eliminationIteration (by omega : 0 ≤ 3) example3DBox

#eval feasibilityCheck.1  -- Number of constraints

/- Example 3: A simple 3D → 2D projection. -/
def example3DPoly : ComputablePolyhedron 3 3 :=
  { A := !![1, 0, 1; 0, 1, 1; 0, 0, -1]  -- x₀ + x₂ ≥ 0, x₁ + x₂ ≥ 0, x₂ ≤ 0
    b := ![0, 0, 0] }

def projected2D :=
  FourierMotzkin.eliminationCycle (by omega : 3 > 0) example3DPoly

#eval projected2D.1  -- Number of constraints in 2D projection

def testPoint2D : Fin 2 → ℚ := ![1, 1]
#eval ComputablePolyhedron.mem projected2D.2 testPoint2D

/- Example 4: Complete iteration — project 3D to 1D. -/
def projected1D_from3D :=
  FourierMotzkin.eliminationIteration (by omega : 1 ≤ 3) example3DBox

#eval projected1D_from3D.1  -- Number of constraints
#eval ComputablePolyhedron.mem projected1D_from3D.2 ![1/2]  -- Test point in projected space
