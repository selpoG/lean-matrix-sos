/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/

import MatrixSOS.Proof.ComplexFunctionField.PfisterForm
import MatrixSOS.Proof.TsenProjective
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.MvPolynomial.Ideal
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.Nullstellensatz
import Mathlib.RingTheory.Polynomial.RationalRoot

/-!
# Polynomial reduction over the complex function field
-/

open Matrix Polynomial
open scoped QuadraticAlgebra Matrix
noncomputable section

namespace MatrixSOS

def complexTripleProductWitnessBound (a b c : Polynomial ℂ) : ℕ :=
  a.natDegree + b.natDegree + c.natDegree + 1

def complexPolyOfBoundedCoeffs (N : ℕ) (x : Fin (N + 1) → ℂ) : Polynomial ℂ :=
  ∑ i : Fin (N + 1), C (x i) * X ^ (i : ℕ)

theorem complexPolyOfBoundedCoeffs_natDegree_le
    (N : ℕ) (x : Fin (N + 1) → ℂ) :
    (complexPolyOfBoundedCoeffs N x).natDegree ≤ N := by
  unfold complexPolyOfBoundedCoeffs
  refine Polynomial.natDegree_sum_le_of_forall_le _ _ ?_
  intro i _hi
  exact (Polynomial.natDegree_C_mul_X_pow_le (x i) (i : ℕ)).trans
    (Nat.lt_succ_iff.mp i.isLt)

theorem complexPolyOfBoundedCoeffs_coeff
    (N : ℕ) (x : Fin (N + 1) → ℂ) (i : Fin (N + 1)) :
    (complexPolyOfBoundedCoeffs N x).coeff (i : ℕ) = x i := by
  unfold complexPolyOfBoundedCoeffs
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _hj hji
    simp [show (i : ℕ) ≠ (j : ℕ) by
      intro hij
      exact hji (Fin.ext hij.symm)]
  · intro hi
    exact (hi (Finset.mem_univ i)).elim

def complexBoundedCoeffAt (N : ℕ) (x : Fin (N + 1) → ℂ) (n : ℕ) : ℂ :=
  if hn : n ≤ N then x ⟨n, Nat.lt_succ_of_le hn⟩ else 0

theorem complexPolyOfBoundedCoeffs_coeffAt
    (N : ℕ) (x : Fin (N + 1) → ℂ) (n : ℕ) :
    (complexPolyOfBoundedCoeffs N x).coeff n = complexBoundedCoeffAt N x n := by
  by_cases hn : n ≤ N
  · simpa [complexBoundedCoeffAt, hn] using
      complexPolyOfBoundedCoeffs_coeff N x ⟨n, Nat.lt_succ_of_le hn⟩
  · have hdeg := complexPolyOfBoundedCoeffs_natDegree_le N x
    have hzero :
        (complexPolyOfBoundedCoeffs N x).coeff n = 0 :=
      Polynomial.natDegree_le_iff_coeff_eq_zero.mp hdeg n (Nat.lt_of_not_ge hn)
    simpa [complexBoundedCoeffAt, hn] using hzero

def complexBoundedSquareCoeff (N : ℕ) (x : Fin (N + 1) → ℂ) (n : ℕ) : ℂ :=
  ∑ ij ∈ Finset.antidiagonal n,
    complexBoundedCoeffAt N x ij.1 * complexBoundedCoeffAt N x ij.2

theorem complexPolyOfBoundedCoeffs_sq_coeff
    (N : ℕ) (x : Fin (N + 1) → ℂ) (n : ℕ) :
    ((complexPolyOfBoundedCoeffs N x) ^ 2).coeff n =
      complexBoundedSquareCoeff N x n := by
  rw [pow_two, Polynomial.coeff_mul]
  simp [complexBoundedSquareCoeff, complexPolyOfBoundedCoeffs_coeffAt]

def complexPolyMulBoundedSquareCoeff
    (p : Polynomial ℂ) (N : ℕ) (x : Fin (N + 1) → ℂ) (n : ℕ) : ℂ :=
  ∑ ij ∈ Finset.antidiagonal n,
    p.coeff ij.1 * complexBoundedSquareCoeff N x ij.2

theorem complexPoly_mul_bounded_square_coeff
    (p : Polynomial ℂ) (N : ℕ) (x : Fin (N + 1) → ℂ) (n : ℕ) :
    (p * (complexPolyOfBoundedCoeffs N x) ^ 2).coeff n =
      complexPolyMulBoundedSquareCoeff p N x n := by
  rw [Polynomial.coeff_mul]
  simp [complexPolyMulBoundedSquareCoeff, complexPolyOfBoundedCoeffs_sq_coeff]

def complexTripleProductEquationBound (a b c : Polynomial ℂ) : ℕ :=
  a.natDegree + b.natDegree + c.natDegree +
    2 * complexTripleProductWitnessBound a b c

def complexTripleProductCoeffVariableCount (a b c : Polynomial ℂ) : ℕ :=
  4 * (complexTripleProductWitnessBound a b c + 1)

def complexTripleProductCoeffEquationCount (a b c : Polynomial ℂ) : ℕ :=
  complexTripleProductEquationBound a b c + 1

def complexQuadraticTensorEval
    {ι : Type*} [Fintype ι]
    (Q : ι → ι → ℂ) (x : ι → ℂ) : ℂ :=
  ∑ i : ι, ∑ j : ι, Q i j * x i * x j

def IsComplexQuadraticTensorEval
    {ι : Type*} [Fintype ι]
    (F : (ι → ℂ) → ℂ) : Prop :=
  ∃ Q : ι → ι → ℂ, ∀ x : ι → ℂ, F x = complexQuadraticTensorEval Q x

def complexQuadraticTensorMvPolynomial
    {ι : Type} [Fintype ι]
    (Q : ι → ι → ℂ) : MvPolynomial ι ℂ :=
  ∑ i : ι, ∑ j : ι, MvPolynomial.C (Q i j) * MvPolynomial.X i * MvPolynomial.X j

theorem complexQuadraticTensorMvPolynomial_eval
    {ι : Type} [Fintype ι]
    (Q : ι → ι → ℂ) (x : ι → ℂ) :
    MvPolynomial.eval x (complexQuadraticTensorMvPolynomial Q) =
      complexQuadraticTensorEval Q x := by
  simp [complexQuadraticTensorMvPolynomial, complexQuadraticTensorEval, mul_assoc]

theorem complexQuadraticTensorMvPolynomial_isHomogeneous
    {ι : Type} [Fintype ι]
    (Q : ι → ι → ℂ) :
    (complexQuadraticTensorMvPolynomial Q).IsHomogeneous 2 := by
  classical
  unfold complexQuadraticTensorMvPolynomial
  refine MvPolynomial.IsHomogeneous.sum Finset.univ (fun i =>
      ∑ j : ι, MvPolynomial.C (Q i j) * MvPolynomial.X i * MvPolynomial.X j) 2 ?_
  intro i _hi
  refine MvPolynomial.IsHomogeneous.sum Finset.univ
      (fun j => MvPolynomial.C (Q i j) * MvPolynomial.X i * MvPolynomial.X j) 2 ?_
  intro j _hj
  have hi : (MvPolynomial.X (R := ℂ) i : MvPolynomial ι ℂ).IsHomogeneous 1 :=
    MvPolynomial.isHomogeneous_X (R := ℂ) i
  have hj : (MvPolynomial.X (R := ℂ) j : MvPolynomial ι ℂ).IsHomogeneous 1 :=
    MvPolynomial.isHomogeneous_X (R := ℂ) j
  have hprod :
      (MvPolynomial.X (R := ℂ) i * MvPolynomial.X (R := ℂ) j :
        MvPolynomial ι ℂ).IsHomogeneous (1 + 1) :=
    hi.mul hj
  have hterm :
      (MvPolynomial.C (Q i j) *
          (MvPolynomial.X (R := ℂ) i * MvPolynomial.X (R := ℂ) j) :
        MvPolynomial ι ℂ).IsHomogeneous (1 + 1) :=
    hprod.C_mul (Q i j)
  have hdeg : 1 + 1 = 2 := by norm_num
  simpa [hdeg, mul_assoc] using hterm

/-- Standard homogeneous-polynomial version of the projective dimension-count input over `ℂ`. -/
def ComplexProjectiveQuadraticHomogeneousDimensionStatement : Prop :=
  ∀ {ι κ : Type} [Fintype ι] [Fintype κ],
    Fintype.card κ < Fintype.card ι →
    ∀ P : κ → MvPolynomial ι ℂ,
      (∀ k : κ, (P k).IsHomogeneous 2) →
      ∃ x : ι → ℂ,
        (∃ i : ι, x i ≠ 0) ∧
        ∀ k : κ, MvPolynomial.eval x (P k) = 0

theorem complexProjectiveQuadraticHomogeneousDimensionStatement_theorem :
    ComplexProjectiveQuadraticHomogeneousDimensionStatement := by
  intro ι κ _hι _hκ hcard P hhom
  exact (algebraicallyClosed_commonZero_of_homogeneous ℂ)
    hcard P (fun k => ⟨2, by norm_num, hhom k⟩)

/-- Polynomial version of the projective dimension-count input over `ℂ`. -/
def ComplexProjectiveQuadraticPolynomialDimensionStatement : Prop :=
  ∀ {ι κ : Type} [Fintype ι] [Fintype κ],
    Fintype.card κ < Fintype.card ι →
    ∀ P : κ → MvPolynomial ι ℂ,
      (∀ k : κ, ∃ Q : ι → ι → ℂ, P k = complexQuadraticTensorMvPolynomial Q) →
      ∃ x : ι → ℂ,
        (∃ i : ι, x i ≠ 0) ∧
        ∀ k : κ, MvPolynomial.eval x (P k) = 0

theorem complexProjectiveQuadraticPolynomialDimensionStatement_of_homogeneousDimensionStatement
    (hstmt : ComplexProjectiveQuadraticHomogeneousDimensionStatement) :
    ComplexProjectiveQuadraticPolynomialDimensionStatement := by
  intro ι κ _hι _hκ hcard P hP
  exact hstmt hcard P (fun k => by
    rcases hP k with ⟨Q, hQ⟩
    rw [hQ]
    exact complexQuadraticTensorMvPolynomial_isHomogeneous Q)

theorem isComplexQuadraticTensorEval_zero
    {ι : Type*} [Fintype ι] :
    IsComplexQuadraticTensorEval (fun _x : ι → ℂ => 0) := by
  refine ⟨fun _ _ => 0, ?_⟩
  intro x
  simp [complexQuadraticTensorEval]

theorem isComplexQuadraticTensorEval_add
    {ι : Type*} [Fintype ι]
    {F G : (ι → ℂ) → ℂ}
    (hF : IsComplexQuadraticTensorEval F)
    (hG : IsComplexQuadraticTensorEval G) :
    IsComplexQuadraticTensorEval (fun x => F x + G x) := by
  rcases hF with ⟨QF, hQF⟩
  rcases hG with ⟨QG, hQG⟩
  refine ⟨fun i j => QF i j + QG i j, ?_⟩
  intro x
  change F x + G x = complexQuadraticTensorEval (fun i j => QF i j + QG i j) x
  rw [hQF x, hQG x]
  simp [complexQuadraticTensorEval, add_mul, Finset.sum_add_distrib]

theorem isComplexQuadraticTensorEval_const_mul
    {ι : Type*} [Fintype ι]
    (c : ℂ) {F : (ι → ℂ) → ℂ}
    (hF : IsComplexQuadraticTensorEval F) :
    IsComplexQuadraticTensorEval (fun x => c * F x) := by
  rcases hF with ⟨Q, hQ⟩
  refine ⟨fun i j => c * Q i j, ?_⟩
  intro x
  change c * F x = complexQuadraticTensorEval (fun i j => c * Q i j) x
  rw [hQ x]
  simp [complexQuadraticTensorEval, Finset.mul_sum, mul_assoc]

theorem isComplexQuadraticTensorEval_coord_mul
    {ι : Type*} [Fintype ι]
    (i j : ι) :
    IsComplexQuadraticTensorEval (fun x : ι → ℂ => x i * x j) := by
  classical
  refine ⟨fun a b => if a = i then if b = j then 1 else 0 else 0, ?_⟩
  intro x
  simp [complexQuadraticTensorEval]

theorem isComplexQuadraticTensorEval_finset_sum
    {ι α : Type*} [Fintype ι]
    (s : Finset α) (F : α → (ι → ℂ) → ℂ)
    (hF : ∀ a ∈ s, IsComplexQuadraticTensorEval (F a)) :
    IsComplexQuadraticTensorEval (fun x => ∑ a ∈ s, F a x) := by
  classical
  revert hF
  refine Finset.induction_on s ?_ ?_
  · intro _hF
    simpa using (isComplexQuadraticTensorEval_zero (ι := ι))
  · intro a s has ih hF
    have ha : IsComplexQuadraticTensorEval (F a) := hF a (Finset.mem_insert_self a s)
    have hs : IsComplexQuadraticTensorEval (fun x => ∑ b ∈ s, F b x) := by
      exact ih (fun b hb => hF b (Finset.mem_insert_of_mem hb))
    simpa [Finset.sum_insert has] using isComplexQuadraticTensorEval_add ha hs

def ComplexProjectiveQuadraticDimensionStatement : Prop :=
  ∀ {ι κ : Type} [Fintype ι] [Fintype κ],
    Fintype.card κ < Fintype.card ι →
    ∀ F : κ → (ι → ℂ) → ℂ,
      (∀ k : κ, IsComplexQuadraticTensorEval (F k)) →
      ∃ x : ι → ℂ,
        (∃ i : ι, x i ≠ 0) ∧
        ∀ k : κ, F k x = 0

theorem complexProjectiveQuadraticDimensionStatement_of_polynomialDimensionStatement
    (hstmt : ComplexProjectiveQuadraticPolynomialDimensionStatement) :
    ComplexProjectiveQuadraticDimensionStatement := by
  classical
  intro ι κ _hι _hκ hcard F hF
  let Q : κ → ι → ι → ℂ := fun k => Classical.choose (hF k)
  have hQ : ∀ k x, F k x = complexQuadraticTensorEval (Q k) x := by
    intro k
    exact Classical.choose_spec (hF k)
  let P : κ → MvPolynomial ι ℂ := fun k => complexQuadraticTensorMvPolynomial (Q k)
  rcases hstmt hcard P (fun k => ⟨Q k, rfl⟩) with ⟨x, hnonzero, hzero⟩
  refine ⟨x, hnonzero, ?_⟩
  intro k
  rw [hQ k x]
  rw [← complexQuadraticTensorMvPolynomial_eval (Q k) x]
  exact hzero k

abbrev complexTripleProductCoeffVariableIndex (a b c : Polynomial ℂ) : Type :=
  Fin 4 × Fin (complexTripleProductWitnessBound a b c + 1)

abbrev complexTripleProductCoeffEquationIndex (a b c : Polynomial ℂ) : Type :=
  Fin (complexTripleProductEquationBound a b c + 1)

theorem complexTripleProductCoeffVariableIndex_card
    (a b c : Polynomial ℂ) :
    Fintype.card (complexTripleProductCoeffVariableIndex a b c) =
      complexTripleProductCoeffVariableCount a b c := by
  simp [complexTripleProductCoeffVariableIndex, complexTripleProductCoeffVariableCount]

theorem complexTripleProductCoeffEquationIndex_card
    (a b c : Polynomial ℂ) :
    Fintype.card (complexTripleProductCoeffEquationIndex a b c) =
      complexTripleProductCoeffEquationCount a b c := by
  simp [complexTripleProductCoeffEquationIndex, complexTripleProductCoeffEquationCount]

theorem complexTripleProductCoeffEquationCount_lt_variableCount
    (a b c : Polynomial ℂ) :
    complexTripleProductCoeffEquationCount a b c <
      complexTripleProductCoeffVariableCount a b c := by
  simp [complexTripleProductCoeffEquationCount, complexTripleProductCoeffVariableCount,
    complexTripleProductEquationBound, complexTripleProductWitnessBound]
  omega

theorem complexTripleProductCoeffEquationIndex_card_lt_variableIndex_card
    (a b c : Polynomial ℂ) :
    Fintype.card (complexTripleProductCoeffEquationIndex a b c) <
      Fintype.card (complexTripleProductCoeffVariableIndex a b c) := by
  rw [complexTripleProductCoeffEquationIndex_card,
    complexTripleProductCoeffVariableIndex_card]
  exact complexTripleProductCoeffEquationCount_lt_variableCount a b c

def complexTripleProductCoeffWitness
    (a b c : Polynomial ℂ)
    (coeff : Fin 4 → Fin (complexTripleProductWitnessBound a b c + 1) → ℂ) :
    Fin 4 → Polynomial ℂ :=
  fun i => complexPolyOfBoundedCoeffs (complexTripleProductWitnessBound a b c) (coeff i)

def complexTripleProductCoeffEquation
    (a b c : Polynomial ℂ)
    (coeff : Fin 4 → Fin (complexTripleProductWitnessBound a b c + 1) → ℂ) :
    Polynomial ℂ :=
  Matrix.toBilin' (Matrix.diagonal ![a, b, c, a * b * c])
    (complexTripleProductCoeffWitness a b c coeff)
    (complexTripleProductCoeffWitness a b c coeff)

theorem complexTripleProductCoeffEquation_eq
    (a b c : Polynomial ℂ)
    (coeff : Fin 4 → Fin (complexTripleProductWitnessBound a b c + 1) → ℂ) :
    complexTripleProductCoeffEquation a b c coeff =
      a * (complexTripleProductCoeffWitness a b c coeff 0) ^ 2 +
      b * (complexTripleProductCoeffWitness a b c coeff 1) ^ 2 +
      c * (complexTripleProductCoeffWitness a b c coeff 2) ^ 2 +
      (a * b * c) * (complexTripleProductCoeffWitness a b c coeff 3) ^ 2 := by
  simp [complexTripleProductCoeffEquation, Matrix.toBilin'_apply, Fin.sum_univ_four, pow_two]
  ring

def complexTripleProductCoeffEquationCoeffExplicit
    (a b c : Polynomial ℂ)
    (coeff : Fin 4 → Fin (complexTripleProductWitnessBound a b c + 1) → ℂ)
    (n : ℕ) : ℂ :=
  let W : ℕ := complexTripleProductWitnessBound a b c
  complexPolyMulBoundedSquareCoeff a W (coeff 0) n +
    complexPolyMulBoundedSquareCoeff b W (coeff 1) n +
    complexPolyMulBoundedSquareCoeff c W (coeff 2) n +
    complexPolyMulBoundedSquareCoeff (a * b * c) W (coeff 3) n

theorem complexTripleProductCoeffEquation_coeff_eq_explicit
    (a b c : Polynomial ℂ)
    (coeff : Fin 4 → Fin (complexTripleProductWitnessBound a b c + 1) → ℂ)
    (n : ℕ) :
    (complexTripleProductCoeffEquation a b c coeff).coeff n =
      complexTripleProductCoeffEquationCoeffExplicit a b c coeff n := by
  rw [complexTripleProductCoeffEquation_eq]
  simp [complexTripleProductCoeffEquationCoeffExplicit, complexTripleProductCoeffWitness,
    complexPoly_mul_bounded_square_coeff, Polynomial.coeff_add]

def complexTripleProductVariableAsCoeff
    (a b c : Polynomial ℂ)
    (x : complexTripleProductCoeffVariableIndex a b c → ℂ) :
    Fin 4 → Fin (complexTripleProductWitnessBound a b c + 1) → ℂ :=
  fun i j => x (i, j)

theorem complexBoundedCoeffAt_variableAsCoeff_mul_isQuadraticTensorEval
    (a b c : Polynomial ℂ)
    (i j : Fin 4) (r s : ℕ) :
    IsComplexQuadraticTensorEval
      (fun x : complexTripleProductCoeffVariableIndex a b c → ℂ =>
        complexBoundedCoeffAt (complexTripleProductWitnessBound a b c)
          (complexTripleProductVariableAsCoeff a b c x i) r *
        complexBoundedCoeffAt (complexTripleProductWitnessBound a b c)
          (complexTripleProductVariableAsCoeff a b c x j) s) := by
  let W : ℕ := complexTripleProductWitnessBound a b c
  by_cases hr : r ≤ W
  · by_cases hs : s ≤ W
    · simpa [complexBoundedCoeffAt, complexTripleProductVariableAsCoeff, W, hr, hs] using
        isComplexQuadraticTensorEval_coord_mul
          (ι := complexTripleProductCoeffVariableIndex a b c)
          (i, ⟨r, Nat.lt_succ_of_le hr⟩) (j, ⟨s, Nat.lt_succ_of_le hs⟩)
    · simpa [complexBoundedCoeffAt, W, hr, hs] using
        (isComplexQuadraticTensorEval_zero
          (ι := complexTripleProductCoeffVariableIndex a b c))
  · simpa [complexBoundedCoeffAt, W, hr] using
      (isComplexQuadraticTensorEval_zero
        (ι := complexTripleProductCoeffVariableIndex a b c))

theorem complexBoundedSquareCoeff_variableAsCoeff_isQuadraticTensorEval
    (a b c : Polynomial ℂ)
    (i : Fin 4) (n : ℕ) :
    IsComplexQuadraticTensorEval
      (fun x : complexTripleProductCoeffVariableIndex a b c → ℂ =>
        complexBoundedSquareCoeff (complexTripleProductWitnessBound a b c)
          (complexTripleProductVariableAsCoeff a b c x i) n) := by
  unfold complexBoundedSquareCoeff
  exact isComplexQuadraticTensorEval_finset_sum
    (ι := complexTripleProductCoeffVariableIndex a b c)
    (s := Finset.antidiagonal n)
    (F := fun ij x =>
      complexBoundedCoeffAt (complexTripleProductWitnessBound a b c)
        (complexTripleProductVariableAsCoeff a b c x i) ij.1 *
      complexBoundedCoeffAt (complexTripleProductWitnessBound a b c)
        (complexTripleProductVariableAsCoeff a b c x i) ij.2)
    (fun ij _hij =>
      complexBoundedCoeffAt_variableAsCoeff_mul_isQuadraticTensorEval
        a b c i i ij.1 ij.2)

theorem complexPolyMulBoundedSquareCoeff_variableAsCoeff_isQuadraticTensorEval
    (a b c p : Polynomial ℂ)
    (i : Fin 4) (n : ℕ) :
    IsComplexQuadraticTensorEval
      (fun x : complexTripleProductCoeffVariableIndex a b c → ℂ =>
        complexPolyMulBoundedSquareCoeff p (complexTripleProductWitnessBound a b c)
          (complexTripleProductVariableAsCoeff a b c x i) n) := by
  unfold complexPolyMulBoundedSquareCoeff
  exact isComplexQuadraticTensorEval_finset_sum
    (ι := complexTripleProductCoeffVariableIndex a b c)
    (s := Finset.antidiagonal n)
    (F := fun ij x =>
      p.coeff ij.1 *
        complexBoundedSquareCoeff (complexTripleProductWitnessBound a b c)
          (complexTripleProductVariableAsCoeff a b c x i) ij.2)
    (fun ij _hij =>
      isComplexQuadraticTensorEval_const_mul
        (ι := complexTripleProductCoeffVariableIndex a b c) (p.coeff ij.1)
        (complexBoundedSquareCoeff_variableAsCoeff_isQuadraticTensorEval
          a b c i ij.2))

theorem complexTripleProductCoeffEquationCoeffExplicit_variableAsCoeff_isQuadraticTensorEval
    (a b c : Polynomial ℂ)
    (n : ℕ) :
    IsComplexQuadraticTensorEval
      (fun x : complexTripleProductCoeffVariableIndex a b c → ℂ =>
        complexTripleProductCoeffEquationCoeffExplicit a b c
          (complexTripleProductVariableAsCoeff a b c x) n) := by
  unfold complexTripleProductCoeffEquationCoeffExplicit
  apply isComplexQuadraticTensorEval_add
  · apply isComplexQuadraticTensorEval_add
    · apply isComplexQuadraticTensorEval_add
      · simpa using
          complexPolyMulBoundedSquareCoeff_variableAsCoeff_isQuadraticTensorEval
            a b c a 0 n
      · simpa using
          complexPolyMulBoundedSquareCoeff_variableAsCoeff_isQuadraticTensorEval
            a b c b 1 n
    · simpa using
        complexPolyMulBoundedSquareCoeff_variableAsCoeff_isQuadraticTensorEval
          a b c c 2 n
  · simpa using
      complexPolyMulBoundedSquareCoeff_variableAsCoeff_isQuadraticTensorEval
        a b c (a * b * c) 3 n

theorem complexTripleProductCoeffEquation_natDegree_le
    (a b c : Polynomial ℂ)
    (coeff : Fin 4 → Fin (complexTripleProductWitnessBound a b c + 1) → ℂ) :
    (complexTripleProductCoeffEquation a b c coeff).natDegree ≤
      complexTripleProductEquationBound a b c := by
  let W : ℕ := complexTripleProductWitnessBound a b c
  let z : Fin 4 → Polynomial ℂ := complexTripleProductCoeffWitness a b c coeff
  have hz : ∀ i : Fin 4, (z i).natDegree ≤ W := by
    intro i
    simpa [z, W, complexTripleProductCoeffWitness] using
      complexPolyOfBoundedCoeffs_natDegree_le W (coeff i)
  have h0 : (a * (z 0) ^ 2).natDegree ≤ complexTripleProductEquationBound a b c := by
    calc
      (a * (z 0) ^ 2).natDegree
          ≤ a.natDegree + ((z 0) ^ 2).natDegree := Polynomial.natDegree_mul_le
      _ ≤ a.natDegree + 2 * W := by
            exact add_le_add_right (Polynomial.natDegree_pow_le_of_le 2 (hz 0)) _
      _ ≤ complexTripleProductEquationBound a b c := by
            simp [complexTripleProductEquationBound, W, complexTripleProductWitnessBound]
            omega
  have h1 : (b * (z 1) ^ 2).natDegree ≤ complexTripleProductEquationBound a b c := by
    calc
      (b * (z 1) ^ 2).natDegree
          ≤ b.natDegree + ((z 1) ^ 2).natDegree := Polynomial.natDegree_mul_le
      _ ≤ b.natDegree + 2 * W := by
            exact add_le_add_right (Polynomial.natDegree_pow_le_of_le 2 (hz 1)) _
      _ ≤ complexTripleProductEquationBound a b c := by
            simp [complexTripleProductEquationBound, W, complexTripleProductWitnessBound]
            omega
  have h2 : (c * (z 2) ^ 2).natDegree ≤ complexTripleProductEquationBound a b c := by
    calc
      (c * (z 2) ^ 2).natDegree
          ≤ c.natDegree + ((z 2) ^ 2).natDegree := Polynomial.natDegree_mul_le
      _ ≤ c.natDegree + 2 * W := by
            exact add_le_add_right (Polynomial.natDegree_pow_le_of_le 2 (hz 2)) _
      _ ≤ complexTripleProductEquationBound a b c := by
            simp [complexTripleProductEquationBound, W, complexTripleProductWitnessBound]
  have habc : (a * b * c).natDegree ≤ a.natDegree + b.natDegree + c.natDegree := by
    calc
      (a * b * c).natDegree
          ≤ (a * b).natDegree + c.natDegree := Polynomial.natDegree_mul_le
      _ ≤ a.natDegree + b.natDegree + c.natDegree := by
            have hab : (a * b).natDegree ≤ a.natDegree + b.natDegree :=
              Polynomial.natDegree_mul_le
            omega
  have h3 :
      ((a * b * c) * (z 3) ^ 2).natDegree ≤
        complexTripleProductEquationBound a b c := by
    calc
      ((a * b * c) * (z 3) ^ 2).natDegree
          ≤ (a * b * c).natDegree + ((z 3) ^ 2).natDegree :=
              Polynomial.natDegree_mul_le
      _ ≤ (a.natDegree + b.natDegree + c.natDegree) + 2 * W := by
            exact add_le_add habc (Polynomial.natDegree_pow_le_of_le 2 (hz 3))
      _ ≤ complexTripleProductEquationBound a b c := by
            simp [complexTripleProductEquationBound, W, complexTripleProductWitnessBound]
  rw [complexTripleProductCoeffEquation_eq]
  change (a * (z 0) ^ 2 + b * (z 1) ^ 2 + c * (z 2) ^ 2 +
      (a * b * c) * (z 3) ^ 2).natDegree ≤ complexTripleProductEquationBound a b c
  have h01 :
      (a * (z 0) ^ 2 + b * (z 1) ^ 2).natDegree ≤
        complexTripleProductEquationBound a b c :=
    Polynomial.natDegree_add_le_of_degree_le h0 h1
  have h012 :
      (a * (z 0) ^ 2 + b * (z 1) ^ 2 + c * (z 2) ^ 2).natDegree ≤
        complexTripleProductEquationBound a b c :=
    Polynomial.natDegree_add_le_of_degree_le h01 h2
  exact Polynomial.natDegree_add_le_of_degree_le h012 h3

/-- Finite-coefficient version of the bounded polynomial triple-product statement.  The unknowns are
the coefficients of four polynomials of the fixed witness bound, and the equation is expressed as
vanishing of all coefficients of the resulting diagonal quadratic polynomial. -/
def ComplexPolyMonicTripleProductThreeNoPairSquareQuad4CoefficientStatement : Prop :=
  ∀ {a b c : Polynomial ℂ},
    a.Monic →
    b.Monic →
    c.Monic →
    ¬ IsSquare (a * b) →
    ¬ IsSquare (a * c) →
    ¬ IsSquare (b * c) →
    ∃ coeff :
      Fin 4 → Fin (complexTripleProductWitnessBound a b c + 1) → ℂ,
      ((complexTripleProductCoeffWitness a b c coeff) 0 ≠ 0 ∨
        (complexTripleProductCoeffWitness a b c coeff) 1 ≠ 0 ∨
        (complexTripleProductCoeffWitness a b c coeff) 2 ≠ 0 ∨
        (complexTripleProductCoeffWitness a b c coeff) 3 ≠ 0) ∧
      (∀ k : ℕ, (complexTripleProductCoeffEquation a b c coeff).coeff k = 0)

/-- Fully finite coefficient endpoint with an explicit degree certificate for the diagonal
equation.  The coefficient vanishing hypotheses are indexed only by
`Fin (complexTripleProductEquationBound a b c + 1)`. -/
def ComplexPolyMonicTripleProductThreeNoPairSquareQuad4FiniteCoefficientStatement : Prop :=
  ∀ {a b c : Polynomial ℂ},
    a.Monic →
    b.Monic →
    c.Monic →
    ¬ IsSquare (a * b) →
    ¬ IsSquare (a * c) →
    ¬ IsSquare (b * c) →
    ∃ coeff :
      Fin 4 → Fin (complexTripleProductWitnessBound a b c + 1) → ℂ,
      ((complexTripleProductCoeffWitness a b c coeff) 0 ≠ 0 ∨
        (complexTripleProductCoeffWitness a b c coeff) 1 ≠ 0 ∨
        (complexTripleProductCoeffWitness a b c coeff) 2 ≠ 0 ∨
        (complexTripleProductCoeffWitness a b c coeff) 3 ≠ 0) ∧
      (complexTripleProductCoeffEquation a b c coeff).natDegree ≤
        complexTripleProductEquationBound a b c ∧
      (∀ k : Fin (complexTripleProductEquationBound a b c + 1),
        (complexTripleProductCoeffEquation a b c coeff).coeff (k : ℕ) = 0)

/-- Fully finite coefficient endpoint without a separate degree certificate.  The fixed witness
bound already implies the degree bound for the diagonal equation. -/
def ComplexPolyMonicTripleProductThreeNoPairSquareQuad4PureFiniteCoefficientStatement : Prop :=
  ∀ {a b c : Polynomial ℂ},
    a.Monic →
    b.Monic →
    c.Monic →
    ¬ IsSquare (a * b) →
    ¬ IsSquare (a * c) →
    ¬ IsSquare (b * c) →
    ∃ coeff :
      Fin 4 → Fin (complexTripleProductWitnessBound a b c + 1) → ℂ,
      ((complexTripleProductCoeffWitness a b c coeff) 0 ≠ 0 ∨
        (complexTripleProductCoeffWitness a b c coeff) 1 ≠ 0 ∨
        (complexTripleProductCoeffWitness a b c coeff) 2 ≠ 0 ∨
        (complexTripleProductCoeffWitness a b c coeff) 3 ≠ 0) ∧
      (∀ k : Fin (complexTripleProductEquationBound a b c + 1),
        (complexTripleProductCoeffEquation a b c coeff).coeff (k : ℕ) = 0)

theorem complexTripleProductCoeffWitness_ne_zero_of_coeff_ne_zero
    (a b c : Polynomial ℂ)
    (coeff : Fin 4 → Fin (complexTripleProductWitnessBound a b c + 1) → ℂ)
    (i : Fin 4)
    (j : Fin (complexTripleProductWitnessBound a b c + 1))
    (hij : coeff i j ≠ 0) :
    complexTripleProductCoeffWitness a b c coeff i ≠ 0 := by
  intro hzero
  have hcoeff :=
    congrArg (fun p : Polynomial ℂ => p.coeff (j : ℕ)) hzero
  change (complexTripleProductCoeffWitness a b c coeff i).coeff (j : ℕ) =
      (0 : Polynomial ℂ).coeff (j : ℕ) at hcoeff
  rw [Polynomial.coeff_zero] at hcoeff
  have hrecover :
      (complexTripleProductCoeffWitness a b c coeff i).coeff (j : ℕ) = coeff i j := by
    simpa [complexTripleProductCoeffWitness] using
      complexPolyOfBoundedCoeffs_coeff (complexTripleProductWitnessBound a b c) (coeff i) j
  exact hij (hrecover.symm.trans hcoeff)

/-- Pure finite coefficient endpoint with the witness nonzero condition also expressed on
coefficients. -/
def ComplexPolyMonicTripleProductThreeNoPairSquareQuad4PureFiniteNonzeroCoefficientStatement : Prop :=
  ∀ {a b c : Polynomial ℂ},
    a.Monic →
    b.Monic →
    c.Monic →
    ¬ IsSquare (a * b) →
    ¬ IsSquare (a * c) →
    ¬ IsSquare (b * c) →
    ∃ coeff :
      Fin 4 → Fin (complexTripleProductWitnessBound a b c + 1) → ℂ,
      (∃ i : Fin 4, ∃ j : Fin (complexTripleProductWitnessBound a b c + 1),
        coeff i j ≠ 0) ∧
      (∀ k : Fin (complexTripleProductEquationBound a b c + 1),
        (complexTripleProductCoeffEquation a b c coeff).coeff (k : ℕ) = 0)

/-- Fully explicit finite coefficient endpoint.  The diagonal equation is expressed by the
finite convolution formula `complexTripleProductCoeffEquationCoeffExplicit`, and the nonzero
condition is also coefficient-level. -/
def ComplexPolyMonicTripleProductThreeNoPairSquareQuad4PureFiniteExplicitCoefficientStatement : Prop :=
  ∀ {a b c : Polynomial ℂ},
    a.Monic →
    b.Monic →
    c.Monic →
    ¬ IsSquare (a * b) →
    ¬ IsSquare (a * c) →
    ¬ IsSquare (b * c) →
    ∃ coeff :
      Fin 4 → Fin (complexTripleProductWitnessBound a b c + 1) → ℂ,
      (∃ i : Fin 4, ∃ j : Fin (complexTripleProductWitnessBound a b c + 1),
        coeff i j ≠ 0) ∧
      (∀ k : Fin (complexTripleProductEquationBound a b c + 1),
        complexTripleProductCoeffEquationCoeffExplicit a b c coeff (k : ℕ) = 0)

/-- Same explicit finite endpoint, but with the unknown coefficients represented as a single
function on the finite variable index. -/
def ComplexPolyMonicTripleProductThreeNoPairSquareQuad4VariableExplicitCoefficientStatement : Prop :=
  ∀ {a b c : Polynomial ℂ},
    a.Monic →
    b.Monic →
    c.Monic →
    ¬ IsSquare (a * b) →
    ¬ IsSquare (a * c) →
    ¬ IsSquare (b * c) →
    ∃ x : complexTripleProductCoeffVariableIndex a b c → ℂ,
      (∃ v : complexTripleProductCoeffVariableIndex a b c, x v ≠ 0) ∧
      (∀ k : complexTripleProductCoeffEquationIndex a b c,
        complexTripleProductCoeffEquationCoeffExplicit a b c
          (complexTripleProductVariableAsCoeff a b c x) (k : ℕ) = 0)

theorem complexPolyMonicTripleProductThreeNoPairSquareQuad4PureFiniteExplicitCoefficientStatement_of_variableExplicitCoefficientStatement
    (hstmt :
      ComplexPolyMonicTripleProductThreeNoPairSquareQuad4VariableExplicitCoefficientStatement) :
    ComplexPolyMonicTripleProductThreeNoPairSquareQuad4PureFiniteExplicitCoefficientStatement := by
  intro a b c ha hb hc hab hac hbc
  rcases hstmt ha hb hc hab hac hbc with ⟨x, hnonzero, hzero⟩
  refine ⟨complexTripleProductVariableAsCoeff a b c x, ?_, ?_⟩
  · rcases hnonzero with ⟨⟨i, j⟩, hij⟩
    exact ⟨i, j, hij⟩
  · intro k
    exact hzero k

theorem complexPolyMonicTripleProductThreeNoPairSquareQuad4VariableExplicitCoefficientStatement_of_projectiveQuadraticDimensionStatement
    (hstmt : ComplexProjectiveQuadraticDimensionStatement) :
    ComplexPolyMonicTripleProductThreeNoPairSquareQuad4VariableExplicitCoefficientStatement := by
  intro a b c _ha _hb _hc _hab _hac _hbc
  let F :
      complexTripleProductCoeffEquationIndex a b c →
        (complexTripleProductCoeffVariableIndex a b c → ℂ) → ℂ :=
    fun k x =>
      complexTripleProductCoeffEquationCoeffExplicit a b c
        (complexTripleProductVariableAsCoeff a b c x) (k : ℕ)
  have hquad : ∀ k, IsComplexQuadraticTensorEval (F k) := by
    intro k
    dsimp [F]
    exact
      complexTripleProductCoeffEquationCoeffExplicit_variableAsCoeff_isQuadraticTensorEval
        a b c (k : ℕ)
  have hlt :
      Fintype.card (complexTripleProductCoeffEquationIndex a b c) <
        Fintype.card (complexTripleProductCoeffVariableIndex a b c) :=
    complexTripleProductCoeffEquationIndex_card_lt_variableIndex_card a b c
  rcases hstmt
      (ι := complexTripleProductCoeffVariableIndex a b c)
      (κ := complexTripleProductCoeffEquationIndex a b c)
      hlt
      F hquad with
    ⟨x, hnonzero, hzero⟩
  exact ⟨x, hnonzero, hzero⟩

theorem complexPolyMonicTripleProductThreeNoPairSquareQuad4PureFiniteNonzeroCoefficientStatement_of_pureFiniteExplicitCoefficientStatement
    (hstmt :
      ComplexPolyMonicTripleProductThreeNoPairSquareQuad4PureFiniteExplicitCoefficientStatement) :
    ComplexPolyMonicTripleProductThreeNoPairSquareQuad4PureFiniteNonzeroCoefficientStatement := by
  intro a b c ha hb hc hab hac hbc
  rcases hstmt ha hb hc hab hac hbc with ⟨coeff, hnonzero, hexplicit⟩
  refine ⟨coeff, hnonzero, ?_⟩
  intro k
  rw [complexTripleProductCoeffEquation_coeff_eq_explicit]
  exact hexplicit k

theorem complexPolyMonicTripleProductThreeNoPairSquareQuad4PureFiniteCoefficientStatement_of_pureFiniteNonzeroCoefficientStatement
    (hstmt :
      ComplexPolyMonicTripleProductThreeNoPairSquareQuad4PureFiniteNonzeroCoefficientStatement) :
    ComplexPolyMonicTripleProductThreeNoPairSquareQuad4PureFiniteCoefficientStatement := by
  intro a b c ha hb hc hab hac hbc
  rcases hstmt ha hb hc hab hac hbc with ⟨coeff, ⟨i, j, hij⟩, hfin⟩
  refine ⟨coeff, ?_, hfin⟩
  have hzi :
      complexTripleProductCoeffWitness a b c coeff i ≠ 0 :=
    complexTripleProductCoeffWitness_ne_zero_of_coeff_ne_zero a b c coeff i j hij
  fin_cases i
  · exact Or.inl (by simpa using hzi)
  · exact Or.inr <| Or.inl (by simpa using hzi)
  · exact Or.inr <| Or.inr <| Or.inl (by simpa using hzi)
  · exact Or.inr <| Or.inr <| Or.inr (by simpa using hzi)

theorem complexPolyMonicTripleProductThreeNoPairSquareQuad4FiniteCoefficientStatement_of_pureFiniteCoefficientStatement
    (hstmt : ComplexPolyMonicTripleProductThreeNoPairSquareQuad4PureFiniteCoefficientStatement) :
    ComplexPolyMonicTripleProductThreeNoPairSquareQuad4FiniteCoefficientStatement := by
  intro a b c ha hb hc hab hac hbc
  rcases hstmt ha hb hc hab hac hbc with ⟨coeff, hnonzero, hfin⟩
  exact ⟨coeff, hnonzero, complexTripleProductCoeffEquation_natDegree_le a b c coeff, hfin⟩

theorem complexPolyMonicTripleProductThreeNoPairSquareQuad4CoefficientStatement_of_finiteCoefficientStatement
    (hstmt : ComplexPolyMonicTripleProductThreeNoPairSquareQuad4FiniteCoefficientStatement) :
    ComplexPolyMonicTripleProductThreeNoPairSquareQuad4CoefficientStatement := by
  intro a b c ha hb hc hab hac hbc
  rcases hstmt ha hb hc hab hac hbc with ⟨coeff, hnonzero, hdeg, hfin⟩
  refine ⟨coeff, hnonzero, ?_⟩
  intro k
  by_cases hk : k ≤ complexTripleProductEquationBound a b c
  · exact hfin ⟨k, Nat.lt_succ_of_le hk⟩
  · exact Polynomial.natDegree_le_iff_coeff_eq_zero.mp hdeg k (Nat.lt_of_not_ge hk)

theorem complexPolyMonicTripleProductThreeNoPairSquareQuad4BoundedStatement_of_coefficientStatement
    (hstmt : ComplexPolyMonicTripleProductThreeNoPairSquareQuad4CoefficientStatement) :
    ComplexPolyMonicTripleProductThreeNoPairSquareQuad4BoundedIsotropicStatement := by
  intro a b c ha hb hc hab hac hbc
  rcases hstmt ha hb hc hab hac hbc with ⟨coeff, hnonzero, hcoeff⟩
  let N : ℕ := complexTripleProductWitnessBound a b c
  let z : Fin 4 → Polynomial ℂ := complexTripleProductCoeffWitness a b c coeff
  refine ⟨z, ?_, ?_, ?_⟩
  · intro i
    simpa [z, N, complexTripleProductWitnessBound, complexTripleProductCoeffWitness] using
      complexPolyOfBoundedCoeffs_natDegree_le N (coeff i)
  · simpa [z, N] using hnonzero
  · apply Polynomial.ext
    intro k
    rw [Polynomial.coeff_zero]
    simpa [z, N, complexTripleProductCoeffEquation] using hcoeff k

theorem complexPolyMonicTripleProductThreeNoPairSquareQuad4Statement_of_boundedStatement
    (hstmt : ComplexPolyMonicTripleProductThreeNoPairSquareQuad4BoundedIsotropicStatement) :
    ComplexPolyMonicTripleProductThreeNoPairSquareQuad4IsotropicStatement := by
  intro a b c ha hb hc hab hac hbc
  rcases hstmt ha hb hc hab hac hbc with ⟨z, _hdeg, hnonzero, hiso⟩
  exact ⟨z, hnonzero, hiso⟩

theorem complexPolyMonicTripleProductThreeNoPairSquareQuad4Statement_of_coefficientStatement
    (hstmt : ComplexPolyMonicTripleProductThreeNoPairSquareQuad4CoefficientStatement) :
    ComplexPolyMonicTripleProductThreeNoPairSquareQuad4IsotropicStatement :=
  complexPolyMonicTripleProductThreeNoPairSquareQuad4Statement_of_boundedStatement
    (complexPolyMonicTripleProductThreeNoPairSquareQuad4BoundedStatement_of_coefficientStatement hstmt)

theorem complexPolyMonicTripleProductThreeNoPairSquareQuad4Statement_of_finiteCoefficientStatement
    (hstmt : ComplexPolyMonicTripleProductThreeNoPairSquareQuad4FiniteCoefficientStatement) :
    ComplexPolyMonicTripleProductThreeNoPairSquareQuad4IsotropicStatement :=
  complexPolyMonicTripleProductThreeNoPairSquareQuad4Statement_of_coefficientStatement
    (complexPolyMonicTripleProductThreeNoPairSquareQuad4CoefficientStatement_of_finiteCoefficientStatement hstmt)

theorem complexPolyMonicTripleProductThreeNoPairSquareQuad4Statement_of_pureFiniteCoefficientStatement
    (hstmt : ComplexPolyMonicTripleProductThreeNoPairSquareQuad4PureFiniteCoefficientStatement) :
    ComplexPolyMonicTripleProductThreeNoPairSquareQuad4IsotropicStatement :=
  complexPolyMonicTripleProductThreeNoPairSquareQuad4Statement_of_finiteCoefficientStatement
    (complexPolyMonicTripleProductThreeNoPairSquareQuad4FiniteCoefficientStatement_of_pureFiniteCoefficientStatement hstmt)

theorem complexPolyMonicTripleProductThreeNoPairSquareQuad4Statement_of_pureFiniteNonzeroCoefficientStatement
    (hstmt :
      ComplexPolyMonicTripleProductThreeNoPairSquareQuad4PureFiniteNonzeroCoefficientStatement) :
    ComplexPolyMonicTripleProductThreeNoPairSquareQuad4IsotropicStatement :=
  complexPolyMonicTripleProductThreeNoPairSquareQuad4Statement_of_pureFiniteCoefficientStatement
    (complexPolyMonicTripleProductThreeNoPairSquareQuad4PureFiniteCoefficientStatement_of_pureFiniteNonzeroCoefficientStatement
      hstmt)

theorem complexPolyMonicTripleProductThreeNoPairSquareQuad4Statement_of_pureFiniteExplicitCoefficientStatement
    (hstmt :
      ComplexPolyMonicTripleProductThreeNoPairSquareQuad4PureFiniteExplicitCoefficientStatement) :
    ComplexPolyMonicTripleProductThreeNoPairSquareQuad4IsotropicStatement :=
  complexPolyMonicTripleProductThreeNoPairSquareQuad4Statement_of_pureFiniteNonzeroCoefficientStatement
    (complexPolyMonicTripleProductThreeNoPairSquareQuad4PureFiniteNonzeroCoefficientStatement_of_pureFiniteExplicitCoefficientStatement
      hstmt)

theorem complexPolyMonicTripleProductThreeNoPairSquareQuad4Statement_of_projectiveQuadraticDimensionStatement
    (hstmt : ComplexProjectiveQuadraticDimensionStatement) :
    ComplexPolyMonicTripleProductThreeNoPairSquareQuad4IsotropicStatement :=
  complexPolyMonicTripleProductThreeNoPairSquareQuad4Statement_of_pureFiniteExplicitCoefficientStatement
    (complexPolyMonicTripleProductThreeNoPairSquareQuad4PureFiniteExplicitCoefficientStatement_of_variableExplicitCoefficientStatement
      (complexPolyMonicTripleProductThreeNoPairSquareQuad4VariableExplicitCoefficientStatement_of_projectiveQuadraticDimensionStatement
        hstmt))

theorem complexPolyMonicTripleProductNoPairSquareQuad4Statement_of_threeNoPairSquareStatement
    (hstmt : ComplexPolyMonicTripleProductThreeNoPairSquareQuad4IsotropicStatement) :
    ComplexPolyMonicTripleProductNoPairSquareQuad4IsotropicStatement := by
  intro a b c ha hb hc hab hac _haabc hbc _hbabc _hcabc
  exact hstmt ha hb hc hab hac hbc

theorem complexPolyMonicQuad4ProductSquareNoPairSquareIsotropicStatement_of_tripleProductStatement
    (hstmt : ComplexPolyMonicTripleProductQuad4IsotropicStatement) :
    ComplexPolyMonicQuad4ProductSquareNoPairSquareIsotropicStatement := by
  intro d hmonic hprod _h01 _h02 _h03 _h12 _h13 _h23
  rcases hprod with ⟨s, hs⟩
  rcases hstmt (hmonic 0) (hmonic 1) (hmonic 2) with ⟨y, hyNonzero, hy⟩
  have hs0 : s ≠ 0 := by
    intro hs0
    have hprod0 : d 0 * d 1 * d 2 * d 3 ≠ 0 := by
      exact mul_ne_zero
        (mul_ne_zero (mul_ne_zero (hmonic 0).ne_zero (hmonic 1).ne_zero) (hmonic 2).ne_zero)
        (hmonic 3).ne_zero
    apply hprod0
    simpa [hs0] using hs
  have hd0120 : d 0 * d 1 * d 2 ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (hmonic 0).ne_zero (hmonic 1).ne_zero) (hmonic 2).ne_zero
  let z : Fin 4 → Polynomial ℂ := ![s * y 0, s * y 1, s * y 2, (d 0 * d 1 * d 2) * y 3]
  refine ⟨z, ?_, ?_⟩
  · rcases hyNonzero with hy0 | hy1 | hy2 | hy3
    · exact Or.inl (mul_ne_zero hs0 hy0)
    · exact Or.inr <| Or.inl (mul_ne_zero hs0 hy1)
    · exact Or.inr <| Or.inr <| Or.inl (mul_ne_zero hs0 hy2)
    · exact Or.inr <| Or.inr <| Or.inr (mul_ne_zero hd0120 hy3)
  · have hy' : y 0 * d 0 * y 0 + y 1 * d 1 * y 1 + y 2 * d 2 * y 2 +
        y 3 * (d 0 * d 1 * d 2) * y 3 = 0 := by
      simpa [Matrix.toBilin'_apply, Fin.sum_univ_four] using hy
    have hs' : s ^ 2 = d 0 * d 1 * d 2 * d 3 := by
      simpa [pow_two] using hs.symm
    simp only [Fin.isValue, Matrix.toBilin'_apply, Fin.sum_univ_four, cons_val_zero,
      cons_val_one, cons_val, Matrix.diagonal_apply_eq, ne_eq, zero_ne_one,
      not_false_eq_true, Matrix.diagonal_apply_ne, mul_zero, zero_mul, add_zero,
      Fin.reduceEq, one_ne_zero, zero_add, z]
    calc
      s * y 0 * d 0 * (s * y 0) +
              s * y 1 * d 1 * (s * y 1) +
            s * y 2 * d 2 * (s * y 2) +
          (d 0 * d 1 * d 2 * y 3) * d 3 * (d 0 * d 1 * d 2 * y 3)
          = s ^ 2 * (y 0 * d 0 * y 0 + y 1 * d 1 * y 1 + y 2 * d 2 * y 2 +
              y 3 * (d 0 * d 1 * d 2) * y 3) := by
              conv_lhs =>
                rw [show s * y 0 * d 0 * (s * y 0) +
                        s * y 1 * d 1 * (s * y 1) +
                      s * y 2 * d 2 * (s * y 2) +
                    (d 0 * d 1 * d 2 * y 3) * d 3 * (d 0 * d 1 * d 2 * y 3) =
                      s ^ 2 * (y 0 * d 0 * y 0 + y 1 * d 1 * y 1 + y 2 * d 2 * y 2) +
                        (d 0 * d 1 * d 2 * d 3) *
                          (y 3 * (d 0 * d 1 * d 2) * y 3) by ring]
              rw [← hs']
              ring
      _ = 0 := by simp [hy']

theorem complexPolyMonicDiagonalQuad4SquareDetNoPairSquareIsotropicStatement_of_productStatement
    (hstmt : ComplexPolyMonicQuad4ProductSquareNoPairSquareIsotropicStatement) :
    ComplexPolyMonicDiagonalQuad4SquareDetNoPairSquareIsotropicStatement := by
  intro d hmonic hdet h01 h02 h03 h12 h13 h23
  have hprod : IsSquare (d 0 * d 1 * d 2 * d 3) := by
    simpa [Matrix.det_diagonal, Fin.prod_univ_four] using hdet
  exact hstmt hmonic hprod h01 h02 h03 h12 h13 h23

theorem complexPolyDiagonalQuad4_isotropic_of_firstPairSquare
    {d : Fin 4 → Polynomial ℂ}
    (hd1 : d 1 ≠ 0)
    (hsq01 : IsSquare (d 0 * d 1)) :
    ∃ z : Fin 4 → Polynomial ℂ,
      (z 0 ≠ 0 ∨ z 1 ≠ 0 ∨ z 2 ≠ 0 ∨ z 3 ≠ 0) ∧
      Matrix.toBilin' (Matrix.diagonal d) z z = 0 := by
  rcases hsq01 with ⟨s, hs⟩
  let z : Fin 4 → Polynomial ℂ := ![d 1, Polynomial.C Complex.I * s, 0, 0]
  refine ⟨z, Or.inl ?_, ?_⟩
  · simpa [z] using hd1
  · have hs' : s ^ 2 = d 0 * d 1 := by
      simpa [pow_two] using hs.symm
    simp only [Fin.isValue, Matrix.toBilin'_apply, Fin.sum_univ_four, cons_val_zero,
      cons_val_one, cons_val, mul_zero, add_zero, Matrix.diagonal_apply_eq, ne_eq,
      not_false_eq_true, Matrix.diagonal_apply_ne, zero_mul, zero_add,
      Fin.reduceEq, z]
    rw [show Polynomial.C Complex.I * s * d 1 * (Polynomial.C Complex.I * s) =
        (Polynomial.C Complex.I * Polynomial.C Complex.I) * s ^ 2 * d 1 by ring]
    rw [show (Polynomial.C Complex.I * Polynomial.C Complex.I : Polynomial ℂ) = -1 by
      rw [← Polynomial.C_mul]
      rw [Complex.I_mul_I]
      simp]
    rw [hs']
    ring

theorem complexPolyDiagonalQuad4_isotropic_of_pair02Square
    {d : Fin 4 → Polynomial ℂ}
    (hd2 : d 2 ≠ 0)
    (hsq02 : IsSquare (d 0 * d 2)) :
    ∃ z : Fin 4 → Polynomial ℂ,
      (z 0 ≠ 0 ∨ z 1 ≠ 0 ∨ z 2 ≠ 0 ∨ z 3 ≠ 0) ∧
      Matrix.toBilin' (Matrix.diagonal d) z z = 0 := by
  rcases hsq02 with ⟨s, hs⟩
  let z : Fin 4 → Polynomial ℂ := ![d 2, 0, Polynomial.C Complex.I * s, 0]
  refine ⟨z, Or.inl ?_, ?_⟩
  · simpa [z] using hd2
  · have hs' : s ^ 2 = d 0 * d 2 := by
      simpa [pow_two] using hs.symm
    simp only [Fin.isValue, Matrix.toBilin'_apply, Fin.sum_univ_four, cons_val_zero,
      cons_val_one, cons_val, mul_zero, add_zero, Matrix.diagonal_apply_eq, ne_eq,
      not_false_eq_true, Matrix.diagonal_apply_ne, zero_mul, zero_add,
      Fin.reduceEq, z]
    rw [show Polynomial.C Complex.I * s * d 2 * (Polynomial.C Complex.I * s) =
        (Polynomial.C Complex.I * Polynomial.C Complex.I) * s ^ 2 * d 2 by ring]
    rw [show (Polynomial.C Complex.I * Polynomial.C Complex.I : Polynomial ℂ) = -1 by
      rw [← Polynomial.C_mul]
      rw [Complex.I_mul_I]
      simp]
    rw [hs']
    ring

theorem complexPolyDiagonalQuad4_isotropic_of_pair03Square
    {d : Fin 4 → Polynomial ℂ}
    (hd3 : d 3 ≠ 0)
    (hsq03 : IsSquare (d 0 * d 3)) :
    ∃ z : Fin 4 → Polynomial ℂ,
      (z 0 ≠ 0 ∨ z 1 ≠ 0 ∨ z 2 ≠ 0 ∨ z 3 ≠ 0) ∧
      Matrix.toBilin' (Matrix.diagonal d) z z = 0 := by
  rcases hsq03 with ⟨s, hs⟩
  let z : Fin 4 → Polynomial ℂ := ![d 3, 0, 0, Polynomial.C Complex.I * s]
  refine ⟨z, Or.inl ?_, ?_⟩
  · simpa [z] using hd3
  · have hs' : s ^ 2 = d 0 * d 3 := by
      simpa [pow_two] using hs.symm
    simp only [Fin.isValue, Matrix.toBilin'_apply, Fin.sum_univ_four, cons_val_zero,
      cons_val_one, cons_val, mul_zero, add_zero, Matrix.diagonal_apply_eq, ne_eq,
      not_false_eq_true, Matrix.diagonal_apply_ne, zero_mul, zero_add,
      Fin.reduceEq, z]
    rw [show Polynomial.C Complex.I * s * d 3 * (Polynomial.C Complex.I * s) =
        (Polynomial.C Complex.I * Polynomial.C Complex.I) * s ^ 2 * d 3 by ring]
    rw [show (Polynomial.C Complex.I * Polynomial.C Complex.I : Polynomial ℂ) = -1 by
      rw [← Polynomial.C_mul]
      rw [Complex.I_mul_I]
      simp]
    rw [hs']
    ring

theorem complexPolyDiagonalQuad4_isotropic_of_pair12Square
    {d : Fin 4 → Polynomial ℂ}
    (hd2 : d 2 ≠ 0)
    (hsq12 : IsSquare (d 1 * d 2)) :
    ∃ z : Fin 4 → Polynomial ℂ,
      (z 0 ≠ 0 ∨ z 1 ≠ 0 ∨ z 2 ≠ 0 ∨ z 3 ≠ 0) ∧
      Matrix.toBilin' (Matrix.diagonal d) z z = 0 := by
  rcases hsq12 with ⟨s, hs⟩
  let z : Fin 4 → Polynomial ℂ := ![0, d 2, Polynomial.C Complex.I * s, 0]
  refine ⟨z, Or.inr <| Or.inl ?_, ?_⟩
  · simpa [z] using hd2
  · have hs' : s ^ 2 = d 1 * d 2 := by
      simpa [pow_two] using hs.symm
    simp only [Fin.isValue, Matrix.toBilin'_apply, Fin.sum_univ_four, cons_val_zero,
      cons_val_one, cons_val, mul_zero, add_zero, Matrix.diagonal_apply_eq, ne_eq,
      not_false_eq_true, Matrix.diagonal_apply_ne, zero_mul, zero_add,
      Fin.reduceEq, z]
    rw [show Polynomial.C Complex.I * s * d 2 * (Polynomial.C Complex.I * s) =
        (Polynomial.C Complex.I * Polynomial.C Complex.I) * s ^ 2 * d 2 by ring]
    rw [show (Polynomial.C Complex.I * Polynomial.C Complex.I : Polynomial ℂ) = -1 by
      rw [← Polynomial.C_mul]
      rw [Complex.I_mul_I]
      simp]
    rw [hs']
    ring

theorem complexPolyDiagonalQuad4_isotropic_of_pair13Square
    {d : Fin 4 → Polynomial ℂ}
    (hd3 : d 3 ≠ 0)
    (hsq13 : IsSquare (d 1 * d 3)) :
    ∃ z : Fin 4 → Polynomial ℂ,
      (z 0 ≠ 0 ∨ z 1 ≠ 0 ∨ z 2 ≠ 0 ∨ z 3 ≠ 0) ∧
      Matrix.toBilin' (Matrix.diagonal d) z z = 0 := by
  rcases hsq13 with ⟨s, hs⟩
  let z : Fin 4 → Polynomial ℂ := ![0, d 3, 0, Polynomial.C Complex.I * s]
  refine ⟨z, Or.inr <| Or.inl ?_, ?_⟩
  · simpa [z] using hd3
  · have hs' : s ^ 2 = d 1 * d 3 := by
      simpa [pow_two] using hs.symm
    simp only [Fin.isValue, Matrix.toBilin'_apply, Fin.sum_univ_four, cons_val_zero,
      cons_val_one, cons_val, mul_zero, add_zero, Matrix.diagonal_apply_eq, ne_eq,
      not_false_eq_true, Matrix.diagonal_apply_ne, zero_mul, zero_add,
      Fin.reduceEq, z]
    rw [show Polynomial.C Complex.I * s * d 3 * (Polynomial.C Complex.I * s) =
        (Polynomial.C Complex.I * Polynomial.C Complex.I) * s ^ 2 * d 3 by ring]
    rw [show (Polynomial.C Complex.I * Polynomial.C Complex.I : Polynomial ℂ) = -1 by
      rw [← Polynomial.C_mul]
      rw [Complex.I_mul_I]
      simp]
    rw [hs']
    ring

theorem complexPolyDiagonalQuad4_isotropic_of_pair23Square
    {d : Fin 4 → Polynomial ℂ}
    (hd3 : d 3 ≠ 0)
    (hsq23 : IsSquare (d 2 * d 3)) :
    ∃ z : Fin 4 → Polynomial ℂ,
      (z 0 ≠ 0 ∨ z 1 ≠ 0 ∨ z 2 ≠ 0 ∨ z 3 ≠ 0) ∧
      Matrix.toBilin' (Matrix.diagonal d) z z = 0 := by
  rcases hsq23 with ⟨s, hs⟩
  let z : Fin 4 → Polynomial ℂ := ![0, 0, d 3, Polynomial.C Complex.I * s]
  refine ⟨z, Or.inr <| Or.inr <| Or.inl ?_, ?_⟩
  · simpa [z] using hd3
  · have hs' : s ^ 2 = d 2 * d 3 := by
      simpa [pow_two] using hs.symm
    simp only [Fin.isValue, Matrix.toBilin'_apply, Fin.sum_univ_four, cons_val_zero,
      cons_val_one, cons_val, mul_zero, add_zero, Matrix.diagonal_apply_eq, ne_eq,
      not_false_eq_true, Matrix.diagonal_apply_ne, zero_mul, zero_add,
      Fin.reduceEq, z]
    rw [show Polynomial.C Complex.I * s * d 3 * (Polynomial.C Complex.I * s) =
        (Polynomial.C Complex.I * Polynomial.C Complex.I) * s ^ 2 * d 3 by ring]
    rw [show (Polynomial.C Complex.I * Polynomial.C Complex.I : Polynomial ℂ) = -1 by
      rw [← Polynomial.C_mul]
      rw [Complex.I_mul_I]
      simp]
    rw [hs']
    ring

theorem complexPolyMonicTripleProductQuad4IsotropicStatement_of_noPairSquareStatement
    (hstmt : ComplexPolyMonicTripleProductNoPairSquareQuad4IsotropicStatement) :
    ComplexPolyMonicTripleProductQuad4IsotropicStatement := by
  intro a b c ha hb hc
  have habc0 : a * b * c ≠ 0 :=
    mul_ne_zero (mul_ne_zero ha.ne_zero hb.ne_zero) hc.ne_zero
  by_cases h01 : IsSquare (a * b)
  · simpa using complexPolyDiagonalQuad4_isotropic_of_firstPairSquare
      (d := ![a, b, c, a * b * c]) hb.ne_zero h01
  by_cases h02 : IsSquare (a * c)
  · simpa using complexPolyDiagonalQuad4_isotropic_of_pair02Square
      (d := ![a, b, c, a * b * c]) hc.ne_zero h02
  by_cases h03 : IsSquare (a * (a * b * c))
  · simpa using complexPolyDiagonalQuad4_isotropic_of_pair03Square
      (d := ![a, b, c, a * b * c]) habc0 h03
  by_cases h12 : IsSquare (b * c)
  · simpa using complexPolyDiagonalQuad4_isotropic_of_pair12Square
      (d := ![a, b, c, a * b * c]) hc.ne_zero h12
  by_cases h13 : IsSquare (b * (a * b * c))
  · simpa using complexPolyDiagonalQuad4_isotropic_of_pair13Square
      (d := ![a, b, c, a * b * c]) habc0 h13
  by_cases h23 : IsSquare (c * (a * b * c))
  · simpa using complexPolyDiagonalQuad4_isotropic_of_pair23Square
      (d := ![a, b, c, a * b * c]) habc0 h23
  exact hstmt ha hb hc h01 h02 h03 h12 h13 h23

theorem complexPolyDiagonalQuad4_isotropic_of_anyPairSquare
    {d : Fin 4 → Polynomial ℂ}
    (hd : ∀ i, d i ≠ 0)
    (hpair :
      IsSquare (d 0 * d 1) ∨ IsSquare (d 0 * d 2) ∨ IsSquare (d 0 * d 3) ∨
        IsSquare (d 1 * d 2) ∨ IsSquare (d 1 * d 3) ∨ IsSquare (d 2 * d 3)) :
    ∃ z : Fin 4 → Polynomial ℂ,
      (z 0 ≠ 0 ∨ z 1 ≠ 0 ∨ z 2 ≠ 0 ∨ z 3 ≠ 0) ∧
      Matrix.toBilin' (Matrix.diagonal d) z z = 0 := by
  rcases hpair with h01 | hpair
  · exact complexPolyDiagonalQuad4_isotropic_of_firstPairSquare (hd 1) h01
  rcases hpair with h02 | hpair
  · exact complexPolyDiagonalQuad4_isotropic_of_pair02Square (hd 2) h02
  rcases hpair with h03 | hpair
  · exact complexPolyDiagonalQuad4_isotropic_of_pair03Square (hd 3) h03
  rcases hpair with h12 | hpair
  · exact complexPolyDiagonalQuad4_isotropic_of_pair12Square (hd 2) h12
  rcases hpair with h13 | h23
  · exact complexPolyDiagonalQuad4_isotropic_of_pair13Square (hd 3) h13
  · exact complexPolyDiagonalQuad4_isotropic_of_pair23Square (hd 3) h23

theorem complexPolyMonicDiagonalQuad4_isotropic_of_anyPairSquare
    {d : Fin 4 → Polynomial ℂ}
    (hmonic : ∀ i, (d i).Monic)
    (hpair :
      IsSquare (d 0 * d 1) ∨ IsSquare (d 0 * d 2) ∨ IsSquare (d 0 * d 3) ∨
        IsSquare (d 1 * d 2) ∨ IsSquare (d 1 * d 3) ∨ IsSquare (d 2 * d 3)) :
    ∃ z : Fin 4 → Polynomial ℂ,
      (z 0 ≠ 0 ∨ z 1 ≠ 0 ∨ z 2 ≠ 0 ∨ z 3 ≠ 0) ∧
      Matrix.toBilin' (Matrix.diagonal d) z z = 0 :=
  complexPolyDiagonalQuad4_isotropic_of_anyPairSquare (fun i => (hmonic i).ne_zero) hpair

theorem complexPolyMonicDiagonalQuad4SquareDetIsotropicStatement_of_noPairSquareStatement
    (hstmt : ComplexPolyMonicDiagonalQuad4SquareDetNoPairSquareIsotropicStatement) :
    ComplexPolyMonicDiagonalQuad4SquareDetIsotropicStatement := by
  intro d hmonic hdet
  by_cases h01 : IsSquare (d 0 * d 1)
  · exact complexPolyMonicDiagonalQuad4_isotropic_of_anyPairSquare hmonic
      (Or.inl h01)
  by_cases h02 : IsSquare (d 0 * d 2)
  · exact complexPolyMonicDiagonalQuad4_isotropic_of_anyPairSquare hmonic
      (Or.inr <| Or.inl h02)
  by_cases h03 : IsSquare (d 0 * d 3)
  · exact complexPolyMonicDiagonalQuad4_isotropic_of_anyPairSquare hmonic
      (Or.inr <| Or.inr <| Or.inl h03)
  by_cases h12 : IsSquare (d 1 * d 2)
  · exact complexPolyMonicDiagonalQuad4_isotropic_of_anyPairSquare hmonic
      (Or.inr <| Or.inr <| Or.inr <| Or.inl h12)
  by_cases h13 : IsSquare (d 1 * d 3)
  · exact complexPolyMonicDiagonalQuad4_isotropic_of_anyPairSquare hmonic
      (Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl h13)
  by_cases h23 : IsSquare (d 2 * d 3)
  · exact complexPolyMonicDiagonalQuad4_isotropic_of_anyPairSquare hmonic
      (Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr h23)
  exact hstmt hmonic hdet h01 h02 h03 h12 h13 h23

-- The coefficient-normalization proof triggers expensive polynomial normalization; a higher
-- heartbeat cap keeps the monic reduction theorem deterministic without affecting later modules.
theorem complexPolyDiagonalQuad4SquareDetIsotropicStatement_of_monicStatement
    (hmonic : ComplexPolyMonicDiagonalQuad4SquareDetIsotropicStatement) :
    ComplexPolyDiagonalQuad4SquareDetIsotropicStatement := by
  intro d hd0 hsq
  let e : Fin 4 → Polynomial ℂ := fun i => d i * C ((d i).leadingCoeff)⁻¹
  let r : Fin 4 → ℂ := fun i => Classical.choose
    (IsAlgClosed.exists_pow_nat_eq ((d i).leadingCoeff)⁻¹ zero_lt_two)
  have hr : ∀ i, r i ^ 2 = ((d i).leadingCoeff)⁻¹ := by
    intro i
    exact Classical.choose_spec (IsAlgClosed.exists_pow_nat_eq ((d i).leadingCoeff)⁻¹ zero_lt_two)
  have hC0 : (C (r 0) : Polynomial ℂ) ^ 2 = C ((d 0).leadingCoeff)⁻¹ := by
    simpa [pow_two] using congrArg Polynomial.C (hr 0)
  have hC1 : (C (r 1) : Polynomial ℂ) ^ 2 = C ((d 1).leadingCoeff)⁻¹ := by
    simpa [pow_two] using congrArg Polynomial.C (hr 1)
  have hC2 : (C (r 2) : Polynomial ℂ) ^ 2 = C ((d 2).leadingCoeff)⁻¹ := by
    simpa [pow_two] using congrArg Polynomial.C (hr 2)
  have hC3 : (C (r 3) : Polynomial ℂ) ^ 2 = C ((d 3).leadingCoeff)⁻¹ := by
    simpa [pow_two] using congrArg Polynomial.C (hr 3)
  have hC0' : (C (r 0) : Polynomial ℂ) * C (r 0) = C ((d 0).leadingCoeff)⁻¹ := by
    simpa [pow_two] using hC0
  have hC1' : (C (r 1) : Polynomial ℂ) * C (r 1) = C ((d 1).leadingCoeff)⁻¹ := by
    simpa [pow_two] using hC1
  have hC2' : (C (r 2) : Polynomial ℂ) * C (r 2) = C ((d 2).leadingCoeff)⁻¹ := by
    simpa [pow_two] using hC2
  have hC3' : (C (r 3) : Polynomial ℂ) * C (r 3) = C ((d 3).leadingCoeff)⁻¹ := by
    simpa [pow_two] using hC3
  have hCprod :
      (((C (r 0)) ^ 2 * (C (r 1)) ^ 2) * ((C (r 2)) ^ 2 * (C (r 3)) ^ 2) : Polynomial ℂ) =
        C ((r 0 * r 1 * r 2 * r 3) ^ 2) := by
    calc
      (((C (r 0)) ^ 2 * (C (r 1)) ^ 2) * ((C (r 2)) ^ 2 * (C (r 3)) ^ 2) : Polynomial ℂ)
          = (C ((r 0) ^ 2) * C ((r 1) ^ 2)) * (C ((r 2) ^ 2) * C ((r 3) ^ 2)) := by
              simp [pow_two]
      _ = C (((r 0) ^ 2 * (r 1) ^ 2) * ((r 2) ^ 2 * (r 3) ^ 2)) := by
            simp only [Polynomial.C_mul]
      _ = C ((r 0 * r 1 * r 2 * r 3) ^ 2) := by
            congr 1
            ring
  have hemonic : ∀ i, (e i).Monic := by
    intro i
    dsimp [e]
    exact Polynomial.monic_mul_leadingCoeff_inv (hd0 i)
  have hsq' : IsSquare ((Matrix.diagonal e).det) := by
    rcases hsq with ⟨s, hs⟩
    let c : Polynomial ℂ := C (r 0 * r 1 * r 2 * r 3)
    have hc : c * c = C ((r 0 * r 1 * r 2 * r 3) ^ 2) := by
      dsimp [c]
      simp [pow_two]
    have hs'' : d 0 * (d 1 * (d 2 * d 3)) = s * s := by
      simpa [Matrix.det_diagonal, Fin.prod_univ_four, mul_assoc] using hs
    refine ⟨s * c, ?_⟩
    rw [Matrix.det_diagonal, Fin.prod_univ_four]
    calc
      e 0 * e 1 * e 2 * e 3
          = (d 0 * (d 1 * (d 2 * d 3))) *
              ((C (r 0)) ^ 2 * (C (r 1)) ^ 2 * (C (r 2)) ^ 2 * (C (r 3)) ^ 2) := by
                rw [hC0, hC1, hC2, hC3]
                simp [e, mul_assoc, mul_left_comm, mul_comm]
      _ = (s * s) *
            ((C (r 0)) ^ 2 * (C (r 1)) ^ 2 * (C (r 2)) ^ 2 * (C (r 3)) ^ 2) := by
                rw [hs'']
      _ = (s * C (r 0 * r 1 * r 2 * r 3)) * (s * C (r 0 * r 1 * r 2 * r 3)) := by
            calc
              (s * s) * ((C (r 0)) ^ 2 * (C (r 1)) ^ 2 * (C (r 2)) ^ 2 * (C (r 3)) ^ 2)
                  = (s * s) * C ((r 0 * r 1 * r 2 * r 3) ^ 2) := by
                      rw [show ((C (r 0)) ^ 2 * (C (r 1)) ^ 2 * (C (r 2)) ^ 2 * (C (r 3)) ^ 2 : Polynomial ℂ) =
                        (((C (r 0)) ^ 2 * (C (r 1)) ^ 2) * ((C (r 2)) ^ 2 * (C (r 3)) ^ 2)) by
                          ring]
                      rw [hCprod]
              _ = (s * c) * (s * c) := by
                    calc
                      (s * s) * C ((r 0 * r 1 * r 2 * r 3) ^ 2)
                          = (s * s) * (c * c) := by
                              rw [hc]
                      _ = (s * c) * (s * c) := by
                            ac_rfl
  rcases hmonic hemonic hsq' with ⟨z, hzneq, hziso⟩
  let w : Fin 4 → Polynomial ℂ := fun i => C (r i) * z i
  have hr0 : ∀ i, r i ≠ 0 := by
    intro i hri
    have hlead0 : (d i).leadingCoeff ≠ 0 := by
      exact Polynomial.leadingCoeff_ne_zero.mpr (hd0 i)
    have hinv0 : ((d i).leadingCoeff)⁻¹ ≠ 0 := inv_ne_zero hlead0
    have : ((d i).leadingCoeff)⁻¹ = 0 := by
      rw [← hr i, hri]
      simp
    exact hinv0 this
  have hwneq : w 0 ≠ 0 ∨ w 1 ≠ 0 ∨ w 2 ≠ 0 ∨ w 3 ≠ 0 := by
    rcases hzneq with hz0 | hz1 | hz2 | hz3
    · exact Or.inl (mul_ne_zero (Polynomial.C_ne_zero.mpr (hr0 0)) hz0)
    · exact Or.inr <| Or.inl (mul_ne_zero (Polynomial.C_ne_zero.mpr (hr0 1)) hz1)
    · exact Or.inr <| Or.inr <| Or.inl (mul_ne_zero (Polynomial.C_ne_zero.mpr (hr0 2)) hz2)
    · exact Or.inr <| Or.inr <| Or.inr (mul_ne_zero (Polynomial.C_ne_zero.mpr (hr0 3)) hz3)
  refine ⟨w, hwneq, ?_⟩
  have hziso' :
      z 0 * e 0 * z 0 + (z 1 * e 1 * z 1 + (z 2 * e 2 * z 2 + z 3 * e 3 * z 3)) = 0 := by
    simpa [Matrix.toBilin'_apply, Fin.sum_univ_four, add_assoc] using hziso
  have hw0 :
      (C (r 0) * z 0) * d 0 * (C (r 0) * z 0) = z 0 * e 0 * z 0 := by
    calc
      (C (r 0) * z 0) * d 0 * (C (r 0) * z 0)
          = z 0 * (d 0 * (C (r 0) * C (r 0))) * z 0 := by
              simp [mul_left_comm, mul_comm]
      _ = z 0 * (d 0 * C ((d 0).leadingCoeff)⁻¹) * z 0 := by
            rw [hC0']
      _ = z 0 * e 0 * z 0 := by
            rw [show e 0 = d 0 * C ((d 0).leadingCoeff)⁻¹ by rfl]
  have hw1 :
      (C (r 1) * z 1) * d 1 * (C (r 1) * z 1) = z 1 * e 1 * z 1 := by
    calc
      (C (r 1) * z 1) * d 1 * (C (r 1) * z 1)
          = z 1 * (d 1 * (C (r 1) * C (r 1))) * z 1 := by
              simp [mul_left_comm, mul_comm]
      _ = z 1 * (d 1 * C ((d 1).leadingCoeff)⁻¹) * z 1 := by
            rw [hC1']
      _ = z 1 * e 1 * z 1 := by
            rw [show e 1 = d 1 * C ((d 1).leadingCoeff)⁻¹ by rfl]
  have hw2 :
      (C (r 2) * z 2) * d 2 * (C (r 2) * z 2) = z 2 * e 2 * z 2 := by
    calc
      (C (r 2) * z 2) * d 2 * (C (r 2) * z 2)
          = z 2 * (d 2 * (C (r 2) * C (r 2))) * z 2 := by
              simp [mul_left_comm, mul_comm]
      _ = z 2 * (d 2 * C ((d 2).leadingCoeff)⁻¹) * z 2 := by
            rw [hC2']
      _ = z 2 * e 2 * z 2 := by
            rw [show e 2 = d 2 * C ((d 2).leadingCoeff)⁻¹ by rfl]
  have hw3 :
      (C (r 3) * z 3) * d 3 * (C (r 3) * z 3) = z 3 * e 3 * z 3 := by
    calc
      (C (r 3) * z 3) * d 3 * (C (r 3) * z 3)
          = z 3 * (d 3 * (C (r 3) * C (r 3))) * z 3 := by
              simp [mul_left_comm, mul_comm]
      _ = z 3 * (d 3 * C ((d 3).leadingCoeff)⁻¹) * z 3 := by
            rw [hC3']
      _ = z 3 * e 3 * z 3 := by
            rw [show e 3 = d 3 * C ((d 3).leadingCoeff)⁻¹ by rfl]
  have hwiso :
      (C (r 0) * z 0) * d 0 * (C (r 0) * z 0) +
        ((C (r 1) * z 1) * d 1 * (C (r 1) * z 1) +
          ((C (r 2) * z 2) * d 2 * (C (r 2) * z 2) +
            (C (r 3) * z 3) * d 3 * (C (r 3) * z 3))) =
      z 0 * e 0 * z 0 + (z 1 * e 1 * z 1 + (z 2 * e 2 * z 2 + z 3 * e 3 * z 3)) := by
    rw [hw0, hw1, hw2, hw3]
  calc
    Matrix.toBilin' (Matrix.diagonal d) w w
        = w 0 * d 0 * w 0 + (w 1 * d 1 * w 1 + (w 2 * d 2 * w 2 + w 3 * d 3 * w 3)) := by
            simp [Matrix.toBilin'_apply, Fin.sum_univ_four, add_assoc, w]
    _ = z 0 * e 0 * z 0 + (z 1 * e 1 * z 1 + (z 2 * e 2 * z 2 + z 3 * e 3 * z 3)) := hwiso
    _ = 0 := hziso'

end MatrixSOS
