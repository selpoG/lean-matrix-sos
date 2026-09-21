/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import MatrixSOS.Polynomial
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Support
import Mathlib.Algebra.Polynomial.Expand
import Mathlib.Tactic.Ring
import Mathlib.Data.Matrix.ColumnRowPartitioned

/-!
# Polynomial matrices, positivity, and sums of squares
-/

open Matrix Polynomial
open scoped Matrix MatrixOrder

noncomputable section

namespace MatrixSOS

abbrev GramIdx (r m : ℕ) := Fin (r + 1) × Fin m
abbrev PolyMat (m : ℕ) := Matrix (Fin m) (Fin m) Poly

/-- A matrix polynomial is SOS if it has a finite rectangular factorization. -/
def IsMatrixSOS {m : ℕ} (M : PolyMat m) : Prop :=
  ∃ (ℓ : ℕ) (R : Matrix (Fin ℓ) (Fin m) Poly), M = R.transpose * R

/-- Bounded SOS factorization with all entries of the factor having degree at most `d`. -/
def BoundedMatrixSOS {m : ℕ} (d : ℕ) (M : PolyMat m) : Prop :=
  ∃ (ℓ : ℕ) (R : Matrix (Fin ℓ) (Fin m) Poly),
    (∀ i j, natDegree (R i j) ≤ d) ∧ M = R.transpose * R

theorem BoundedMatrixSOS.isMatrixSOS {m d : ℕ} {M : PolyMat m}
    (hM : BoundedMatrixSOS d M) : IsMatrixSOS M := by
  rcases hM with ⟨ℓ, R, _hRdeg, hR⟩
  exact ⟨ℓ, R, hR⟩


def mapEval {ι κ : Type*} (x : ℝ) (A : Matrix ι κ (Polynomial ℝ)) : Matrix ι κ ℝ :=
  fun i j => (A i j).eval x

def constPolyMat {ι κ : Type*} (A : Matrix ι κ ℝ) : Matrix ι κ (Polynomial ℝ) :=
  fun i j => Polynomial.C (A i j)

def Qpoly (r m : ℕ) : Matrix (GramIdx r m) (Fin m) (Polynomial ℝ) :=
  fun ij b =>
    match ij with
    | ⟨k, a⟩ => if a = b then (Polynomial.X : Polynomial ℝ) ^ (k : ℕ) else 0

def Qeval (r m : ℕ) (x : ℝ) : Matrix (GramIdx r m) (Fin m) ℝ :=
  fun ij b =>
    match ij with
    | ⟨k, a⟩ => if a = b then x ^ (k : ℕ) else 0

def coeffMat {r m ℓ : ℕ}
    (A : Matrix (Fin ℓ) (Fin m) (Polynomial ℝ)) :
    Matrix (Fin ℓ) (GramIdx r m) ℝ :=
  fun i ka => (A i ka.2).coeff ka.1

@[simp] lemma mapEval_apply {ι κ : Type*} (x : ℝ)
    (A : Matrix ι κ (Polynomial ℝ)) (i : ι) (j : κ) :
    mapEval x A i j = (A i j).eval x := rfl

@[simp] lemma mapEval_constPolyMat {ι κ : Type*} (x : ℝ) (A : Matrix ι κ ℝ) :
    mapEval x (constPolyMat A) = A := by
  ext i j
  simp [mapEval, constPolyMat]

lemma eq_constPolyMat_of_natDegree_le_zero
    {ι κ : Type*}
    (A : Matrix ι κ (Polynomial ℝ))
    (hA : ∀ i j, natDegree (A i j) ≤ 0) :
    A = constPolyMat (mapEval 0 A) := by
  ext i j
  rw [eq_C_of_natDegree_le_zero (hA i j)]
  simp [constPolyMat, mapEval, Polynomial.coeff_zero_eq_eval_zero]

@[simp] lemma mapEval_Qpoly (r m : ℕ) (x : ℝ) :
    mapEval x (Qpoly r m) = Qeval r m x := by
  ext i j
  rcases i with ⟨k, a⟩
  by_cases h : a = j
  · simp [Qpoly, Qeval, mapEval, h]
  · simp [Qpoly, Qeval, mapEval, h]

@[simp] lemma constPolyMat_transpose {ι κ : Type*} (A : Matrix ι κ ℝ) :
    constPolyMat A.transpose = (constPolyMat A).transpose := by
  ext i j
  simp [constPolyMat]

@[simp] lemma constPolyMat_mul
    {ι κ μ : Type*} [Fintype κ]
    (A : Matrix ι κ ℝ) (B : Matrix κ μ ℝ) :
    constPolyMat (A * B) = (constPolyMat A) * (constPolyMat B) := by
  ext i j n
  by_cases hn : n = 0
  · subst hn
    simp [constPolyMat, Matrix.mul_apply]
  · simp [constPolyMat, Matrix.mul_apply]

lemma coeffMat_mul_Qpoly_entry
    {r m ℓ : ℕ}
    (A : Matrix (Fin ℓ) (Fin m) (Polynomial ℝ))
    (hA : ∀ i j, natDegree (A i j) ≤ r)
    (i : Fin ℓ) (a : Fin m) :
    (constPolyMat (coeffMat (r := r) A) * Qpoly r m) i a = A i a := by
  ext n
  rw [Matrix.mul_apply]
  rw [show (∑ j : GramIdx r m,
      constPolyMat (coeffMat (r := r) A) i j * Qpoly r m j a)
      = ∑ x ∈ (Finset.univ : Finset (Fin (r + 1))).product Finset.univ,
          constPolyMat (coeffMat (r := r) A) i x * Qpoly r m x a by
      simp [Finset.univ_product_univ]]
  rw [Polynomial.finsetSum_coeff]
  calc
    ∑ b ∈ (Finset.univ : Finset (Fin (r + 1))).product Finset.univ,
        coeff (constPolyMat (coeffMat (r := r) A) i b * Qpoly r m b a) n
      =
        ∑ x ∈ (Finset.univ : Finset (Fin (r + 1))),
          ∑ y ∈ (Finset.univ : Finset (Fin m)),
            coeff (constPolyMat (coeffMat (r := r) A) i (x, y) * Qpoly r m (x, y) a) n := by
          simpa using
            (Finset.sum_product
              (Finset.univ : Finset (Fin (r + 1)))
              (Finset.univ : Finset (Fin m))
              (fun p => coeff (constPolyMat (coeffMat (r := r) A) i p * Qpoly r m p a) n))
    _ =
        ∑ x ∈ (Finset.univ : Finset (Fin (r + 1))),
          coeff (constPolyMat (coeffMat (r := r) A) i (x, a) * Qpoly r m (x, a) a) n := by
          apply Finset.sum_congr rfl
          intro x hx
          rw [Finset.sum_eq_single a]
          · intro b _ hb
            simp [constPolyMat, coeffMat, Qpoly, hb]
          · simp [constPolyMat, coeffMat, Qpoly]
    _ = ∑ x ∈ (Finset.univ : Finset (Fin (r + 1))), if n = x then (A i a).coeff x else 0 := by
          apply Finset.sum_congr rfl
          intro x hx
          simp [constPolyMat, coeffMat, Qpoly]
    _ = (A i a).coeff n := by
          by_cases hn : n < r + 1
          · let xn : Fin (r + 1) := ⟨n, hn⟩
            rw [Finset.sum_eq_single xn]
            · simp [xn]
            · intro x _ hxne
              have hxne' : n ≠ x := by
                intro h
                apply hxne
                apply Fin.ext
                simpa [xn] using h.symm
              simp [hxne']
            · simp
          · have hcoeff : (A i a).coeff n = 0 := by
              exact coeff_eq_zero_of_natDegree_lt <|
                lt_of_le_of_lt (hA i a)
                  (lt_of_lt_of_le (Nat.lt_succ_self r) (Nat.not_lt.mp hn))
            rw [hcoeff]
            apply Finset.sum_eq_zero
            intro x hx
            have hxne : n ≠ x := by
              intro h
              apply hn
              simpa [h] using x.is_lt
            simp [hxne]

lemma coeffMat_mul_Qpoly
    {r m ℓ : ℕ}
    (A : Matrix (Fin ℓ) (Fin m) (Polynomial ℝ))
    (hA : ∀ i j, natDegree (A i j) ≤ r) :
    constPolyMat (coeffMat (r := r) A) * Qpoly r m = A := by
  ext i a n
  exact congrArg (fun p => p.coeff n) (coeffMat_mul_Qpoly_entry A hA i a)

def NonnegOnNN {m : ℕ} (M : PolyMat m) : Prop :=
  ∀ x : ℝ, 0 ≤ x → (mapEval x M).PosSemidef

def NonnegOnIci {m : ℕ} (a : ℝ) (M : PolyMat m) : Prop :=
  ∀ x : ℝ, a ≤ x → (mapEval x M).PosSemidef

def NonnegOnIic {m : ℕ} (a : ℝ) (M : PolyMat m) : Prop :=
  ∀ x : ℝ, x ≤ a → (mapEval x M).PosSemidef

def NonnegOnIcc {m : ℕ} (a b : ℝ) (M : PolyMat m) : Prop :=
  ∀ x : ℝ, a ≤ x → x ≤ b → (mapEval x M).PosSemidef

def affinePullbackPoly (a s : ℝ) (p : Poly) : Poly :=
  p.comp (Polynomial.C s * Polynomial.X + Polynomial.C a)

def affinePullbackMat {ι κ : Type*} (a s : ℝ)
    (A : Matrix ι κ Poly) : Matrix ι κ Poly :=
  fun i j => affinePullbackPoly a s (A i j)

@[simp] lemma mapEval_affinePullbackMat {ι κ : Type*} (a s x : ℝ)
    (A : Matrix ι κ Poly) :
    mapEval x (affinePullbackMat a s A) = mapEval (s * x + a) A := by
  ext i j
  simp [mapEval, affinePullbackMat, affinePullbackPoly, Polynomial.eval_comp]

lemma affinePullbackMat_isSymm {m : ℕ} {a s : ℝ} {M : PolyMat m}
    (hM : M.IsSymm) :
    (affinePullbackMat a s M).IsSymm := by
  refine Matrix.IsSymm.ext ?_
  intro i j
  exact congrArg (affinePullbackPoly a s) (hM.apply i j)

lemma affinePullbackPoly_inverse {a s : ℝ} (hs : s ≠ 0) (p : Poly) :
    affinePullbackPoly (-a / s) (1 / s) (affinePullbackPoly a s p) = p := by
  apply Polynomial.funext
  intro x
  simp [affinePullbackPoly, Polynomial.eval_comp]
  congr 1
  field_simp [hs]
  ring

lemma affinePullbackMat_inverse {ι κ : Type*} {a s : ℝ} (hs : s ≠ 0)
    (M : Matrix ι κ Poly) :
    affinePullbackMat (-a / s) (1 / s) (affinePullbackMat a s M) = M := by
  apply Matrix.ext
  intro i j
  exact affinePullbackPoly_inverse hs (M i j)

lemma natDegree_affinePullbackPoly_le {a s : ℝ} {p : Poly} {d : ℕ}
    (hp : p.natDegree ≤ d) :
    (affinePullbackPoly a s p).natDegree ≤ d := by
  have hlin : natDegree (Polynomial.C s * Polynomial.X + Polynomial.C a : Poly) ≤ 1 := by
    compute_degree
  dsimp [affinePullbackPoly]
  calc
    natDegree (p.comp (Polynomial.C s * Polynomial.X + Polynomial.C a)) ≤
        natDegree p * natDegree (Polynomial.C s * Polynomial.X + Polynomial.C a : Poly) :=
      Polynomial.natDegree_comp_le
    _ ≤ d * 1 := Nat.mul_le_mul hp hlin
    _ = d := by simp

lemma natDegree_affinePullbackMat_le {m d : ℕ} {a s : ℝ} {M : PolyMat m}
    (hM : ∀ i j, natDegree (M i j) ≤ d) :
    ∀ i j, natDegree (affinePullbackMat a s M i j) ≤ d := by
  intro i j
  exact natDegree_affinePullbackPoly_le (hM i j)

def GramTerm (r m : ℕ)
    (Y : Matrix (GramIdx r m) (GramIdx r m) ℝ) : PolyMat m :=
  let QT : Matrix (Fin m) (GramIdx r m) (Polynomial ℝ) := (Qpoly r m).transpose
  let YC : Matrix (GramIdx r m) (GramIdx r m) (Polynomial ℝ) := constPolyMat Y
  let Q  : Matrix (GramIdx r m) (Fin m) (Polynomial ℝ) := Qpoly r m
  ((QT * YC) * Q : PolyMat m)

def GramForm (r s m : ℕ)
    (Y₁ : Matrix (GramIdx r m) (GramIdx r m) ℝ)
    (Y₂ : Matrix (GramIdx s m) (GramIdx s m) ℝ) : PolyMat m :=
  GramTerm r m Y₁ + ((Polynomial.X : Polynomial ℝ) • GramTerm s m Y₂ : PolyMat m)

lemma gramTerm_of_coeffMat
    {r m ℓ : ℕ}
    (C : Matrix (Fin ℓ) (GramIdx r m) ℝ) :
    GramTerm r m (C.transpose * C)
      = (constPolyMat C * Qpoly r m).transpose * (constPolyMat C * Qpoly r m) := by
  simp [GramTerm, Matrix.mul_assoc]

def SOSForm {m ℓ₁ ℓ₂ : ℕ}
    (A : Matrix (Fin ℓ₁) (Fin m) (Polynomial ℝ))
    (B : Matrix (Fin ℓ₂) (Fin m) (Polynomial ℝ)) : PolyMat m :=
  let AT : Matrix (Fin m) (Fin ℓ₁) (Polynomial ℝ) := A.transpose
  let BT : Matrix (Fin m) (Fin ℓ₂) (Polynomial ℝ) := B.transpose
  (((AT * A : PolyMat m))
    + ((Polynomial.X : Polynomial ℝ) • (BT * B : PolyMat m) : PolyMat m) : PolyMat m)

@[simp] lemma mapEval_transpose {ι κ : Type*} (x : ℝ)
    (A : Matrix ι κ (Polynomial ℝ)) :
    mapEval x A.transpose = (mapEval x A).transpose := by
  ext i j
  simp [mapEval]

@[simp] lemma mapEval_add {ι κ : Type*} (x : ℝ)
    (A B : Matrix ι κ (Polynomial ℝ)) :
    mapEval x (A + B) = mapEval x A + mapEval x B := by
  ext i j
  simp [mapEval]

@[simp] lemma mapEval_sub {ι κ : Type*} (x : ℝ)
    (A B : Matrix ι κ (Polynomial ℝ)) :
    mapEval x (A - B) = mapEval x A - mapEval x B := by
  ext i j
  simp [mapEval]

@[simp] lemma mapEval_mul
    {ι κ μ : Type*} [Fintype κ]
    (x : ℝ)
    (A : Matrix ι κ (Polynomial ℝ))
    (B : Matrix κ μ (Polynomial ℝ)) :
    mapEval x (A * B) = (mapEval x A) * (mapEval x B) := by
  ext i j
  rw [mapEval, Matrix.mul_apply, Matrix.mul_apply]
  rw [Polynomial.eval_finsetSum]
  apply Finset.sum_congr rfl
  intro k hk
  simp [Polynomial.eval_mul]

@[simp] lemma mapEval_smul
    {ι κ : Type*} (x : ℝ)
    (p : Polynomial ℝ) (A : Matrix ι κ (Polynomial ℝ)) :
    mapEval x (p • A) = (p.eval x) • mapEval x A := by
  ext i j
  simp [mapEval]

@[simp] lemma mapEval_GramTerm
    (r m : ℕ)
    (Y : Matrix (GramIdx r m) (GramIdx r m) ℝ)
    (x : ℝ) :
    mapEval x (GramTerm r m Y) =
      (Qeval r m x).transpose * (Y * Qeval r m x) := by
  simp [GramTerm, Matrix.mul_assoc]

@[simp] lemma mapEval_GramForm
    (r s m : ℕ)
    (Y₁ : Matrix (GramIdx r m) (GramIdx r m) ℝ)
    (Y₂ : Matrix (GramIdx s m) (GramIdx s m) ℝ)
    (x : ℝ) :
    mapEval x (GramForm r s m Y₁ Y₂)
      =
      (Qeval r m x).transpose * (Y₁ * Qeval r m x)
        +
      x • ((Qeval s m x).transpose * (Y₂ * Qeval s m x)) := by
  simp [GramForm]

lemma exists_gram_factor
    {n : Type*} [Fintype n]
    (Y : Matrix n n ℝ)
    (hY : Y.PosSemidef) :
    ∃ C : Matrix n n ℝ, Y = C.transpose * C := by
  classical
  rcases CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hY.nonneg with ⟨C, hC⟩
  refine ⟨C, ?_⟩
  ext i j
  simpa [Matrix.mul_apply, star_eq_conjTranspose, Matrix.conjTranspose] using
    congrArg (fun M : Matrix n n ℝ => M i j) hC

/--
A bounded rectangular SOS factorization can be repackaged as a real PSD Gram
matrix in the monomial basis of the same degree.
-/
theorem boundedMatrixSOS_to_gramTerm
    {m d : ℕ} {M : PolyMat m}
    (hM : BoundedMatrixSOS d M) :
    ∃ Y : Matrix (GramIdx d m) (GramIdx d m) ℝ,
      Y.PosSemidef ∧ M = GramTerm d m Y := by
  rcases hM with ⟨ℓ, R, hRdeg, rfl⟩
  let C : Matrix (Fin ℓ) (GramIdx d m) ℝ := coeffMat (r := d) R
  refine ⟨C.transpose * C, ?_, ?_⟩
  · simpa using (Matrix.posSemidef_conjTranspose_mul_self (A := C))
  · rw [gramTerm_of_coeffMat]
    have hCQ : constPolyMat C * Qpoly d m = R := by
      simpa [C] using coeffMat_mul_Qpoly R hRdeg
    simp [hCQ]

/-- A positive semidefinite Gram matrix gives an SOS matrix polynomial. -/
theorem isMatrixSOS_gramTerm_of_posSemidef
    {m r : ℕ} {Y : Matrix (GramIdx r m) (GramIdx r m) ℝ}
    (hY : Y.PosSemidef) :
    IsMatrixSOS (GramTerm r m Y) := by
  rcases exists_gram_factor Y hY with ⟨C, hC⟩
  let e : Fin (Fintype.card (GramIdx r m)) ≃ GramIdx r m :=
    (Fintype.equivFin (GramIdx r m)).symm
  let R₀ : Matrix (GramIdx r m) (Fin m) Poly := constPolyMat C * Qpoly r m
  let R : Matrix (Fin (Fintype.card (GramIdx r m))) (Fin m) Poly :=
    R₀.submatrix e id
  refine ⟨Fintype.card (GramIdx r m), R, ?_⟩
  · rw [hC]
    have hsub :
        R.transpose * R =
          R₀.transpose.submatrix id e * R₀.submatrix e id := by
      ext i j
      simp [R, Matrix.mul_apply]
    calc
      GramTerm r m (C.transpose * C) = (R₀.transpose * R₀).submatrix id id := by
          simp [GramTerm, Matrix.mul_assoc, R₀]
      _ = R₀.transpose.submatrix id e * R₀.submatrix e id :=
          (Matrix.submatrix_mul_equiv R₀.transpose R₀ id e id).symm
      _ = R.transpose * R := hsub.symm

end MatrixSOS
