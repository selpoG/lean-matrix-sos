/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import MatrixSOS.PolyMatrix
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.StdBasis
import Mathlib.Tactic.Ring

/-!
# Algebraic operations on polynomial matrix sums of squares
-/

open Matrix Polynomial
open scoped Matrix MatrixOrder

noncomputable section

namespace MatrixSOS

abbrev V (m : ℕ) := Fin m → Poly

def bilinOfPolyMat {m : ℕ} (P : PolyMat m) : LinearMap.BilinForm Poly (V m) :=
  Matrix.toBilin' P

lemma bilinOfPolyMat_isSymm {m : ℕ} {P : PolyMat m} (hP : P.IsSymm) :
    LinearMap.IsSymm (bilinOfPolyMat P) := by
  rw [LinearMap.isSymm_def]
  intro v w
  suffices h :
      ∑ i, ∑ j, v i * (P i j * w j) = ∑ i, ∑ j, w i * (P i j * v j) by
    simpa [bilinOfPolyMat, Matrix.toBilin'_apply', dotProduct, mulVec, Finset.mul_sum] using h
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  calc
    ∑ x, v x * (P x i * w i) = ∑ x, w i * (P i x * v x) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [hP.apply]
      ring
    _ = ∑ i_1, w i * (P i i_1 * v i_1) := by rfl

def compressVec {m : ℕ} (i : Fin (m + 1)) (v : V (m + 1)) : V m :=
  i.removeNth v

def insertVec {m : ℕ} (i : Fin (m + 1)) (a : Poly) (v : V m) : V (m + 1) :=
  i.insertNth a v

def compressPolyMat {m : ℕ} (i : Fin (m + 1)) (P : PolyMat (m + 1)) : PolyMat m :=
  P.submatrix i.succAbove i.succAbove

def insertMatZeroCol {m ℓ : ℕ}
    (i : Fin (m + 1))
    (R : Matrix (Fin ℓ) (Fin m) Poly) :
    Matrix (Fin ℓ) (Fin (m + 1)) Poly :=
  fun r => insertVec i 0 (fun j => R r j)

@[simp] lemma compressVec_apply {m : ℕ} (i : Fin (m + 1)) (v : V (m + 1)) (j : Fin m) :
    compressVec i v j = v (i.succAbove j) := rfl

@[simp] lemma insertVec_apply_same {m : ℕ} (i : Fin (m + 1)) (a : Poly) (v : V m) :
    insertVec i a v i = a := by
  simp [insertVec]

@[simp] lemma insertVec_apply_succAbove {m : ℕ} (i : Fin (m + 1)) (a : Poly) (v : V m) (j : Fin m) :
    insertVec i a v (i.succAbove j) = v j := by
  simp [insertVec]

@[simp] lemma compressVec_insertVec {m : ℕ} (i : Fin (m + 1)) (a : Poly) (v : V m) :
    compressVec i (insertVec i a v) = v := by
  funext j
  simp [compressVec, insertVec]

@[simp] lemma compressVec_add {m : ℕ} (i : Fin (m + 1)) (v w : V (m + 1)) :
    compressVec i (v + w) = compressVec i v + compressVec i w := by
  funext j
  simp [compressVec, Fin.removeNth_apply]

@[simp] lemma compressVec_smul {m : ℕ} (i : Fin (m + 1)) (a : Poly) (v : V (m + 1)) :
    compressVec i (a • v) = a • compressVec i v := by
  funext j
  simp [compressVec, Fin.removeNth_apply]

@[simp] lemma compressPolyMat_apply {m : ℕ} (i : Fin (m + 1)) (P : PolyMat (m + 1))
    (a b : Fin m) :
    compressPolyMat i P a b = P (i.succAbove a) (i.succAbove b) := rfl

@[simp] lemma insertMatZeroCol_apply_same {m ℓ : ℕ}
    (i : Fin (m + 1))
    (R : Matrix (Fin ℓ) (Fin m) Poly)
    (r : Fin ℓ) :
    insertMatZeroCol i R r i = 0 := by
  simp [insertMatZeroCol]

@[simp] lemma insertMatZeroCol_apply_succAbove {m ℓ : ℕ}
    (i : Fin (m + 1))
    (R : Matrix (Fin ℓ) (Fin m) Poly)
    (r : Fin ℓ) (j : Fin m) :
    insertMatZeroCol i R r (i.succAbove j) = R r j := by
  simp [insertMatZeroCol]

lemma compressPolyMat_transpose_mul_insertMatZeroCol {m ℓ : ℕ}
    (i : Fin (m + 1))
    (R : Matrix (Fin ℓ) (Fin m) Poly) :
    compressPolyMat i
        ((insertMatZeroCol i R).transpose * insertMatZeroCol i R) = R.transpose * R := by
  ext a b
  simp [compressPolyMat, Matrix.mul_apply]

@[simp] lemma transpose_mul_insertMatZeroCol_apply_same_left {m ℓ : ℕ}
    (i : Fin (m + 1))
    (R : Matrix (Fin ℓ) (Fin m) Poly)
    (j : Fin (m + 1)) :
    ((insertMatZeroCol i R).transpose * insertMatZeroCol i R) i j = 0 := by
  rw [Matrix.mul_apply]
  simp

@[simp] lemma transpose_mul_insertMatZeroCol_apply_same_right {m ℓ : ℕ}
    (i : Fin (m + 1))
    (R : Matrix (Fin ℓ) (Fin m) Poly)
    (j : Fin (m + 1)) :
    ((insertMatZeroCol i R).transpose * insertMatZeroCol i R) j i = 0 := by
  rw [Matrix.mul_apply]
  simp

lemma eq_of_compress_eq_and_zero_row_col {m : ℕ}
    {i : Fin (m + 1)}
    {P Q : PolyMat (m + 1)}
    (hcomp : compressPolyMat i P = compressPolyMat i Q)
    (hPirow : ∀ j, P i j = 0)
    (hPicol : ∀ j, P j i = 0)
    (hQirow : ∀ j, Q i j = 0)
    (hQicol : ∀ j, Q j i = 0) :
    P = Q := by
  ext a b n
  rcases Fin.eq_self_or_eq_succAbove i a with rfl | ⟨a', rfl⟩
  · rw [hPirow, hQirow]
  · rcases Fin.eq_self_or_eq_succAbove i b with rfl | ⟨b', rfl⟩
    · rw [hPicol, hQicol]
    · simpa [compressPolyMat] using congrArg (fun M => (M a' b').coeff n) hcomp

@[simp] lemma mapEval_compressPolyMat {m : ℕ} (x : ℝ) (i : Fin (m + 1)) (P : PolyMat (m + 1)) :
    mapEval x (compressPolyMat i P) = (mapEval x P).submatrix i.succAbove i.succAbove := by
  ext a b
  rfl

lemma compressPolyMat_isSymm {m : ℕ} {i : Fin (m + 1)} {P : PolyMat (m + 1)} (hP : P.IsSymm) :
    (compressPolyMat i P).IsSymm := by
  refine Matrix.IsSymm.ext ?_
  intro a b
  simpa [compressPolyMat] using hP.apply (i.succAbove a) (i.succAbove b)

lemma compressPolyMat_posSemidef {m : ℕ} {i : Fin (m + 1)} {P : PolyMat (m + 1)}
    (x : ℝ) (hP : (mapEval x P).PosSemidef) :
    (mapEval x (compressPolyMat i P)).PosSemidef := by
  simpa [mapEval_compressPolyMat] using Matrix.PosSemidef.submatrix hP i.succAbove

@[simp] lemma bilinOfPolyMat_single {m : ℕ} (P : PolyMat m) (i j : Fin m) :
    bilinOfPolyMat P (Pi.single i 1) (Pi.single j 1) = P i j := by
  simp [bilinOfPolyMat]

@[simp] lemma toMatrix'_bilinOfPolyMat {m : ℕ} (P : PolyMat m) :
    LinearMap.BilinForm.toMatrix' (bilinOfPolyMat P) = P := by
  simp [bilinOfPolyMat]

end MatrixSOS
