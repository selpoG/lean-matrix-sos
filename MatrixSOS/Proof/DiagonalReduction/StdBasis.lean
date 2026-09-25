/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/

import MatrixSOS.Proof.PolyMatrix

/-!
# Standard basis identities for diagonal reduction
-/

open Matrix Polynomial
open scoped Matrix MatrixOrder

noncomputable section

namespace MatrixSOS

noncomputable def stdBasisV (m : ℕ) : Module.Basis (Fin m) Poly (V m) :=
  Pi.basisFun Poly (Fin m)

@[simp] lemma stdBasisV_apply {m : ℕ} (i j : Fin m) :
    stdBasisV m i j = if i = j then 1 else 0 := by
  by_cases h : i = j
  · subst h
    simp [stdBasisV]
  · simp [stdBasisV, h, eq_comm]

@[simp] lemma compressVec_stdBasisV_same {m : ℕ} (i : Fin (m + 1)) :
    compressVec i (stdBasisV (m + 1) i) = 0 := by
  funext j
  change (stdBasisV (m + 1) i) (i.succAbove j) = 0
  simp [stdBasisV_apply]

@[simp] lemma compressVec_stdBasisV_succAbove {m : ℕ} (i : Fin (m + 1)) (j : Fin m) :
    compressVec i (stdBasisV (m + 1) (i.succAbove j)) = stdBasisV m j := by
  funext k
  by_cases h : j = k
  · subst h
    change (stdBasisV (m + 1) (i.succAbove j)) (i.succAbove j) = (stdBasisV m) j j
    simp [stdBasisV_apply]
  · change (stdBasisV (m + 1) (i.succAbove j)) (i.succAbove k) = (stdBasisV m) j k
    simp [stdBasisV_apply, h]

lemma bilin_sum_stdBasis_right
    {m : ℕ}
    (B : LinearMap.BilinForm Poly (V m))
    (v w : V m) :
    B v w = ∑ i : Fin m, w i * B v (stdBasisV m i) := by
  symm
  simpa [stdBasisV, Pi.basisFun_repr] using congrArg (B v) ((stdBasisV m).sum_repr w)

lemma bilin_sum_stdBasis_left
    {m : ℕ}
    (B : LinearMap.BilinForm Poly (V m))
    (v w : V m) :
    B v w = ∑ i : Fin m, v i * B (stdBasisV m i) w := by
  symm
  simpa [stdBasisV, Pi.basisFun_repr] using congrArg (fun z => B z w) ((stdBasisV m).sum_repr v)

@[simp] lemma bilinOfPolyMat_stdBasis_right
    {m : ℕ}
    (P : PolyMat m)
    (v : V m)
    (j : Fin m) :
    bilinOfPolyMat P v (stdBasisV m j) = ∑ i : Fin m, v i * P i j := by
  rw [bilin_sum_stdBasis_left]
  apply Finset.sum_congr rfl
  intro i hi
  simp [bilinOfPolyMat, stdBasisV, Matrix.toBilin'_single]

@[simp] lemma bilinOfPolyMat_stdBasis_left
    {m : ℕ}
    (P : PolyMat m)
    (i : Fin m)
    (w : V m) :
    bilinOfPolyMat P (stdBasisV m i) w = ∑ j : Fin m, P i j * w j := by
  rw [bilin_sum_stdBasis_right]
  apply Finset.sum_congr rfl
  intro j hj
  simp [bilinOfPolyMat, stdBasisV, Matrix.toBilin'_single, mul_comm]

@[simp] lemma bilinOfPolyMat_stdBasis
    {m : ℕ}
    (P : PolyMat m)
    (i j : Fin m) :
    bilinOfPolyMat P (stdBasisV m i) (stdBasisV m j) = P i j := by
  simp [stdBasisV_apply]

end MatrixSOS
