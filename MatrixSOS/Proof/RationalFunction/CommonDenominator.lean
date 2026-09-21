/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import MatrixSOS.RationalFunction
import Mathlib.Tactic

/-!
# Common denominators for rational-function certificates
-/

open Matrix Polynomial
open scoped Matrix
noncomputable section

namespace MatrixSOS

@[simp] theorem mapToFrac_transpose {ι κ : Type*} (A : Matrix ι κ Poly) :
    mapToFrac A.transpose = (mapToFrac A).transpose := by
  ext i j
  simp [mapToFrac]

@[simp] theorem mapToFrac_mul
    {ι κ μ : Type*} [Fintype κ]
    (A : Matrix ι κ Poly) (B : Matrix κ μ Poly) :
    mapToFrac (A * B) = mapToFrac A * mapToFrac B := by
  ext i j
  simp [mapToFrac, Matrix.mul_apply, map_sum]

@[simp] theorem mapToFrac_det
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι Poly) :
    algebraMap Poly FracPoly A.det = (mapToFrac A).det := by
  classical
  simp [mapToFrac, Matrix.det_apply, map_sum, map_prod]

theorem mapToFrac_inj
    {ι κ : Type*}
    {A B : Matrix ι κ Poly} :
    mapToFrac A = mapToFrac B ↔ A = B := by
  constructor
  · intro h
    ext i j n
    exact congrArg (fun p => p.coeff n) <|
      (IsFractionRing.injective Poly FracPoly) (by
        simpa [mapToFrac] using congrArg (fun M => M i j) h)
  · intro h
    simp [h]

theorem exists_common_denominator
    {ι : Type*}
    [Finite ι]
    (f : ι → FracPoly) :
    ∃ q : Poly, q ∈ nonZeroDivisors Poly ∧
      ∀ i, ∃ a : Poly, algebraMap Poly FracPoly q * f i = algebraMap Poly FracPoly a := by
  classical
  let _ := Fintype.ofFinite ι
  choose num den hden hrepr using
    fun i => (IsFractionRing.div_surjective (A := Poly) (K := FracPoly) (f i))
  let q : Poly := ∏ i, den i
  have hq : q ∈ nonZeroDivisors Poly := by
    refine mem_nonZeroDivisors_iff_ne_zero.mpr ?_
    exact Finset.prod_ne_zero_iff.mpr (fun i hi => mem_nonZeroDivisors_iff_ne_zero.mp (hden i))
  refine ⟨q, hq, ?_⟩
  intro i
  let rest : Poly := Finset.prod (Finset.univ.erase i) den
  refine ⟨num i * rest, ?_⟩
  have hq_split : q = den i * rest := by
    symm
    simpa [q, rest, mul_comm] using
      (Finset.prod_erase_mul (s := Finset.univ) (f := den) (by simp : i ∈ Finset.univ))
  have hdeni : algebraMap Poly FracPoly (den i) ≠ 0 :=
    IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (hden i)
  calc
    algebraMap Poly FracPoly q * f i
        = algebraMap Poly FracPoly q * (algebraMap Poly FracPoly (num i) /
            algebraMap Poly FracPoly (den i)) := by rw [(hrepr i).symm]
    _ = algebraMap Poly FracPoly (den i * rest) * (algebraMap Poly FracPoly (num i) /
            algebraMap Poly FracPoly (den i)) := by rw [hq_split]
    _ = (algebraMap Poly FracPoly (den i) * algebraMap Poly FracPoly rest) *
            (algebraMap Poly FracPoly (num i) / algebraMap Poly FracPoly (den i)) := by
          simp [map_mul]
    _ = algebraMap Poly FracPoly (num i * rest) := by
          field_simp [hdeni]
          simp [map_mul, mul_comm]

theorem exists_common_denominator_matrix
    {ι κ : Type*}
    [Finite ι] [Finite κ]
    (A : Matrix ι κ FracPoly) :
    ∃ q : Poly, q ∈ nonZeroDivisors Poly ∧
      ∀ i j, ∃ B : Poly, algebraMap Poly FracPoly q * A i j = algebraMap Poly FracPoly B := by
  let f : ι × κ → FracPoly := fun ij => A ij.1 ij.2
  rcases exists_common_denominator f with ⟨q, hq, hclear⟩
  refine ⟨q, hq, ?_⟩
  intro i j
  simpa [f] using hclear (i, j)

theorem exists_poly_matrix_of_mul_common_denominator_matrix
    {ι κ : Type*}
    [Finite ι] [Finite κ]
    (A : Matrix ι κ FracPoly) :
    ∃ q : Poly, q ∈ nonZeroDivisors Poly ∧
      ∃ B : Matrix ι κ Poly,
        (algebraMap Poly FracPoly q) • A = mapToFrac B := by
  classical
  rcases exists_common_denominator_matrix A with ⟨q, hq, hclear⟩
  choose b hb using hclear
  refine ⟨q, hq, fun i j => b i j, ?_⟩
  ext i j
  change algebraMap Poly FracPoly q * A i j = algebraMap Poly FracPoly (b i j)
  exact hb i j

end MatrixSOS
