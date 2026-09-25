/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/

import MatrixSOS.Proof.RationalFunction.Statements
import MatrixSOS.Proof.RationalFunction.NonnegWhereDefined

/-!
# Binary sums of squares over rational functions
-/

open Matrix Polynomial
open scoped Matrix RatFunc

noncomputable section

namespace MatrixSOS

theorem ternary_isotropic_over_squareClosed_of_sqAddSq_left
    {K : Type}
    [Field K]
    [LinearOrder K]
    [IsStrictOrderedRing K]
    [NonnegSquareClosed K]
    [Algebra FracPoly K]
    {a b : FracPoly}
    (ha0 : a ≠ 0)
    (ha : ∃ r s : FracPoly, a = r ^ 2 + s ^ 2) :
    ∃ x y z : K, x ≠ 0 ∧
      x ^ 2 = algebraMap FracPoly K a * y ^ 2 + algebraMap FracPoly K b * z ^ 2 := by
  rcases ha with ⟨r, s, rfl⟩
  have hnonneg : 0 ≤ algebraMap FracPoly K (r ^ 2 + s ^ 2) := by
    have hr : 0 ≤ (algebraMap FracPoly K r) ^ 2 := sq_nonneg _
    have hs : 0 ≤ (algebraMap FracPoly K s) ^ 2 := sq_nonneg _
    simpa [map_add, map_pow] using add_nonneg hr hs
  rcases (isSquare_iff_exists_sq _).mp
      (NonnegSquareClosed.isSquare_of_nonneg hnonneg) with ⟨u, hu⟩
  have hmapa0 : algebraMap FracPoly K (r ^ 2 + s ^ 2) ≠ 0 := by
    exact (map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective FracPoly K)).2 ha0
  have hu0 : u ≠ 0 := by
    intro hu0
    apply hmapa0
    rw [hu, hu0]
    simp
  have huinv :
      algebraMap FracPoly K (r ^ 2 + s ^ 2) * (u⁻¹) ^ 2 = 1 := by
    calc
      algebraMap FracPoly K (r ^ 2 + s ^ 2) * (u⁻¹) ^ 2 = u ^ 2 * (u⁻¹) ^ 2 := by
        rw [hu]
      _ = 1 := by
        calc
          u ^ 2 * (u⁻¹) ^ 2 = (u * u) * (u⁻¹ * u⁻¹) := by ring
          _ = (u * u⁻¹) * (u * u⁻¹) := by ring
          _ = 1 := by simp [hu0]
  refine ⟨1, u⁻¹, 0, one_ne_zero, ?_⟩
  have hrep :
      algebraMap FracPoly K (r ^ 2 + s ^ 2) * (u⁻¹) ^ 2 +
          algebraMap FracPoly K b * (0 : K) ^ 2 = 1 := by
    calc
      algebraMap FracPoly K (r ^ 2 + s ^ 2) * (u⁻¹) ^ 2 +
          algebraMap FracPoly K b * (0 : K) ^ 2
          = algebraMap FracPoly K (r ^ 2 + s ^ 2) * (u⁻¹) ^ 2 := by
              simp
      _ = 1 := huinv
  simpa [pow_two] using hrep.symm

theorem fracTernaryIsotropicSqAddSqStatement_of_squareClosedLocalGlobalStatement
    (hstmt : FracTernarySquareClosedLocalGlobalStatement) :
    FracTernaryIsotropicSqAddSqStatement := by
  intro a b ha0 hb0 ha hb
  refine hstmt ha0 hb0 ?_
  intro K _ _ _ _ _
  exact ternary_isotropic_over_squareClosed_of_sqAddSq_left (K := K) ha0 ha

theorem fracBinaryRepresentsOneSqAddSqStatement_of_ternaryIsotropicSqAddSqStatement
    (hstmt : FracTernaryIsotropicSqAddSqStatement) :
    FracBinaryRepresentsOneSqAddSqStatement := by
  intro a b ha0 hb0 ha hb
  rcases hstmt ha0 hb0 ha hb with ⟨x, y, z, hx, hxyz⟩
  refine ⟨y / x, z / x, ?_⟩
  have hx2 : x ^ 2 ≠ 0 := pow_ne_zero 2 hx
  calc
    a * (y / x) ^ 2 + b * (z / x) ^ 2
        = (a * y ^ 2 + b * z ^ 2) / x ^ 2 := by
            field_simp [hx]
    _ = x ^ 2 / x ^ 2 := by rw [hxyz]
    _ = 1 := by
          field_simp [hx2]

theorem fracBinaryRepresentsOneStatement_of_sqAddSqStatement
    (hstmt : FracBinaryRepresentsOneSqAddSqStatement) :
    FracBinaryRepresentsOneStatement := by
  intro a b ha0 hb0 ha hb
  rcases exists_sq_add_sq_of_nonneg_where_defined ha with ⟨ra, sa, hsqA⟩
  rcases exists_sq_add_sq_of_nonneg_where_defined hb with ⟨rb, sb, hsqB⟩
  exact hstmt ha0 hb0 ⟨ra, sa, hsqA⟩ ⟨rb, sb, hsqB⟩

end MatrixSOS
