/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import MatrixSOS.Proof.RationalFunction.Statements
import MatrixSOS.Proof.RationalFunction.NonnegWhereDefined
import MatrixSOS.Proof.QuadraticForms

open Matrix Polynomial
open scoped QuadraticAlgebra Matrix
noncomputable section

namespace MatrixSOS

theorem fracTernaryPlainIsotropicOverSquareClosedExtensions_of_local
    {a b : FracPoly}
    (h : FracTernaryIsotropicOverSquareClosedExtensions a b) :
    FracTernaryPlainIsotropicOverSquareClosedExtensions a b := by
  intro K _ _ _ _ _
  rcases h (K := K) with ⟨x, y, z, hx, hxyz⟩
  exact ⟨x, y, z, Or.inl hx, hxyz⟩

theorem fracPfister2PlainIsotropicOverSquareClosedExtensions_iff_ternary
    {a b : FracPoly} :
    FracPfister2PlainIsotropicOverSquareClosedExtensions a b ↔
      FracTernaryPlainIsotropicOverSquareClosedExtensions a b := by
  constructor
  · intro h K _ _ _ _ _
    rcases h (K := K) with ⟨x, y, z, w, hneq, hpf⟩
    exact exists_ternary_isotropic_of_exists_pfister2_isotropic
      ⟨x, y, z, w, hneq, by simpa [map_mul] using hpf⟩
  · intro h K _ _ _ _ _
    rcases h (K := K) with ⟨x, y, z, hneq, hxyz⟩
    exact exists_pfister2_isotropic_of_exists_ternary_isotropic
      ⟨x, y, z, hneq, hxyz⟩

/-- If `-cd` is a sum of two squares, then the diagonal 4-form `⟨c, c, d, d⟩` is isotropic via
the explicit vector `(u, v, c, 0)`. -/
theorem exists_ccdd_isotropic_of_neg_mul_sum_two_squares
    {K : Type*}
    [Field K]
    {c d u v : K}
    (hc0 : c ≠ 0)
    (hcd : -c * d = u ^ 2 + v ^ 2) :
    ∃ x y z w : K,
      (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0 ∨ w ≠ 0) ∧
      c * x ^ 2 + c * y ^ 2 + d * z ^ 2 + d * w ^ 2 = 0 := by
  refine ⟨u, v, c, 0, Or.inr <| Or.inr <| Or.inl hc0, ?_⟩
  calc
    c * u ^ 2 + c * v ^ 2 + d * c ^ 2 + d * (0 : K) ^ 2
        = c * (u ^ 2 + v ^ 2) + d * c ^ 2 := by ring
    _ = c * (-c * d) + d * c ^ 2 := by rw [hcd]
    _ = 0 := by ring

theorem exists_ccdd_isotropic_iff_neg_mul_pos_of_squareClosed
    {K : Type*}
    [Field K]
    [LinearOrder K]
    [IsStrictOrderedRing K]
    [NonnegSquareClosed K]
    {c d : K}
    (hc0 : c ≠ 0)
    (hd0 : d ≠ 0) :
    (∃ x y z w : K,
      (x ≠ 0 ∨ y ≠ 0 ∨ z ≠ 0 ∨ w ≠ 0) ∧
      c * x ^ 2 + c * y ^ 2 + d * z ^ 2 + d * w ^ 2 = 0) ↔
      0 < -c * d := by
  constructor
  · rintro ⟨x, y, z, w, hneq, hsum⟩
    by_cases hc : 0 < c
    · by_cases hd : 0 < d
      · have hcx_nonneg : 0 ≤ c * x ^ 2 := mul_nonneg (le_of_lt hc) (sq_nonneg x)
        have hcy_nonneg : 0 ≤ c * y ^ 2 := mul_nonneg (le_of_lt hc) (sq_nonneg y)
        have hdz_nonneg : 0 ≤ d * z ^ 2 := mul_nonneg (le_of_lt hd) (sq_nonneg z)
        have hdw_nonneg : 0 ≤ d * w ^ 2 := mul_nonneg (le_of_lt hd) (sq_nonneg w)
        have hsum_pos : 0 < c * x ^ 2 + c * y ^ 2 + d * z ^ 2 + d * w ^ 2 := by
          rcases hneq with hx | hy | hz | hw
          · have hcx_pos : 0 < c * x ^ 2 := mul_pos hc (sq_pos_iff.mpr hx)
            nlinarith
          · have hcy_pos : 0 < c * y ^ 2 := mul_pos hc (sq_pos_iff.mpr hy)
            nlinarith
          · have hdz_pos : 0 < d * z ^ 2 := mul_pos hd (sq_pos_iff.mpr hz)
            nlinarith
          · have hdw_pos : 0 < d * w ^ 2 := mul_pos hd (sq_pos_iff.mpr hw)
            nlinarith
        nlinarith
      · have hdneg : d < 0 := lt_of_le_of_ne (le_of_not_gt hd) hd0
        simpa [neg_mul] using (neg_pos.mpr (mul_neg_of_pos_of_neg hc hdneg))
    · have hcneg : c < 0 := lt_of_le_of_ne (le_of_not_gt hc) hc0
      by_cases hd : 0 < d
      · simpa [neg_mul] using (neg_pos.mpr (mul_neg_of_neg_of_pos hcneg hd))
      · have hdneg : d < 0 := lt_of_le_of_ne (le_of_not_gt hd) hd0
        have hcx_nonpos : c * x ^ 2 ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (le_of_lt hcneg) (sq_nonneg x)
        have hcy_nonpos : c * y ^ 2 ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (le_of_lt hcneg) (sq_nonneg y)
        have hdz_nonpos : d * z ^ 2 ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (le_of_lt hdneg) (sq_nonneg z)
        have hdw_nonpos : d * w ^ 2 ≤ 0 :=
          mul_nonpos_of_nonpos_of_nonneg (le_of_lt hdneg) (sq_nonneg w)
        have hsum_neg : c * x ^ 2 + c * y ^ 2 + d * z ^ 2 + d * w ^ 2 < 0 := by
          rcases hneq with hx | hy | hz | hw
          · have hcx_neg : c * x ^ 2 < 0 := mul_neg_of_neg_of_pos hcneg (sq_pos_iff.mpr hx)
            nlinarith
          · have hcy_neg : c * y ^ 2 < 0 := mul_neg_of_neg_of_pos hcneg (sq_pos_iff.mpr hy)
            nlinarith
          · have hdz_neg : d * z ^ 2 < 0 := mul_neg_of_neg_of_pos hdneg (sq_pos_iff.mpr hz)
            nlinarith
          · have hdw_neg : d * w ^ 2 < 0 := mul_neg_of_neg_of_pos hdneg (sq_pos_iff.mpr hw)
            nlinarith
        nlinarith
  · intro hcd
    rcases (isSquare_iff_exists_sq (-c * d)).mp
        (NonnegSquareClosed.isSquare_of_nonneg (le_of_lt hcd)) with ⟨u, hu⟩
    exact exists_ccdd_isotropic_of_neg_mul_sum_two_squares (c := c) (d := d) (u := u) (v := 0)
      hc0 (by simp [hu])

theorem fracCCDDPlainIsotropicOverSquareClosedExtensions_iff_neg_mul_pos
    {c d : FracPoly}
    (hc0 : c ≠ 0)
    (hd0 : d ≠ 0) :
    FracCCDDPlainIsotropicOverSquareClosedExtensions c d ↔
      ∀ {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [NonnegSquareClosed K]
          [Algebra FracPoly K],
        0 < -algebraMap FracPoly K c * algebraMap FracPoly K d := by
  constructor
  · intro h K _ _ _ _ _
    exact (exists_ccdd_isotropic_iff_neg_mul_pos_of_squareClosed
      (K := K)
      ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective FracPoly K)).2 hc0)
      ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective FracPoly K)).2 hd0)).mp
        (h (K := K))
  · intro h K _ _ _ _ _
    exact (exists_ccdd_isotropic_iff_neg_mul_pos_of_squareClosed
      (K := K)
      ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective FracPoly K)).2 hc0)
      ((map_ne_zero_iff _ (FaithfulSMul.algebraMap_injective FracPoly K)).2 hd0)).mpr
        (h (K := K))

theorem
    fracCCDDPlainIsotropicOverSquareClosedExtensionsNonnegWhereDefinedStatement_of_strictPosNonnegWhereDefinedStatement
    (hstmt : FracStrictPosOverSquareClosedExtensionsNonnegWhereDefinedStatement) :
    FracCCDDPlainIsotropicOverSquareClosedExtensionsNonnegWhereDefinedStatement := by
  intro c d hc0 hd0 hlocal
  have hallPos :
      ∀ {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [NonnegSquareClosed K]
          [Algebra FracPoly K],
        0 < -algebraMap FracPoly K c * algebraMap FracPoly K d :=
    (fracCCDDPlainIsotropicOverSquareClosedExtensions_iff_neg_mul_pos hc0 hd0).mp hlocal
  have hpos :
      ∀ {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [NonnegSquareClosed K]
          [Algebra FracPoly K],
        0 < algebraMap FracPoly K (-c * d) := by
    intro K _ _ _ _ _
    simpa [map_mul] using hallPos (K := K)
  exact hstmt hpos

theorem
    fracCCDDPlainIsotropicOverSquareClosedExtensionsSqAddSqStatement_of_ccddNonnegWhereDefinedStatement
    (hstmt : FracCCDDPlainIsotropicOverSquareClosedExtensionsNonnegWhereDefinedStatement) :
    FracCCDDPlainIsotropicOverSquareClosedExtensionsSqAddSqStatement := by
  intro c d hc0 hd0 hlocal
  exact exists_sq_add_sq_of_nonneg_where_defined (hstmt hc0 hd0 hlocal)

theorem fracTernarySquareClosedLocalGlobalStatement_of_isotropicStatement
    (hstmt : FracTernaryIsotropicSquareClosedLocalGlobalStatement) :
    FracTernarySquareClosedLocalGlobalStatement := by
  intro a b ha0 hb0 hlocal
  have hplain : FracTernaryPlainIsotropicOverSquareClosedExtensions a b :=
    fracTernaryPlainIsotropicOverSquareClosedExtensions_of_local hlocal
  rcases hstmt ha0 hb0 hplain with ⟨x, y, z, hneq, hxyz⟩
  exact exists_first_nonzero_of_ternary_isotropic ha0 hb0 hneq hxyz


end MatrixSOS
