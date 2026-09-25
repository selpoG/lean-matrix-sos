/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/

import MatrixSOS.Proof.RationalFunction.NonnegWhereDefinedAlgebra
import MatrixSOS.Proof.Polynomial

/-!
# Nonnegativity of rational functions where defined
-/

open Matrix Polynomial
open scoped Matrix
noncomputable section

namespace MatrixSOS

theorem sq_add_sq_mul_sq_add_sq
    {R : Type*}
    [CommRing R]
    (a b c d : R) :
    (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) = (a * c + b * d) ^ 2 + (b * c - a * d) ^ 2 := by
  ring

theorem sq_add_sq_div_sq_add_sq
    {K : Type*}
    [Field K]
    (a b c d : K)
    (hcd : c ^ 2 + d ^ 2 ≠ 0) :
    (a ^ 2 + b ^ 2) / (c ^ 2 + d ^ 2) =
      ((a * c + b * d) / (c ^ 2 + d ^ 2)) ^ 2 +
        ((b * c - a * d) / (c ^ 2 + d ^ 2)) ^ 2 := by
  field_simp [hcd]
  rw [sq_add_sq_mul_sq_add_sq]

theorem exists_sq_add_sq_of_sq_add_sq_div_sq_add_sq
    {K : Type*}
    [Field K]
    (a b c d : K)
    (hcd : c ^ 2 + d ^ 2 ≠ 0) :
    ∃ u v : K, (a ^ 2 + b ^ 2) / (c ^ 2 + d ^ 2) = u ^ 2 + v ^ 2 := by
  refine ⟨(a * c + b * d) / (c ^ 2 + d ^ 2), (b * c - a * d) / (c ^ 2 + d ^ 2), ?_⟩
  exact sq_add_sq_div_sq_add_sq a b c d hcd

theorem exists_sq_add_sq_of_frac_of_nonneg_num_den
    {p q : Poly}
    (hp : ∀ x : ℝ, 0 ≤ p.eval x)
    (hq : ∀ x : ℝ, 0 ≤ q.eval x)
    (hq0 : q ≠ 0) :
    ∃ u v : FracPoly,
      algebraMap Poly FracPoly p / algebraMap Poly FracPoly q = u ^ 2 + v ^ 2 := by
  rcases exists_sq_add_sq_of_nonneg hp with ⟨a, b, hab⟩
  rcases exists_sq_add_sq_of_nonneg hq with ⟨c, d, hcd⟩
  have hsum0 : c ^ 2 + d ^ 2 ≠ 0 := by simpa [hcd] using hq0
  have hsum0' : ((algebraMap Poly FracPoly c) ^ 2 + (algebraMap Poly FracPoly d) ^ 2) ≠ 0 := by
    simpa [map_add, map_pow] using
      (map_ne_zero_iff _ (IsFractionRing.injective Poly FracPoly)).mpr hsum0
  rcases exists_sq_add_sq_of_sq_add_sq_div_sq_add_sq
      (K := FracPoly)
      (algebraMap Poly FracPoly a)
      (algebraMap Poly FracPoly b)
      (algebraMap Poly FracPoly c)
      (algebraMap Poly FracPoly d)
      hsum0' with ⟨u, v, huv⟩
  refine ⟨u, v, ?_⟩
  simpa [hab, hcd, map_add, map_pow] using huv

theorem exists_sq_add_sq_of_nonneg_frac_rep
    {r : FracPoly}
    {p q : Poly}
    (hrep : IsFracRep r p q)
    (hp : ∀ x : ℝ, 0 ≤ p.eval x)
    (hq : ∀ x : ℝ, 0 ≤ q.eval x) :
    ∃ u v : FracPoly, r = u ^ 2 + v ^ 2 := by
  rcases hrep with ⟨hq0, hr⟩
  rcases exists_sq_add_sq_of_frac_of_nonneg_num_den hp hq hq0 with ⟨u, v, huv⟩
  refine ⟨u, v, ?_⟩
  simpa [hr] using huv

theorem exists_sq_add_sq_of_nonneg_where_defined_of_rep
    {r : FracPoly}
    {p q : Poly}
    (hr : RatNonnegWhereDefined r)
    (hrep : IsFracRep r p q) :
    ∃ u v : FracPoly, r = u ^ 2 + v ^ 2 := by
  have hrep' : IsFracRep r (p * q) (q ^ 2) := isFracRep_mul_den_sq hrep
  have hpq : ∀ x : ℝ, 0 ≤ (p * q).eval x :=
    eval_mul_den_nonneg_of_nonneg_where_defined hr hrep
  have hq2 : ∀ x : ℝ, 0 ≤ (q ^ 2).eval x := by
    intro x
    simpa [Polynomial.eval_pow] using sq_nonneg (q.eval x)
  exact exists_sq_add_sq_of_nonneg_frac_rep hrep' hpq hq2

theorem exists_sq_add_sq_of_nonneg_where_defined
    {r : FracPoly}
    (hr : RatNonnegWhereDefined r) :
    ∃ u v : FracPoly, r = u ^ 2 + v ^ 2 := by
  exact exists_sq_add_sq_of_nonneg_where_defined_of_rep hr (isFracRep_num_den r)

end MatrixSOS
