/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mocho Go
-/

import MatrixSOS.Proof.TsenProjective
import Mathlib.FieldTheory.RatFunc.Basic
import Mathlib.RingTheory.Polynomial.RationalRoot

/-!
# Coefficient comparison in the proof of Tsen's theorem
-/

open Matrix Polynomial
open scoped BigOperators
noncomputable section

namespace MatrixSOS

namespace Tsen

/-- In the coefficient-comparison proof, the main variable has weight `0` and
the unknown polynomial coefficients have weight `1`. -/
def coeffWeight {σ : Type} : Option σ → ℕ
  | none => 0
  | some _ => 1

lemma weight_optionElim {σ : Type} (m : σ →₀ ℕ) (n : ℕ) :
    Finsupp.weight (coeffWeight : Option σ → ℕ) (m.optionElim n) =
      Finsupp.weight (fun _ : σ => (1 : ℕ)) m := by
  rw [Finsupp.weight_apply, Finsupp.sum_option_index_smul]
  simp [coeffWeight, Finsupp.weight_apply]

/--
If a polynomial in the main variable has weighted degree `d`, then every
coefficient is an ordinary homogeneous polynomial of degree `d` in the
coefficient variables.
-/
lemma coeff_isHomogeneous_of_optionEquivLeft_symm_weighted
    {K σ : Type} [CommSemiring K] [Finite σ]
    {p : Polynomial (MvPolynomial σ K)} {d : ℕ}
    (hp : ((MvPolynomial.optionEquivLeft K σ).symm p).IsWeightedHomogeneous
      (coeffWeight : Option σ → ℕ) d)
    (n : ℕ) :
    (p.coeff n).IsHomogeneous d := by
  classical
  intro m hm
  have hcoeff :
      ((MvPolynomial.optionEquivLeft K σ).symm p).coeff (m.optionElim n) ≠ 0 := by
    rw [← MvPolynomial.optionEquivLeft_coeff_some_coeff_none]
    simpa using hm
  have hw := hp hcoeff
  rwa [weight_optionElim] at hw

/-- A polynomial in the distinguished main variable, embedded into an
`Option`-indexed multivariate polynomial ring. -/
def polynomialInMainVar {K τ : Type} [CommSemiring K]
    (p : Polynomial K) : MvPolynomial (Option τ) K :=
  ∑ n ∈ p.support, MvPolynomial.C (p.coeff n) *
    MvPolynomial.X (none : Option τ) ^ n

lemma polynomialInMainVar_isWeightedHomogeneous
    {K τ : Type} [CommSemiring K] (p : Polynomial K) :
    (polynomialInMainVar (K := K) (τ := τ) p).IsWeightedHomogeneous
      coeffWeight 0 := by
  classical
  unfold polynomialInMainVar
  refine MvPolynomial.IsWeightedHomogeneous.sum _ _ _ ?_
  intro n _hn
  have hx :
      (MvPolynomial.X (R := K) (none : Option τ)).IsWeightedHomogeneous
        coeffWeight 0 := by
    simpa [coeffWeight] using
      MvPolynomial.isWeightedHomogeneous_X (R := K) (w := coeffWeight)
        (none : Option τ)
  have hxpow :
      (MvPolynomial.X (R := K) (none : Option τ) ^ n).IsWeightedHomogeneous
        coeffWeight (n • 0) := hx.pow n
  have hterm := hxpow.C_mul (p.coeff n)
  simpa using hterm

lemma polynomialInMainVar_degreeOf_none_le
    {K τ : Type} [Field K] (p : Polynomial K) :
    MvPolynomial.degreeOf (none : Option τ)
      (polynomialInMainVar (K := K) (τ := τ) p) ≤ p.natDegree := by
  classical
  unfold polynomialInMainVar
  refine le_trans (MvPolynomial.degreeOf_sum_le _ _ _) ?_
  rw [Finset.sup_le_iff]
  intro n hn
  refine le_trans (MvPolynomial.degreeOf_mul_le _ _ _) ?_
  calc
    MvPolynomial.degreeOf (none : Option τ)
          (MvPolynomial.C (p.coeff n) : MvPolynomial (Option τ) K) +
        MvPolynomial.degreeOf (none : Option τ)
          (MvPolynomial.X none ^ n : MvPolynomial (Option τ) K)
        ≤ 0 + n := by
          gcongr
          · rw [MvPolynomial.degreeOf_C]
          · calc
              MvPolynomial.degreeOf (none : Option τ)
                (MvPolynomial.X none ^ n : MvPolynomial (Option τ) K)
                  ≤ n * MvPolynomial.degreeOf (none : Option τ)
                      (MvPolynomial.X (R := K) none) :=
                    MvPolynomial.degreeOf_pow_le (none : Option τ)
                      (MvPolynomial.X (R := K) none) n
              _ = n := by simp
    _ = n := by simp
    _ ≤ p.natDegree := Polynomial.le_natDegree_of_mem_supp n hn

/-- The generic polynomial of degree at most `N` in the main variable assigned
to the original variable `i`. -/
def genericBoundedPoly {K ι : Type} [CommSemiring K]
    (N : ℕ) (i : ι) : MvPolynomial (Option (ι × Fin (N + 1))) K :=
  ∑ j : Fin (N + 1),
    MvPolynomial.X (some (i, j)) * MvPolynomial.X none ^ (j : ℕ)

/-- A concrete polynomial obtained by specializing the generic coefficients. -/
def boundedPolyFromCoeffs {K ι : Type} [CommSemiring K]
    (N : ℕ) (x : ι × Fin (N + 1) → K) (i : ι) : Polynomial K :=
  ∑ j : Fin (N + 1), Polynomial.C (x (i, j)) * Polynomial.X ^ (j : ℕ)

lemma boundedPolyFromCoeffs_coeff
    {K ι : Type} [Field K] (N : ℕ) (x : ι × Fin (N + 1) → K)
    (i : ι) (j : Fin (N + 1)) :
    (boundedPolyFromCoeffs (K := K) N x i).coeff (j : ℕ) = x (i, j) := by
  classical
  unfold boundedPolyFromCoeffs
  rw [Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _hk hkj
    simp [show (j : ℕ) ≠ (k : ℕ) by
      intro h
      exact hkj (Fin.ext h.symm)]
  · intro hj
    exact (hj (Finset.mem_univ j)).elim

lemma eval_genericBoundedPoly
    {K ι : Type} [Field K] (N : ℕ) (x : ι × Fin (N + 1) → K) (i : ι) :
    Polynomial.map (MvPolynomial.eval x)
      (MvPolynomial.optionEquivLeft K (ι × Fin (N + 1))
        (genericBoundedPoly (K := K) N i)) =
      boundedPolyFromCoeffs (K := K) N x i := by
  classical
  simp [genericBoundedPoly, boundedPolyFromCoeffs, Polynomial.map_sum, Polynomial.map_mul,
    Polynomial.map_pow]

lemma genericBoundedPoly_isWeightedHomogeneous
    {K ι : Type} [CommSemiring K] (N : ℕ) (i : ι) :
    (genericBoundedPoly (K := K) N i).IsWeightedHomogeneous coeffWeight 1 := by
  classical
  unfold genericBoundedPoly
  refine MvPolynomial.IsWeightedHomogeneous.sum _ _ _ ?_
  intro j _hj
  have hcoeff :
      MvPolynomial.IsWeightedHomogeneous coeffWeight
        (MvPolynomial.X (R := K) (some (i, j) : Option (ι × Fin (N + 1)))) 1 := by
    simpa [coeffWeight] using
      MvPolynomial.isWeightedHomogeneous_X (R := K) (w := coeffWeight)
        (some (i, j) : Option (ι × Fin (N + 1)))
  have hx :
      MvPolynomial.IsWeightedHomogeneous coeffWeight
        (MvPolynomial.X (R := K) (none : Option (ι × Fin (N + 1)))) 0 := by
    simpa [coeffWeight] using
      MvPolynomial.isWeightedHomogeneous_X (R := K) (w := coeffWeight)
        (none : Option (ι × Fin (N + 1)))
  have hxpow :
      MvPolynomial.IsWeightedHomogeneous coeffWeight
        (MvPolynomial.X (R := K) (none : Option (ι × Fin (N + 1))) ^ (j : ℕ))
        ((j : ℕ) • 0) := hx.pow (j : ℕ)
  have hmul := hcoeff.mul hxpow
  simpa using hmul

lemma genericBoundedPoly_degreeOf_none_le
    {K ι : Type} [Field K] (N : ℕ) (i : ι) :
    MvPolynomial.degreeOf (none : Option (ι × Fin (N + 1)))
      (genericBoundedPoly (K := K) N i) ≤ N := by
  classical
  unfold genericBoundedPoly
  refine le_trans (MvPolynomial.degreeOf_sum_le _ _ _) ?_
  rw [Finset.sup_le_iff]
  intro j _hj
  refine le_trans (MvPolynomial.degreeOf_mul_le _ _ _) ?_
  calc
    MvPolynomial.degreeOf (none : Option (ι × Fin (N + 1)))
          (MvPolynomial.X (some (i, j)) : MvPolynomial (Option (ι × Fin (N + 1))) K) +
        MvPolynomial.degreeOf (none : Option (ι × Fin (N + 1)))
          (MvPolynomial.X none ^ (j : ℕ) :
            MvPolynomial (Option (ι × Fin (N + 1))) K)
        ≤ 0 + (j : ℕ) := by
          gcongr
          · rw [MvPolynomial.degreeOf_X_of_ne]
            simp
          · calc
              MvPolynomial.degreeOf (none : Option (ι × Fin (N + 1)))
                (MvPolynomial.X none ^ (j : ℕ) :
                  MvPolynomial (Option (ι × Fin (N + 1))) K)
                  ≤ (j : ℕ) * MvPolynomial.degreeOf (none : Option (ι × Fin (N + 1)))
                      (MvPolynomial.X (R := K) none) :=
                    MvPolynomial.degreeOf_pow_le (none : Option (ι × Fin (N + 1)))
                      (MvPolynomial.X (R := K) none) (j : ℕ)
              _ = (j : ℕ) := by simp
    _ = (j : ℕ) := by simp
    _ ≤ N := Nat.lt_succ_iff.mp j.isLt

lemma genericMonomial_isWeightedHomogeneous
    {K ι : Type} [CommSemiring K] (N : ℕ) (m : ι →₀ ℕ) :
    MvPolynomial.IsWeightedHomogeneous coeffWeight
      (∏ i ∈ m.support, genericBoundedPoly (K := K) N i ^ m i) m.degree := by
  classical
  have hprod := MvPolynomial.IsWeightedHomogeneous.prod (s := m.support)
    (φ := fun i => genericBoundedPoly (K := K) N i ^ m i)
    (n := fun i => m i)
    (fun i _hi => by
      have hg := genericBoundedPoly_isWeightedHomogeneous (K := K) N i
      have hp := hg.pow (m i)
      simpa using hp)
  simpa [Finsupp.degree_apply] using hprod

lemma genericMonomial_degreeOf_none_le
    {K ι : Type} [Field K] (N : ℕ) (m : ι →₀ ℕ) :
    MvPolynomial.degreeOf (none : Option (ι × Fin (N + 1)))
      (∏ i ∈ m.support, genericBoundedPoly (K := K) N i ^ m i) ≤
        m.degree * N := by
  classical
  refine le_trans (MvPolynomial.degreeOf_prod_le _ _ _) ?_
  calc
    (∑ j ∈ m.support,
      MvPolynomial.degreeOf (none : Option (ι × Fin (N + 1)))
        (genericBoundedPoly (K := K) N j ^ m j))
        ≤ ∑ j ∈ m.support, m j * N := by
          refine Finset.sum_le_sum ?_
          intro i _hi
          calc
            MvPolynomial.degreeOf (none : Option (ι × Fin (N + 1)))
                (genericBoundedPoly (K := K) N i ^ m i)
                ≤ m i * MvPolynomial.degreeOf (none : Option (ι × Fin (N + 1)))
                    (genericBoundedPoly (K := K) N i) :=
                  MvPolynomial.degreeOf_pow_le _ _ _
            _ ≤ m i * N := by
                  gcongr
                  exact genericBoundedPoly_degreeOf_none_le (K := K) N i
    _ = m.degree * N := by
          rw [← Finset.sum_mul]
          simp [Finsupp.degree_apply]

lemma eval_genericMonomial
    {K ι : Type} [Field K] (N : ℕ) (x : ι × Fin (N + 1) → K)
    (m : ι →₀ ℕ) :
    Polynomial.map (MvPolynomial.eval x)
      (MvPolynomial.optionEquivLeft K (ι × Fin (N + 1))
        (∏ i ∈ m.support, genericBoundedPoly (K := K) N i ^ m i)) =
      ∏ i ∈ m.support, boundedPolyFromCoeffs (K := K) N x i ^ m i := by
  classical
  rw [map_prod (MvPolynomial.optionEquivLeft K (ι × Fin (N + 1)))
    (fun i => genericBoundedPoly (K := K) N i ^ m i) m.support]
  rw [Polynomial.map_prod]
  apply Finset.prod_congr rfl
  intro i _hi
  rw [map_pow (MvPolynomial.optionEquivLeft K (ι × Fin (N + 1)))]
  rw [Polynomial.map_pow]
  rw [eval_genericBoundedPoly]

/-- The cleared polynomial obtained after substituting generic bounded
polynomials into the support of a homogeneous polynomial. -/
def genericCleared {K ι : Type} [CommSemiring K]
    (N : ℕ) (S : Finset (ι →₀ ℕ))
    (a : (ι →₀ ℕ) → Polynomial K) :
    MvPolynomial (Option (ι × Fin (N + 1))) K :=
  ∑ m ∈ S,
    polynomialInMainVar (K := K) (τ := ι × Fin (N + 1)) (a m) *
      ∏ i ∈ m.support, genericBoundedPoly (K := K) N i ^ m i

lemma eval_polynomialInMainVar
    {K ι : Type} [Field K] (N : ℕ) (x : ι × Fin (N + 1) → K)
    (p : Polynomial K) :
    Polynomial.map (MvPolynomial.eval x)
      (MvPolynomial.optionEquivLeft K (ι × Fin (N + 1))
        (polynomialInMainVar (K := K) (τ := ι × Fin (N + 1)) p)) = p := by
  classical
  ext n
  by_cases h : p.coeff n = 0
  · simp [polynomialInMainVar, Polynomial.coeff_map, h]
  · simp [polynomialInMainVar, Polynomial.coeff_map, h]

lemma eval_genericCleared
    {K ι : Type} [Field K] (N : ℕ) (x : ι × Fin (N + 1) → K)
    (S : Finset (ι →₀ ℕ)) (a : (ι →₀ ℕ) → Polynomial K) :
    Polynomial.map (MvPolynomial.eval x)
      (MvPolynomial.optionEquivLeft K (ι × Fin (N + 1))
        (genericCleared (K := K) N S a)) =
      ∑ m ∈ S, a m *
        ∏ i ∈ m.support, boundedPolyFromCoeffs (K := K) N x i ^ m i := by
  classical
  unfold genericCleared
  rw [map_sum (MvPolynomial.optionEquivLeft K (ι × Fin (N + 1)))
    (fun m => polynomialInMainVar (K := K) (τ := ι × Fin (N + 1)) (a m) *
      ∏ i ∈ m.support, genericBoundedPoly (K := K) N i ^ m i) S]
  rw [Polynomial.map_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [map_mul]
  rw [Polynomial.map_mul]
  rw [eval_polynomialInMainVar]
  rw [eval_genericMonomial]

lemma genericCleared_isWeightedHomogeneous
    {K ι : Type} [CommSemiring K] (N : ℕ) (S : Finset (ι →₀ ℕ))
    (a : (ι →₀ ℕ) → Polynomial K) (d : ℕ)
    (hS : ∀ m ∈ S, m.degree = d) :
    (genericCleared (K := K) N S a).IsWeightedHomogeneous coeffWeight d := by
  classical
  unfold genericCleared
  refine MvPolynomial.IsWeightedHomogeneous.sum _ _ _ ?_
  intro m hm
  have hcoeff :=
    polynomialInMainVar_isWeightedHomogeneous
      (K := K) (τ := ι × Fin (N + 1)) (a m)
  have hmon := genericMonomial_isWeightedHomogeneous (K := K) N m
  have hmul := hcoeff.mul hmon
  simpa [hS m hm] using hmul

lemma genericCleared_degreeOf_none_le
    {K ι : Type} [Field K] (N D d : ℕ) (S : Finset (ι →₀ ℕ))
    (a : (ι →₀ ℕ) → Polynomial K)
    (hD : ∀ m ∈ S, (a m).natDegree ≤ D)
    (hdeg : ∀ m ∈ S, m.degree = d) :
    MvPolynomial.degreeOf (none : Option (ι × Fin (N + 1)))
      (genericCleared (K := K) N S a) ≤ D + d * N := by
  classical
  unfold genericCleared
  refine le_trans (MvPolynomial.degreeOf_sum_le _ _ _) ?_
  rw [Finset.sup_le_iff]
  intro m hm
  refine le_trans (MvPolynomial.degreeOf_mul_le _ _ _) ?_
  calc
    MvPolynomial.degreeOf (none : Option (ι × Fin (N + 1)))
          (polynomialInMainVar (K := K) (τ := ι × Fin (N + 1)) (a m)) +
        MvPolynomial.degreeOf (none : Option (ι × Fin (N + 1)))
          (∏ i ∈ m.support, genericBoundedPoly (K := K) N i ^ m i)
        ≤ (a m).natDegree + m.degree * N := by
          gcongr
          · exact polynomialInMainVar_degreeOf_none_le
              (K := K) (τ := ι × Fin (N + 1)) (a m)
          · exact genericMonomial_degreeOf_none_le (K := K) N m
    _ ≤ D + d * N := by
          gcongr
          · exact hD m hm
          · rw [hdeg m hm]

lemma genericCleared_coeff_isHomogeneous
    {K ι : Type} [Field K] [Finite ι]
    (N d n : ℕ) (S : Finset (ι →₀ ℕ))
    (a : (ι →₀ ℕ) → Polynomial K)
    (hS : ∀ m ∈ S, m.degree = d) :
    ((MvPolynomial.optionEquivLeft K (ι × Fin (N + 1))
      (genericCleared (K := K) N S a)).coeff n).IsHomogeneous d := by
  classical
  exact coeff_isHomogeneous_of_optionEquivLeft_symm_weighted
    (K := K) (σ := ι × Fin (N + 1))
    (p := MvPolynomial.optionEquivLeft K (ι × Fin (N + 1))
      (genericCleared (K := K) N S a))
    (by
      simpa using genericCleared_isWeightedHomogeneous (K := K) N S a d hS)
    n

lemma ratFunc_map_num_eq_mul_map_denom_general
    {K : Type} [Field K] (x : RatFunc K) :
    algebraMap (Polynomial K) (RatFunc K) x.num =
      x * algebraMap (Polynomial K) (RatFunc K) x.denom := by
  calc
    algebraMap (Polynomial K) (RatFunc K) x.num
        =
          (algebraMap (Polynomial K) (RatFunc K) x.num /
              algebraMap (Polynomial K) (RatFunc K) x.denom) *
            algebraMap (Polynomial K) (RatFunc K) x.denom := by
              field_simp [RatFunc.denom_ne_zero x]
    _ = x * algebraMap (Polynomial K) (RatFunc K) x.denom := by
          rw [RatFunc.num_div_denom x]

/-- A common denominator for all coefficients of a multivariate polynomial over
`K(X)`. -/
def commonDenom {K ι : Type} [Field K]
    (P : MvPolynomial ι (RatFunc K)) : Polynomial K :=
  ∏ m ∈ P.support, RatFunc.denom (P.coeff m)

/-- The coefficient obtained after multiplying a coefficient of `P` by the
common denominator. -/
def clearedCoeff {K ι : Type} [Field K] [DecidableEq ι]
    (P : MvPolynomial ι (RatFunc K)) (m : ι →₀ ℕ) : Polynomial K :=
  RatFunc.num (P.coeff m) *
    ∏ n ∈ P.support.erase m, RatFunc.denom (P.coeff n)

/-- The maximum degree of the polynomial coefficients after clearing
denominators. -/
def clearedCoeffMaxDegree {K ι : Type} [Field K] [DecidableEq ι]
    (P : MvPolynomial ι (RatFunc K)) : ℕ :=
  P.support.sup fun m => (clearedCoeff (K := K) P m).natDegree

lemma clearedCoeff_natDegree_le_maxDegree
    {K ι : Type} [Field K] [DecidableEq ι]
    (P : MvPolynomial ι (RatFunc K)) {m : ι →₀ ℕ} (hm : m ∈ P.support) :
    (clearedCoeff (K := K) P m).natDegree ≤
      clearedCoeffMaxDegree (K := K) P := by
  unfold clearedCoeffMaxDegree
  exact Finset.le_sup (s := P.support)
    (f := fun m => (clearedCoeff (K := K) P m).natDegree) hm

lemma commonDenom_ne_zero {K ι : Type} [Field K]
    (P : MvPolynomial ι (RatFunc K)) :
    commonDenom (K := K) P ≠ 0 := by
  unfold commonDenom
  exact Finset.prod_ne_zero_iff.mpr fun m _hm =>
    RatFunc.denom_ne_zero (P.coeff m)

lemma map_commonDenom_mul_coeff_eq_map_clearedCoeff
    {K ι : Type} [Field K] [DecidableEq ι]
    (P : MvPolynomial ι (RatFunc K)) {m : ι →₀ ℕ} (hm : m ∈ P.support) :
    algebraMap (Polynomial K) (RatFunc K) (commonDenom (K := K) P) *
        P.coeff m =
      algebraMap (Polynomial K) (RatFunc K) (clearedCoeff (K := K) P m) := by
  classical
  have hprod : commonDenom (K := K) P =
      RatFunc.denom (P.coeff m) *
        ∏ n ∈ P.support.erase m, RatFunc.denom (P.coeff n) := by
    unfold commonDenom
    calc
      (∏ x ∈ P.support, RatFunc.denom (P.coeff x))
          =
            (∏ x ∈ P.support.erase m, RatFunc.denom (P.coeff x)) *
              RatFunc.denom (P.coeff m) := by
                exact (Finset.prod_erase_mul (s := P.support) (a := m)
                  (f := fun x => RatFunc.denom (P.coeff x)) hm).symm
      _ = RatFunc.denom (P.coeff m) *
            ∏ x ∈ P.support.erase m, RatFunc.denom (P.coeff x) := by
              ring
  have hnum := ratFunc_map_num_eq_mul_map_denom_general (K := K) (P.coeff m)
  calc
    algebraMap (Polynomial K) (RatFunc K) (commonDenom (K := K) P) * P.coeff m
        =
          (algebraMap (Polynomial K) (RatFunc K) (RatFunc.denom (P.coeff m)) *
            algebraMap (Polynomial K) (RatFunc K)
              (∏ n ∈ P.support.erase m, RatFunc.denom (P.coeff n))) *
            P.coeff m := by
              rw [hprod, map_mul]
    _ =
        algebraMap (Polynomial K) (RatFunc K)
            (∏ n ∈ P.support.erase m, RatFunc.denom (P.coeff n)) *
          (P.coeff m *
            algebraMap (Polynomial K) (RatFunc K) (RatFunc.denom (P.coeff m))) := by
          ring
    _ =
        algebraMap (Polynomial K) (RatFunc K)
            (∏ n ∈ P.support.erase m, RatFunc.denom (P.coeff n)) *
          algebraMap (Polynomial K) (RatFunc K) (RatFunc.num (P.coeff m)) := by
          rw [← hnum]
    _ = algebraMap (Polynomial K) (RatFunc K) (clearedCoeff (K := K) P m) := by
          rw [clearedCoeff, map_mul]
          ring

lemma map_commonDenom_mul_eval_eq_map_clearedSum
    {K ι : Type} [Field K] [DecidableEq ι]
    (P : MvPolynomial ι (RatFunc K)) (z : ι → Polynomial K) :
    algebraMap (Polynomial K) (RatFunc K) (commonDenom (K := K) P) *
        MvPolynomial.eval (fun i => algebraMap (Polynomial K) (RatFunc K) (z i)) P =
      algebraMap (Polynomial K) (RatFunc K)
        (∑ m ∈ P.support, clearedCoeff (K := K) P m *
          ∏ i ∈ m.support, z i ^ m i) := by
  classical
  rw [MvPolynomial.eval_eq]
  rw [Finset.mul_sum]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro m hm
  have hcoeff := map_commonDenom_mul_coeff_eq_map_clearedCoeff (K := K) P hm
  calc
    algebraMap (Polynomial K) (RatFunc K) (commonDenom (K := K) P) *
        (P.coeff m * ∏ i ∈ m.support, algebraMap (Polynomial K) (RatFunc K) (z i) ^ m i)
      =
        (algebraMap (Polynomial K) (RatFunc K) (commonDenom (K := K) P) * P.coeff m) *
          ∏ i ∈ m.support, algebraMap (Polynomial K) (RatFunc K) (z i) ^ m i := by
          ring
    _ =
        algebraMap (Polynomial K) (RatFunc K) (clearedCoeff (K := K) P m) *
          ∏ i ∈ m.support, algebraMap (Polynomial K) (RatFunc K) (z i) ^ m i := by
          rw [hcoeff]
    _ =
        algebraMap (Polynomial K) (RatFunc K) (clearedCoeff (K := K) P m) *
          ∏ i ∈ m.support, algebraMap (Polynomial K) (RatFunc K) (z i ^ m i) := by
          congr 1
          apply Finset.prod_congr rfl
          intro i _hi
          rw [map_pow]
    _ =
        algebraMap (Polynomial K) (RatFunc K)
          (clearedCoeff (K := K) P m * ∏ i ∈ m.support, z i ^ m i) := by
          simp [map_mul, map_prod]

/--
Tsen's theorem for the rational function field `K(X)`, in the `C₁` form used
by this project, assuming the projective homogeneous dimension-count input over
`K`.

Concretely, every positive-degree homogeneous polynomial over `K(X)` in more
variables than its degree has a nontrivial zero.
-/
private theorem ratFunc_c1FieldStatement_of_projectiveHomogeneousDimensionStatement
    {K : Type} [Field K]
    (hproj : ProjectiveHomogeneousDimensionStatement K) :
    C1FieldStatement (RatFunc K) := by
  classical
  intro ι _hι d hdpos hvars P hhom
  let := Classical.decEq ι
  let D : ℕ := clearedCoeffMaxDegree (K := K) P
  let N : ℕ := D
  let B : ℕ := D + d * N
  let G : MvPolynomial (Option (ι × Fin (N + 1))) K :=
    genericCleared (K := K) N P.support (clearedCoeff (K := K) P)
  have hsupportDegree : ∀ m ∈ P.support, m.degree = d := by
    intro m hm
    have hw := hhom (MvPolynomial.mem_support_iff.mp hm)
    simpa [Finsupp.degree_apply, Finsupp.weight_apply, Finsupp.sum] using hw
  have hD : ∀ m ∈ P.support, (clearedCoeff (K := K) P m).natDegree ≤ D := by
    intro m hm
    exact clearedCoeff_natDegree_le_maxDegree (K := K) P hm
  have hdegG : MvPolynomial.degreeOf (none : Option (ι × Fin (N + 1))) G ≤ B := by
    dsimp [G, B]
    exact genericCleared_degreeOf_none_le (K := K) N D d P.support
      (clearedCoeff (K := K) P) hD hsupportDegree
  have hnatG : (MvPolynomial.optionEquivLeft K (ι × Fin (N + 1)) G).natDegree ≤ B := by
    rw [MvPolynomial.natDegree_optionEquivLeft]
    exact hdegG
  have hcard : Fintype.card (Fin (B + 1)) < Fintype.card (ι × Fin (N + 1)) := by
    have hcpos : 0 < Fintype.card ι := lt_trans hdpos hvars
    have hcalc : D + d * D + 1 < Fintype.card ι * (D + 1) := by
      calc
        D + d * D + 1 = (d + 1) * D + 1 := by ring
        _ ≤ Fintype.card ι * D + 1 := by
              gcongr
              exact Nat.succ_le_of_lt hvars
        _ < Fintype.card ι * D + Fintype.card ι := by omega
        _ = Fintype.card ι * (D + 1) := by ring
    simpa [B, N, Fintype.card_prod, Fintype.card_fin] using hcalc
  rcases hproj (ι := ι × Fin (N + 1)) (κ := Fin (B + 1)) hcard
      (fun k : Fin (B + 1) =>
        (MvPolynomial.optionEquivLeft K (ι × Fin (N + 1)) G).coeff (k : ℕ))
      (fun k => ⟨d, hdpos, by
        dsimp [G]
        exact genericCleared_coeff_isHomogeneous (K := K) (ι := ι) N d (k : ℕ)
          P.support (clearedCoeff (K := K) P) hsupportDegree⟩) with
    ⟨x, hxnonzero, hxzero⟩
  have hpolyZero :
      Polynomial.map (MvPolynomial.eval x)
        (MvPolynomial.optionEquivLeft K (ι × Fin (N + 1)) G) = 0 := by
    ext n
    by_cases hn : n ≤ B
    · have hz := hxzero ⟨n, Nat.lt_succ_of_le hn⟩
      simpa [Polynomial.coeff_map] using hz
    · have hcoeff : (MvPolynomial.optionEquivLeft K (ι × Fin (N + 1)) G).coeff n = 0 := by
        exact Polynomial.natDegree_le_iff_coeff_eq_zero.mp hnatG n (Nat.lt_of_not_ge hn)
      simp [Polynomial.coeff_map, hcoeff]
  let y : ι → RatFunc K := fun i =>
    algebraMap (Polynomial K) (RatFunc K) (boundedPolyFromCoeffs (K := K) N x i)
  have hyNonzero : ∃ i : ι, y i ≠ 0 := by
    rcases hxnonzero with ⟨v, hv⟩
    refine ⟨v.1, ?_⟩
    intro hy
    have hpoly : boundedPolyFromCoeffs (K := K) N x v.1 = 0 := by
      exact (map_eq_zero_iff _
        (IsFractionRing.injective (R := Polynomial K) (K := RatFunc K))).mp hy
    have hcoeff := congrArg (fun p : Polynomial K => p.coeff (v.2 : ℕ)) hpoly
    have hcoeff_zero : (boundedPolyFromCoeffs (K := K) N x v.1).coeff (v.2 : ℕ) = 0 := by
      simpa using hcoeff
    rw [boundedPolyFromCoeffs_coeff] at hcoeff_zero
    exact hv hcoeff_zero
  have hclearedPolyZero :
      ∑ m ∈ P.support, clearedCoeff (K := K) P m *
        ∏ i ∈ m.support, boundedPolyFromCoeffs (K := K) N x i ^ m i = 0 := by
    have h := hpolyZero
    rw [eval_genericCleared] at h
    simpa [G] using h
  have hratClear :
      algebraMap (Polynomial K) (RatFunc K) (commonDenom (K := K) P) *
          MvPolynomial.eval y P = 0 := by
    have hmap := congrArg (algebraMap (Polynomial K) (RatFunc K)) hclearedPolyZero
    simp only [map_zero] at hmap
    rw [map_commonDenom_mul_eval_eq_map_clearedSum
      (K := K) P (fun i => boundedPolyFromCoeffs (K := K) N x i)]
    exact hmap
  have hq0 : algebraMap (Polynomial K) (RatFunc K) (commonDenom (K := K) P) ≠ 0 := by
    exact (map_ne_zero_iff _
      (IsFractionRing.injective (R := Polynomial K) (K := RatFunc K))).2
      (commonDenom_ne_zero (K := K) P)
  have hyzero : MvPolynomial.eval y P = 0 := by
    exact (mul_eq_zero.mp hratClear).resolve_left hq0
  exact ⟨y, hyNonzero, hyzero⟩

/-- Tsen's theorem for `K(X)` when `K` is algebraically closed. -/
theorem algebraicallyClosed_ratFunc_c1FieldStatement
    (K : Type) [Field K] [IsAlgClosed K] :
    C1FieldStatement (RatFunc K) :=
  ratFunc_c1FieldStatement_of_projectiveHomogeneousDimensionStatement
    (algebraicallyClosed_commonZero_of_homogeneous K)

end Tsen

end MatrixSOS
