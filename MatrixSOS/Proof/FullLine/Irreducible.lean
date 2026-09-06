/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import MatrixSOS.Proof.NoRealRootDescent.ComplexRoots.Irreducible

open Matrix Polynomial
open scoped Matrix
noncomputable section

namespace MatrixSOS

private theorem matrix_smul_left_cancel_poly
    {ι κ : Type*}
    {c : Poly}
    (hc : c ≠ 0)
    {A B : Matrix ι κ Poly}
    (h : c • A = c • B) :
    A = B := by
  funext i j
  have hij := congrArg (fun M => M i j) h
  have hij' : c * A i j = c * B i j := by
    simpa [Matrix.smul_apply] using hij
  exact (mul_left_cancel₀ hc : c * A i j = c * B i j → A i j = B i j) hij'

theorem polynomial_square_factor_of_irreducible_scaled_square_of_step
    {n : Type*}
    [Fintype n]
    {p : Poly}
    (hp0 : p ≠ 0)
    (hpow :
      ∀ Q : Matrix n n Poly,
        EntrywiseDvdBy (p ^ 2) (Q.transpose * Q) →
          ∃ U : Matrix n n Poly, Q.transpose * Q = (p ^ 2) • (U.transpose * U))
    (A : Matrix n n Poly)
    {T : Matrix n n Poly}
    (hT : (p ^ 2) • A = T.transpose * T) :
    ∃ U : Matrix n n Poly, A = U.transpose * U := by
  have hdiv : EntrywiseDvdBy (p ^ 2) (T.transpose * T) :=
    entrywiseDvdBy_sq_of_scaled_gram hT
  rcases hpow T hdiv with ⟨U, hU⟩
  refine ⟨U, matrix_smul_left_cancel_poly (c := p ^ 2) ?_ ?_⟩
  · exact pow_ne_zero 2 hp0
  · rw [hT, hU]

theorem polynomial_square_factor_descent_of_irreducible_scaled_square_of_isRoot
    {n : Type*}
    [Fintype n]
    {p : Poly}
    (hp : Irreducible p)
    {a : ℝ}
    (ha : p.IsRoot a)
    (A : Matrix n n Poly)
    {T : Matrix n n Poly}
    (hT : (p ^ 2) • A = T.transpose * T) :
    ∃ U : Matrix n n Poly, A = U.transpose * U := by
  classical
  have hfactor :
      ∀ Q : Matrix n n Poly,
        EntrywiseDvdBy (p ^ 2) (Q.transpose * Q) →
          ∃ U : Matrix n n Poly, Q.transpose * Q = (p ^ 2) • (U.transpose * U) := by
    intro Q hQ
    have hEval : mapEval a Q = 0 := by
      have hdiv : EntrywiseDvdBy p (Q.transpose * Q) := entrywiseDvdBy_of_sq hQ
      have hrootGram : mapEval a (Q.transpose * Q) = 0 := by
        ext i j
        have hroot : ((Q.transpose * Q) i j).IsRoot a :=
          Polynomial.dvd_iff_isRoot.mp
            ((irreducible_associated_X_sub_C_of_isRoot hp ha).dvd_iff_dvd_left.mp
              (hdiv i j))
        simpa [Polynomial.IsRoot] using hroot
      have hEvalGram :
          (mapEval a Q).transpose * mapEval a Q = 0 := by
        simpa [mapEval_mul] using hrootGram
      simpa using (Matrix.conjTranspose_mul_self_eq_zero (A := mapEval a Q)).mp hEvalGram
    have hdivQ : EntrywiseDvdBy p Q := by
      intro i j
      have hroot : (Q i j).IsRoot a := by
        simpa [Polynomial.IsRoot, mapEval] using congrArg (fun M => M i j) hEval
      exact (irreducible_associated_X_sub_C_of_isRoot hp ha).dvd_iff_dvd_left.mpr
        (Polynomial.dvd_iff_isRoot.mpr hroot)
    rcases (entrywiseDvdBy_iff_exists_smul p Q).mp hdivQ with ⟨U, hU⟩
    refine ⟨U, ?_⟩
    calc
      Q.transpose * Q = (p • U).transpose * (p • U) := by rw [hU]
      _ = (p ^ 2) • (U.transpose * U) := by
          rw [Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul]
          simp [pow_two, smul_smul]
  exact polynomial_square_factor_of_irreducible_scaled_square_of_step
    hp.ne_zero hfactor A hT

theorem polynomial_square_factor_descent_of_normalized_irreducible_sqAddSq_scaled_square
    {n : Type*}
    [Fintype n]
    {p a b : Poly}
    (hp : Irreducible p)
    (hnorm : normalize p = p)
    (hnoroot : ∀ a : ℝ, ¬ p.IsRoot a)
    (hpab : p = a ^ 2 + b ^ 2)
    (A : Matrix n n Poly)
    {T : Matrix n n Poly}
    (hT : (p ^ 2) • A = T.transpose * T) :
    ∃ U : Matrix n n Poly, A = U.transpose * U := by
  classical
  have hfactor :
      ∀ Q : Matrix n n Poly,
        EntrywiseDvdBy (p ^ 2) (Q.transpose * Q) →
          ∃ U : Matrix n n Poly, Q.transpose * Q = (p ^ 2) • (U.transpose * U) := by
    intro Q hQ
    exact gram_factor_of_normalized_irreducible_noRoot_sqAddSq hp hnorm hnoroot hpab Q hQ
  exact polynomial_square_factor_of_irreducible_scaled_square_of_step
    hp.ne_zero hfactor A hT

private theorem prod_normalizedFactors_poly
    {q : Poly}
    (hq : q ≠ 0) :
    (UniqueFactorizationMonoid.normalizedFactors q).prod = normalize q :=
  UniqueFactorizationMonoid.prod_normalizedFactors_eq hq

private theorem irreducible_of_mem_normalizedFactors_poly
    {q p : Poly}
    (hp : p ∈ UniqueFactorizationMonoid.normalizedFactors q) :
    Irreducible p :=
  (UniqueFactorizationMonoid.prime_of_normalized_factor p hp).irreducible

theorem polynomial_square_factor_of_scaled_square_ne_zero
    {n : Type*}
    [Fintype n]
    (A : Matrix n n Poly)
    {q : Poly}
    (hq : q ≠ 0)
    {T : Matrix n n Poly}
    (hT : (q ^ 2) • A = T.transpose * T) :
    ∃ U : Matrix n n Poly, A = U.transpose * U := by
  classical
  have hnorm :
      ∃ T' : Matrix n n Poly,
        ((normalize q) ^ 2) • A = T'.transpose * T' := by
    rcases associated_normalize q with ⟨u, hu⟩
    refine ⟨(u : Poly) • T, ?_⟩
    calc
      ((normalize q) ^ 2) • A = (((u : Poly) ^ 2) * (q ^ 2)) • A := by
        rw [← hu]
        simp [pow_two, mul_left_comm, mul_comm]
      _ = ((u : Poly) ^ 2) • ((q ^ 2) • A) := by
        simp [smul_smul]
      _ = ((u : Poly) ^ 2) • (T.transpose * T) := by rw [hT]
      _ = (((u : Poly) • T).transpose) * ((u : Poly) • T) := by
        rw [Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul]
        simp [pow_two, smul_smul]
  rcases hnorm with ⟨T', hT'⟩
  have hmain :
      ∀ s : Multiset Poly,
        (∀ p ∈ s, Irreducible p) →
        (∀ p ∈ s, normalize p = p) →
        ∀ {R : Matrix n n Poly},
          ((s.prod ^ 2) • A = R.transpose * R) →
          ∃ U : Matrix n n Poly, A = U.transpose * U := by
    intro s hs hsnorm
    induction s using Multiset.induction_on with
    | empty =>
        intro R hR
        refine ⟨R, ?_⟩
        simpa using hR
    | cons p s ih =>
        intro R hR
        have hp : Irreducible p := hs p (Multiset.mem_cons_self _ _)
        have hpnorm : normalize p = p := hsnorm p (Multiset.mem_cons_self _ _)
        have hs' : ∀ r ∈ s, Irreducible r := fun r hr => hs r (Multiset.mem_cons_of_mem hr)
        have hsnorm' : ∀ r ∈ s, normalize r = r := fun r hr => hsnorm r (Multiset.mem_cons_of_mem hr)
        have hRp :
            (p ^ 2) • (((s.prod : Poly) ^ 2) • A) = R.transpose * R := by
          simpa [Multiset.prod_cons, pow_two, smul_smul, mul_assoc, mul_left_comm, mul_comm] using hR
        by_cases hroot : ∃ a : ℝ, p.IsRoot a
        · rcases hroot with ⟨a, ha⟩
          rcases polynomial_square_factor_descent_of_irreducible_scaled_square_of_isRoot
              hp ha (((s.prod : Poly) ^ 2) • A) hRp with ⟨U, hU⟩
          exact ih hs' hsnorm' (by simpa using hU)
        · have hnoroot : ∀ a : ℝ, ¬ p.IsRoot a := by
            intro a ha
            exact hroot ⟨a, ha⟩
          rcases exists_bezout_sq_add_sq_of_irreducible_of_normalized_of_forall_not_isRoot
              hp hpnorm hnoroot with
            ⟨a, b, _u, _v, hpab, _hbezout⟩
          rcases polynomial_square_factor_descent_of_normalized_irreducible_sqAddSq_scaled_square
              hp hpnorm hnoroot hpab (((s.prod : Poly) ^ 2) • A) hRp with ⟨U, hU⟩
          exact ih hs' hsnorm' (by simpa using hU)
  have hsirr : ∀ p ∈ UniqueFactorizationMonoid.normalizedFactors q, Irreducible p :=
    fun p hp => irreducible_of_mem_normalizedFactors_poly hp
  have hsnorm : ∀ p ∈ UniqueFactorizationMonoid.normalizedFactors q, normalize p = p :=
    fun p hp => UniqueFactorizationMonoid.normalize_normalized_factor p hp
  have hT'' :
      (((UniqueFactorizationMonoid.normalizedFactors q).prod : Poly) ^ 2) • A =
        T'.transpose * T' := by
    simpa [prod_normalizedFactors_poly hq] using hT'
  exact hmain (UniqueFactorizationMonoid.normalizedFactors q) hsirr hsnorm hT''

end MatrixSOS
