/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import MatrixSOS.Proof.NoRealRootDescent.ComplexRoots.RealImag
import MatrixSOS.Proof.NoRealRootDescent.Parity.Statements
import MatrixSOS.PolyMatrix

/-!
# Paired real and imaginary blocks in complex-root descent
-/

open Polynomial
open scoped Matrix

noncomputable section

namespace MatrixSOS
def pairIndexEmbedding {r m : ℕ} (h : r ≤ m) :
    ((Unit ⊕ Unit) × Fin r) ↪ ((Unit ⊕ Unit) × Fin m) where
  toFun x := (x.1, Fin.castLE h x.2)
  inj' := by
    intro x y hxy
    apply Prod.ext
    · simpa using congrArg Prod.fst hxy
    · apply Fin.ext
      simpa using congrArg Fin.val (congrArg Prod.snd hxy)

@[simp] theorem pairIndexEmbedding_apply
    {r m : ℕ}
    {h : r ≤ m}
    (x : ((Unit ⊕ Unit) × Fin r)) :
    pairIndexEmbedding h x = (x.1, Fin.castLE h x.2) := rfl

@[simp] theorem pairIndexEmbedding_apply_fst
    {r m : ℕ}
    {h : r ≤ m}
    (s : Unit ⊕ Unit)
    (t : Fin r) :
    pairIndexEmbedding h (s, t) = (s, Fin.castLE h t) := rfl

theorem exists_orthonormalBasis_extending_complexPairRealImagEuclideanFamily_even
    {m r : ℕ}
    (w : Fin r → EuclideanSpace ℂ (((Unit ⊕ Unit) × Fin m)))
    (hpair : Orthonormal ℝ (complexPairRealImagEuclideanFamily w))
    (hrle : r ≤ m) :
    ∃ b : OrthonormalBasis (((Unit ⊕ Unit) × Fin m)) ℝ
        (EuclideanSpace ℝ (((Unit ⊕ Unit) × Fin m))),
      ∀ s (t : Fin r), b (s, Fin.castLE hrle t) = complexPairRealImagEuclideanFamily w (s, t) := by
  let n := ((Unit ⊕ Unit) × Fin m)
  let e : ((Unit ⊕ Unit) × Fin r) ↪ n := pairIndexEmbedding hrle
  let v : n → EuclideanSpace ℝ n := Function.extend e (complexPairRealImagEuclideanFamily w) 0
  have hv :
      Orthonormal ℝ ((Set.range e).domRestrict v) := by
    rw [orthonormal_iff_ite]
    intro i j
    rcases i with ⟨i, hi⟩
    rcases j with ⟨j, hj⟩
    rcases hi with ⟨a, rfl⟩
    rcases hj with ⟨b, rfl⟩
    have hsub :
        (⟨e a, ⟨a, rfl⟩⟩ : Set.range e) = ⟨e b, ⟨b, rfl⟩⟩ ↔ a = b := by
      constructor
      · intro h
        exact e.injective (Subtype.ext_iff.mp h)
      · intro h
        cases h
        rfl
    simpa only [Set.domRestrict_apply, v, e.injective.extend_apply, hsub] using
      (orthonormal_iff_ite.mp hpair a b)
  have hcard : Module.finrank ℝ (EuclideanSpace ℝ n) = Fintype.card n := by
    exact finrank_euclideanSpace
  obtain ⟨b, hb⟩ :=
    hv.exists_orthonormalBasis_extension_of_card_eq (ι := n) (v := v) (s := Set.range e) hcard
  refine ⟨b, ?_⟩
  intro s t
  have hmem : (s, Fin.castLE hrle t) ∈ Set.range e := by
    refine ⟨(s, t), ?_⟩
    rfl
  calc
    b (s, Fin.castLE hrle t) = v (s, Fin.castLE hrle t) := hb _ hmem
    _ = complexPairRealImagEuclideanFamily w (s, t) := by
      rw [show (s, Fin.castLE hrle t) = e (s, t) by
            rfl]
      exact e.injective.extend_apply _ _ _

theorem orthogonal_to_complexPairRealImagEuclideanFamily_of_not_mem_range_even
    {m r : ℕ}
    {hrle : r ≤ m}
    {w : Fin r → EuclideanSpace ℂ (((Unit ⊕ Unit) × Fin m))}
    {b : OrthonormalBasis (((Unit ⊕ Unit) × Fin m)) ℝ
        (EuclideanSpace ℝ (((Unit ⊕ Unit) × Fin m)))}
    (hb : ∀ s (t : Fin r), b (s, Fin.castLE hrle t) = complexPairRealImagEuclideanFamily w (s, t))
    {i : ((Unit ⊕ Unit) × Fin m)}
    (hi : i ∉ Set.range (pairIndexEmbedding hrle)) :
    ∀ u : Fin r,
      b i ⬝ᵥ complexPairRealImagEuclideanFamily w (Sum.inl (), u) = 0 ∧
        b i ⬝ᵥ complexPairRealImagEuclideanFamily w (Sum.inr (), u) = 0 := by
  intro u
  have hneq_re : i ≠ pairIndexEmbedding hrle (Sum.inl (), u) := by
    intro hEq
    exact hi ⟨(Sum.inl (), u), hEq.symm⟩
  have hneq_im : i ≠ pairIndexEmbedding hrle (Sum.inr (), u) := by
    intro hEq
    exact hi ⟨(Sum.inr (), u), hEq.symm⟩
  have hneq_re' : i ≠ (Sum.inl (), Fin.castLE hrle u) := by
    simpa [pairIndexEmbedding_apply_fst] using hneq_re
  have hneq_im' : i ≠ (Sum.inr (), Fin.castLE hrle u) := by
    simpa [pairIndexEmbedding_apply_fst] using hneq_im
  constructor
  · have horth :
        b i ⬝ᵥ b (pairIndexEmbedding hrle (Sum.inl (), u)) = 0 := by
      have hinner : inner ℝ (b i) (b (pairIndexEmbedding hrle (Sum.inl (), u))) = 0 := by
        change inner ℝ (b i) (b (Sum.inl (), Fin.castLE hrle u)) = 0
        have hinner' := by
          simpa [pairIndexEmbedding_apply_fst] using
            (orthonormal_iff_ite.mp b.orthonormal i (pairIndexEmbedding hrle (Sum.inl (), u)))
        exact hinner'.trans (ite_eq_right hneq_re')
      have hinner' : inner ℝ (b (pairIndexEmbedding hrle (Sum.inl (), u))) (b i) = 0 := by
        simpa [real_inner_comm] using hinner
      change inner ℝ (b (pairIndexEmbedding hrle (Sum.inl (), u))) (b i) = 0
      exact hinner'
    rw [pairIndexEmbedding_apply_fst] at horth
    rw [hb (Sum.inl ()) u] at horth
    exact horth
  · have horth :
        b i ⬝ᵥ b (pairIndexEmbedding hrle (Sum.inr (), u)) = 0 := by
      have hinner : inner ℝ (b i) (b (pairIndexEmbedding hrle (Sum.inr (), u))) = 0 := by
        change inner ℝ (b i) (b (Sum.inr (), Fin.castLE hrle u)) = 0
        have hinner' := by
          simpa [pairIndexEmbedding_apply_fst] using
            (orthonormal_iff_ite.mp b.orthonormal i (pairIndexEmbedding hrle (Sum.inr (), u)))
        exact hinner'.trans (ite_eq_right hneq_im')
      have hinner' : inner ℝ (b (pairIndexEmbedding hrle (Sum.inr (), u))) (b i) = 0 := by
        simpa [real_inner_comm] using hinner
      change inner ℝ (b (pairIndexEmbedding hrle (Sum.inr (), u))) (b i) = 0
      exact hinner'
    rw [pairIndexEmbedding_apply_fst] at horth
    rw [hb (Sum.inr ()) u] at horth
    exact horth

theorem noRealRootStepCancellationComplexIsotropicRealPairBlockEvenStatement_theorem :
    NoRealRootStepCancellationComplexIsotropicRealPairBlockEvenStatement := by
  intro m κ Q hQ
  let n := ((Unit ⊕ Unit) × Fin m)
  let W : Submodule ℂ (EuclideanSpace ℂ n) :=
    Submodule.span ℂ (Set.range fun j => WithLp.toLp 2 (Q.col j))
  let r : ℕ := Module.finrank ℂ W
  let w : Fin r → EuclideanSpace ℂ n :=
    fun i => (((stdOrthonormalBasis ℂ W i : W) : EuclideanSpace ℂ n))
  have hpair :
      Orthonormal ℝ (complexPairRealImagEuclideanFamily w) := by
    let hpair0 :=
      orthonormal_complexPairRealImagEuclideanFamily_stdOrthonormalBasis_span_toLp_cols_of_transpose_mul_eq_zero
        Q hQ
    dsimp only at hpair0
    change Orthonormal ℝ (complexPairRealImagEuclideanFamily w) at hpair0
    exact hpair0
  have hrle : r ≤ m := by
    simpa [n, W, r] using finrank_span_toLp_cols_le_even_pairs_of_transpose_mul_eq_zero Q hQ
  obtain ⟨b, hb⟩ :=
    exists_orthonormalBasis_extending_complexPairRealImagEuclideanFamily_even w hpair hrle
  let O : Matrix n n ℝ := ((EuclideanSpace.basisFun n ℝ).toBasis.toMatrix b).transpose
  refine ⟨O, ?_, ?_, ?_⟩
  · have hOrth :
        ((EuclideanSpace.basisFun n ℝ).toBasis.toMatrix b) ∈ Matrix.orthogonalGroup n ℝ :=
      (EuclideanSpace.basisFun n ℝ).toMatrix_orthonormalBasis_mem_orthogonal b
    have hMMt :
        ((EuclideanSpace.basisFun n ℝ).toBasis.toMatrix b) *
            ((EuclideanSpace.basisFun n ℝ).toBasis.toMatrix b).transpose =
          1 := (Matrix.mem_orthogonalGroup_iff (n := n) (R := ℝ)).1 hOrth
    simpa [O] using hMMt
  · have hOrth :
        ((EuclideanSpace.basisFun n ℝ).toBasis.toMatrix b) ∈ Matrix.orthogonalGroup n ℝ :=
      (EuclideanSpace.basisFun n ℝ).toMatrix_orthonormalBasis_mem_orthogonal b
    have hMtM :
        ((EuclideanSpace.basisFun n ℝ).toBasis.toMatrix b).transpose *
            ((EuclideanSpace.basisFun n ℝ).toBasis.toMatrix b) =
          1 := (Matrix.mem_orthogonalGroup_iff' (n := n) (R := ℝ)).1 hOrth
    simpa [O] using hMtM
  · intro t j
    have hspanW : Submodule.span ℂ (Set.range w) = W := by
      have hspanTop :
          Submodule.span ℂ
              (Set.range fun i : Fin r => ((stdOrthonormalBasis ℂ W i : W) : W)) =
            ⊤ := by
        simpa [r] using (stdOrthonormalBasis ℂ W).toBasis.span_eq
      calc
        Submodule.span ℂ (Set.range w)
            = Submodule.map W.subtype (Submodule.span ℂ
                (Set.range fun i : Fin r => ((stdOrthonormalBasis ℂ W i : W) : W))) := by
                  rw [Submodule.map_span]
                  congr 1
                  ext x
                  constructor
                  · rintro ⟨i, rfl⟩
                    exact ⟨((stdOrthonormalBasis ℂ W i : W) : W), ⟨i, rfl⟩, rfl⟩
                  · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
                    exact ⟨i, rfl⟩
        _ = W := by
              rw [hspanTop, Submodule.map_top]
              exact Submodule.range_subtype W
    have hcolW : WithLp.toLp 2 (Q.col j) ∈ W := by
      exact Submodule.subset_span ⟨j, rfl⟩
    have hrow_re :
        ((O.map (algebraMap ℝ ℂ)) * Q) (Sum.inl (), t) j =
          (fun k => ((b (Sum.inl (), t)) k : ℂ)) ⬝ᵥ Q.col j := by
      change
        ((((EuclideanSpace.basisFun n ℝ).toBasis.toMatrix b).transpose.map
              (algebraMap ℝ ℂ)) * Q) (Sum.inl (), t) j =
          (fun k => ((b (Sum.inl (), t)) k : ℂ)) ⬝ᵥ Q.col j
      exact transpose_basisFun_toMatrix_mul_apply_eq_dotProduct (b := b) (Q := Q)
        (i := (Sum.inl (), t)) (j := j)
    have hrow_im :
        ((O.map (algebraMap ℝ ℂ)) * Q) (Sum.inr (), t) j =
          (fun k => ((b (Sum.inr (), t)) k : ℂ)) ⬝ᵥ Q.col j := by
      change
        ((((EuclideanSpace.basisFun n ℝ).toBasis.toMatrix b).transpose.map
              (algebraMap ℝ ℂ)) * Q) (Sum.inr (), t) j =
          (fun k => ((b (Sum.inr (), t)) k : ℂ)) ⬝ᵥ Q.col j
      exact transpose_basisFun_toMatrix_mul_apply_eq_dotProduct (b := b) (Q := Q)
        (i := (Sum.inr (), t)) (j := j)
    by_cases ht : (t : ℕ) < r
    · let u : Fin r := ⟨t, ht⟩
      have hwu :
          WithLp.ofLp (w u) ⬝ᵥ Q.col j = 0 := by
        have huW : w u ∈ W := by
          change (((stdOrthonormalBasis ℂ W u : W) : EuclideanSpace ℂ n)) ∈ W
          exact (stdOrthonormalBasis ℂ W u).property
        exact dotProduct_eq_zero_of_mem_span_toLp_cols_of_transpose_mul_eq_zero Q hQ huW hcolW
      have hcast : Fin.castLE hrle u = t := by
        apply Fin.ext
        simp [u]
      rw [hrow_re, hrow_im]
      rw [show b (Sum.inl (), t) = complexPairRealImagEuclideanFamily w (Sum.inl (), u) by
            rw [← hcast]
            exact hb _ u]
      rw [show b (Sum.inr (), t) = complexPairRealImagEuclideanFamily w (Sum.inr (), u) by
            rw [← hcast]
            exact hb _ u]
      have hpairdot := complexPairRealImagEuclideanFamily_dot_add_I w u (Q.col j)
      rw [hwu, mul_zero] at hpairdot
      exact hpairdot
    · have hi_re : (Sum.inl (), t) ∉ Set.range (pairIndexEmbedding hrle) := by
        intro hmem
        rcases hmem with ⟨⟨s, u⟩, hu⟩
        have hEq : Fin.castLE hrle u = t := by
            simpa [pairIndexEmbedding_apply_fst] using congrArg Prod.snd hu
        have hu_lt : ((Fin.castLE hrle u : Fin m) : ℕ) < r := by
          change (u : ℕ) < r
          exact u.2
        have hEqVal : (Fin.castLE hrle u : ℕ) = (t : ℕ) := by
          exact congrArg Fin.val hEq
        exact ht (by
          rw [← hEqVal]
          exact hu_lt)
      have hi_im : (Sum.inr (), t) ∉ Set.range (pairIndexEmbedding hrle) := by
        intro hmem
        rcases hmem with ⟨⟨s, u⟩, hu⟩
        have hEq : Fin.castLE hrle u = t := by
            simpa [pairIndexEmbedding_apply_fst] using congrArg Prod.snd hu
        have hu_lt : ((Fin.castLE hrle u : Fin m) : ℕ) < r := by
          change (u : ℕ) < r
          exact u.2
        have hEqVal : (Fin.castLE hrle u : ℕ) = (t : ℕ) := by
          exact congrArg Fin.val hEq
        exact ht (by
          rw [← hEqVal]
          exact hu_lt)
      have hcolSpan : WithLp.toLp 2 (Q.col j) ∈ Submodule.span ℂ (Set.range w) := by
        rw [hspanW]
        exact hcolW
      have hReZero :
          (fun k => ((b (Sum.inl (), t)) k : ℂ)) ⬝ᵥ Q.col j = 0 := by
        exact dotProduct_eq_zero_of_mem_span_of_orthogonal_to_pairFamily
          (u := b (Sum.inl (), t)) (w := w)
          (orthogonal_to_complexPairRealImagEuclideanFamily_of_not_mem_range_even hb hi_re) hcolSpan
      have hImZero :
          (fun k => ((b (Sum.inr (), t)) k : ℂ)) ⬝ᵥ Q.col j = 0 := by
        exact dotProduct_eq_zero_of_mem_span_of_orthogonal_to_pairFamily
          (u := b (Sum.inr (), t)) (w := w)
          (orthogonal_to_complexPairRealImagEuclideanFamily_of_not_mem_range_even hb hi_im) hcolSpan
      rw [hrow_re, hrow_im, hReZero, hImZero]
      simp

def oddPairIndexEmbedding {r m : ℕ} (h : r ≤ m) :
    ((Unit ⊕ Unit) × Fin r) ↪ (((Unit ⊕ Unit) × Fin m) ⊕ Unit) where
  toFun x := Sum.inl (x.1, Fin.castLE h x.2)
  inj' := by
    intro x y hxy
    have hxy' : (x.1, Fin.castLE h x.2) = (y.1, Fin.castLE h y.2) := by
      exact Sum.inl.inj hxy
    apply Prod.ext
    · simpa using congrArg Prod.fst hxy'
    · apply Fin.ext
      simpa using congrArg Fin.val (congrArg Prod.snd hxy')

@[simp] theorem oddPairIndexEmbedding_apply
    {r m : ℕ}
    {h : r ≤ m}
    (x : ((Unit ⊕ Unit) × Fin r)) :
    oddPairIndexEmbedding h x = Sum.inl (x.1, Fin.castLE h x.2) := rfl

@[simp] theorem oddPairIndexEmbedding_apply_fst
    {r m : ℕ}
    {h : r ≤ m}
    (s : Unit ⊕ Unit)
    (t : Fin r) :
    oddPairIndexEmbedding h (s, t) = Sum.inl (s, Fin.castLE h t) := rfl

theorem exists_orthonormalBasis_extending_complexPairRealImagEuclideanFamily_odd
    {m r : ℕ}
    (w : Fin r → EuclideanSpace ℂ ((((Unit ⊕ Unit) × Fin m) ⊕ Unit)))
    (hpair : Orthonormal ℝ (complexPairRealImagEuclideanFamily w))
    (hrle : r ≤ m) :
    ∃ b : OrthonormalBasis ((((Unit ⊕ Unit) × Fin m) ⊕ Unit)) ℝ
        (EuclideanSpace ℝ ((((Unit ⊕ Unit) × Fin m) ⊕ Unit))),
      ∀ s (t : Fin r),
        b (Sum.inl (s, Fin.castLE hrle t)) = complexPairRealImagEuclideanFamily w (s, t) := by
  let n := (((Unit ⊕ Unit) × Fin m) ⊕ Unit)
  let e : ((Unit ⊕ Unit) × Fin r) ↪ n := oddPairIndexEmbedding hrle
  let v : n → EuclideanSpace ℝ n := Function.extend e (complexPairRealImagEuclideanFamily w) 0
  have hv :
      Orthonormal ℝ ((Set.range e).domRestrict v) := by
    rw [orthonormal_iff_ite]
    intro i j
    rcases i with ⟨i, hi⟩
    rcases j with ⟨j, hj⟩
    rcases hi with ⟨a, rfl⟩
    rcases hj with ⟨b, rfl⟩
    have hsub :
        (⟨e a, ⟨a, rfl⟩⟩ : Set.range e) = ⟨e b, ⟨b, rfl⟩⟩ ↔ a = b := by
      constructor
      · intro h
        exact e.injective (Subtype.ext_iff.mp h)
      · intro h
        cases h
        rfl
    simpa only [Set.domRestrict_apply, v, e.injective.extend_apply, hsub] using
      (orthonormal_iff_ite.mp hpair a b)
  have hcard : Module.finrank ℝ (EuclideanSpace ℝ n) = Fintype.card n := by
    exact finrank_euclideanSpace
  obtain ⟨b, hb⟩ :=
    hv.exists_orthonormalBasis_extension_of_card_eq (ι := n) (v := v) (s := Set.range e) hcard
  refine ⟨b, ?_⟩
  intro s t
  have hmem : Sum.inl (s, Fin.castLE hrle t) ∈ Set.range e := by
    refine ⟨(s, t), ?_⟩
    rfl
  calc
    b (Sum.inl (s, Fin.castLE hrle t)) = v (Sum.inl (s, Fin.castLE hrle t)) := hb _ hmem
    _ = complexPairRealImagEuclideanFamily w (s, t) := by
      rw [show Sum.inl (s, Fin.castLE hrle t) = e (s, t) by
            rfl]
      exact e.injective.extend_apply _ _ _

theorem orthogonal_to_complexPairRealImagEuclideanFamily_of_not_mem_range_odd
    {m r : ℕ}
    {hrle : r ≤ m}
    {w : Fin r → EuclideanSpace ℂ ((((Unit ⊕ Unit) × Fin m) ⊕ Unit))}
    {b : OrthonormalBasis ((((Unit ⊕ Unit) × Fin m) ⊕ Unit)) ℝ
        (EuclideanSpace ℝ ((((Unit ⊕ Unit) × Fin m) ⊕ Unit)))}
    (hb : ∀ s (t : Fin r),
      b (Sum.inl (s, Fin.castLE hrle t)) = complexPairRealImagEuclideanFamily w (s, t))
    {i : (((Unit ⊕ Unit) × Fin m) ⊕ Unit)}
    (hi : i ∉ Set.range (oddPairIndexEmbedding hrle)) :
    ∀ u : Fin r,
      b i ⬝ᵥ complexPairRealImagEuclideanFamily w (Sum.inl (), u) = 0 ∧
        b i ⬝ᵥ complexPairRealImagEuclideanFamily w (Sum.inr (), u) = 0 := by
  intro u
  have hneq_re : i ≠ oddPairIndexEmbedding hrle (Sum.inl (), u) := by
    intro hEq
    exact hi ⟨(Sum.inl (), u), hEq.symm⟩
  have hneq_im : i ≠ oddPairIndexEmbedding hrle (Sum.inr (), u) := by
    intro hEq
    exact hi ⟨(Sum.inr (), u), hEq.symm⟩
  have hneq_re' : i ≠ Sum.inl (Sum.inl (), Fin.castLE hrle u) := by
    simpa [oddPairIndexEmbedding_apply_fst] using hneq_re
  have hneq_im' : i ≠ Sum.inl (Sum.inr (), Fin.castLE hrle u) := by
    simpa [oddPairIndexEmbedding_apply_fst] using hneq_im
  constructor
  · have horth :
        b i ⬝ᵥ b (oddPairIndexEmbedding hrle (Sum.inl (), u)) = 0 := by
      have hinner : inner ℝ (b i) (b (oddPairIndexEmbedding hrle (Sum.inl (), u))) = 0 := by
        change inner ℝ (b i) (b (Sum.inl (Sum.inl (), Fin.castLE hrle u))) = 0
        have hinner' := by
          simpa [oddPairIndexEmbedding_apply_fst] using
            (orthonormal_iff_ite.mp b.orthonormal i (oddPairIndexEmbedding hrle (Sum.inl (), u)))
        exact hinner'.trans (ite_eq_right hneq_re')
      have hinner' : inner ℝ (b (oddPairIndexEmbedding hrle (Sum.inl (), u))) (b i) = 0 := by
        simpa [real_inner_comm] using hinner
      change inner ℝ (b (oddPairIndexEmbedding hrle (Sum.inl (), u))) (b i) = 0
      exact hinner'
    rw [oddPairIndexEmbedding_apply_fst] at horth
    rw [hb (Sum.inl ()) u] at horth
    exact horth
  · have horth :
        b i ⬝ᵥ b (oddPairIndexEmbedding hrle (Sum.inr (), u)) = 0 := by
      have hinner : inner ℝ (b i) (b (oddPairIndexEmbedding hrle (Sum.inr (), u))) = 0 := by
        change inner ℝ (b i) (b (Sum.inl (Sum.inr (), Fin.castLE hrle u))) = 0
        have hinner' := by
          simpa [oddPairIndexEmbedding_apply_fst] using
            (orthonormal_iff_ite.mp b.orthonormal i (oddPairIndexEmbedding hrle (Sum.inr (), u)))
        exact hinner'.trans (ite_eq_right hneq_im')
      have hinner' : inner ℝ (b (oddPairIndexEmbedding hrle (Sum.inr (), u))) (b i) = 0 := by
        simpa [real_inner_comm] using hinner
      change inner ℝ (b (oddPairIndexEmbedding hrle (Sum.inr (), u))) (b i) = 0
      exact hinner'
    rw [oddPairIndexEmbedding_apply_fst] at horth
    rw [hb (Sum.inr ()) u] at horth
    exact horth

theorem noRealRootStepCancellationComplexIsotropicRealPairBlockOddStatement_theorem :
    NoRealRootStepCancellationComplexIsotropicRealPairBlockOddStatement := by
  intro m κ Q hQ
  let n := (((Unit ⊕ Unit) × Fin m) ⊕ Unit)
  let W : Submodule ℂ (EuclideanSpace ℂ n) :=
    Submodule.span ℂ (Set.range fun j => WithLp.toLp 2 (Q.col j))
  let r : ℕ := Module.finrank ℂ W
  let w : Fin r → EuclideanSpace ℂ n :=
    fun i => (((stdOrthonormalBasis ℂ W i : W) : EuclideanSpace ℂ n))
  have hpair :
      Orthonormal ℝ (complexPairRealImagEuclideanFamily w) := by
    let hpair0 :=
      orthonormal_complexPairRealImagEuclideanFamily_stdOrthonormalBasis_span_toLp_cols_of_transpose_mul_eq_zero
        Q hQ
    dsimp only at hpair0
    change Orthonormal ℝ (complexPairRealImagEuclideanFamily w) at hpair0
    exact hpair0
  have hrle : r ≤ m := by
    simpa [n, W, r] using finrank_span_toLp_cols_le_odd_pairs_of_transpose_mul_eq_zero Q hQ
  obtain ⟨b, hb⟩ :=
    exists_orthonormalBasis_extending_complexPairRealImagEuclideanFamily_odd w hpair hrle
  let O : Matrix n n ℝ := ((EuclideanSpace.basisFun n ℝ).toBasis.toMatrix b).transpose
  have hspanW : Submodule.span ℂ (Set.range w) = W := by
    have hspanTop :
        Submodule.span ℂ
            (Set.range fun i : Fin r => ((stdOrthonormalBasis ℂ W i : W) : W)) =
          ⊤ := by
      simpa [r] using (stdOrthonormalBasis ℂ W).toBasis.span_eq
    calc
      Submodule.span ℂ (Set.range w)
          = Submodule.map W.subtype (Submodule.span ℂ
              (Set.range fun i : Fin r => ((stdOrthonormalBasis ℂ W i : W) : W))) := by
                rw [Submodule.map_span]
                congr 1
                ext x
                constructor
                · rintro ⟨i, rfl⟩
                  exact ⟨((stdOrthonormalBasis ℂ W i : W) : W), ⟨i, rfl⟩, rfl⟩
                · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
                  exact ⟨i, rfl⟩
      _ = W := by
            rw [hspanTop, Submodule.map_top]
            exact Submodule.range_subtype W
  refine ⟨O, ?_, ?_, ?_, ?_⟩
  · have hOrth :
        ((EuclideanSpace.basisFun n ℝ).toBasis.toMatrix b) ∈ Matrix.orthogonalGroup n ℝ :=
      (EuclideanSpace.basisFun n ℝ).toMatrix_orthonormalBasis_mem_orthogonal b
    have hMMt :
        ((EuclideanSpace.basisFun n ℝ).toBasis.toMatrix b) *
            ((EuclideanSpace.basisFun n ℝ).toBasis.toMatrix b).transpose =
          1 := (Matrix.mem_orthogonalGroup_iff (n := n) (R := ℝ)).1 hOrth
    simpa [O] using hMMt
  · have hOrth :
        ((EuclideanSpace.basisFun n ℝ).toBasis.toMatrix b) ∈ Matrix.orthogonalGroup n ℝ :=
      (EuclideanSpace.basisFun n ℝ).toMatrix_orthonormalBasis_mem_orthogonal b
    have hMtM :
        ((EuclideanSpace.basisFun n ℝ).toBasis.toMatrix b).transpose *
            ((EuclideanSpace.basisFun n ℝ).toBasis.toMatrix b) =
          1 := (Matrix.mem_orthogonalGroup_iff' (n := n) (R := ℝ)).1 hOrth
    simpa [O] using hMtM
  · intro t j
    have hcolW : WithLp.toLp 2 (Q.col j) ∈ W := by
      exact Submodule.subset_span ⟨j, rfl⟩
    have hcolSpan : WithLp.toLp 2 (Q.col j) ∈ Submodule.span ℂ (Set.range w) := by
      rw [hspanW]
      exact hcolW
    have hrow_re :
        ((O.map (algebraMap ℝ ℂ)) * Q) (Sum.inl (Sum.inl (), t)) j =
          (fun k => ((b (Sum.inl (Sum.inl (), t))) k : ℂ)) ⬝ᵥ Q.col j := by
      change
        ((((EuclideanSpace.basisFun n ℝ).toBasis.toMatrix b).transpose.map
              (algebraMap ℝ ℂ)) * Q) (Sum.inl (Sum.inl (), t)) j =
          (fun k => ((b (Sum.inl (Sum.inl (), t))) k : ℂ)) ⬝ᵥ Q.col j
      exact transpose_basisFun_toMatrix_mul_apply_eq_dotProduct (b := b) (Q := Q)
        (i := Sum.inl (Sum.inl (), t)) (j := j)
    have hrow_im :
        ((O.map (algebraMap ℝ ℂ)) * Q) (Sum.inl (Sum.inr (), t)) j =
          (fun k => ((b (Sum.inl (Sum.inr (), t))) k : ℂ)) ⬝ᵥ Q.col j := by
      change
        ((((EuclideanSpace.basisFun n ℝ).toBasis.toMatrix b).transpose.map
              (algebraMap ℝ ℂ)) * Q) (Sum.inl (Sum.inr (), t)) j =
          (fun k => ((b (Sum.inl (Sum.inr (), t))) k : ℂ)) ⬝ᵥ Q.col j
      exact transpose_basisFun_toMatrix_mul_apply_eq_dotProduct (b := b) (Q := Q)
        (i := Sum.inl (Sum.inr (), t)) (j := j)
    by_cases ht : (t : ℕ) < r
    · let u : Fin r := ⟨t, ht⟩
      have hwu :
          WithLp.ofLp (w u) ⬝ᵥ Q.col j = 0 := by
        have huW : w u ∈ W := by
          change (((stdOrthonormalBasis ℂ W u : W) : EuclideanSpace ℂ n)) ∈ W
          exact (stdOrthonormalBasis ℂ W u).property
        exact dotProduct_eq_zero_of_mem_span_toLp_cols_of_transpose_mul_eq_zero Q hQ huW hcolW
      have hcast : Fin.castLE hrle u = t := by
        apply Fin.ext
        simp [u]
      rw [hrow_re, hrow_im]
      rw [show b (Sum.inl (Sum.inl (), t)) = complexPairRealImagEuclideanFamily w (Sum.inl (), u) by
            rw [← hcast]
            exact hb _ u]
      rw [show b (Sum.inl (Sum.inr (), t)) = complexPairRealImagEuclideanFamily w (Sum.inr (), u) by
            rw [← hcast]
            exact hb _ u]
      have hpairdot := complexPairRealImagEuclideanFamily_dot_add_I w u (Q.col j)
      rw [hwu, mul_zero] at hpairdot
      exact hpairdot
    · have hi_re : Sum.inl (Sum.inl (), t) ∉ Set.range (oddPairIndexEmbedding hrle) := by
        intro hmem
        rcases hmem with ⟨⟨s, u⟩, hu⟩
        have hEq : Fin.castLE hrle u = t := by
          cases hu
          rfl
        have hu_lt : ((Fin.castLE hrle u : Fin m) : ℕ) < r := by
          change (u : ℕ) < r
          exact u.2
        have hEqVal : (Fin.castLE hrle u : ℕ) = (t : ℕ) := by
          exact congrArg Fin.val hEq
        exact ht (by
          rw [← hEqVal]
          exact hu_lt)
      have hi_im : Sum.inl (Sum.inr (), t) ∉ Set.range (oddPairIndexEmbedding hrle) := by
        intro hmem
        rcases hmem with ⟨⟨s, u⟩, hu⟩
        have hEq : Fin.castLE hrle u = t := by
          cases hu
          rfl
        have hu_lt : ((Fin.castLE hrle u : Fin m) : ℕ) < r := by
          change (u : ℕ) < r
          exact u.2
        have hEqVal : (Fin.castLE hrle u : ℕ) = (t : ℕ) := by
          exact congrArg Fin.val hEq
        exact ht (by
          rw [← hEqVal]
          exact hu_lt)
      have hReZero :
          (fun k => ((b (Sum.inl (Sum.inl (), t))) k : ℂ)) ⬝ᵥ Q.col j = 0 := by
        exact dotProduct_eq_zero_of_mem_span_of_orthogonal_to_pairFamily
          (u := b (Sum.inl (Sum.inl (), t))) (w := w)
          (orthogonal_to_complexPairRealImagEuclideanFamily_of_not_mem_range_odd hb hi_re) hcolSpan
      have hImZero :
          (fun k => ((b (Sum.inl (Sum.inr (), t))) k : ℂ)) ⬝ᵥ Q.col j = 0 := by
        exact dotProduct_eq_zero_of_mem_span_of_orthogonal_to_pairFamily
          (u := b (Sum.inl (Sum.inr (), t))) (w := w)
          (orthogonal_to_complexPairRealImagEuclideanFamily_of_not_mem_range_odd hb hi_im) hcolSpan
      rw [hrow_re, hrow_im, hReZero, hImZero]
      simp
  · intro j
    have hcolW : WithLp.toLp 2 (Q.col j) ∈ W := by
      exact Submodule.subset_span ⟨j, rfl⟩
    have hcolSpan : WithLp.toLp 2 (Q.col j) ∈ Submodule.span ℂ (Set.range w) := by
      rw [hspanW]
      exact hcolW
    have hrow_last :
        ((O.map (algebraMap ℝ ℂ)) * Q) (Sum.inr ()) j =
          (fun k => ((b (Sum.inr ())) k : ℂ)) ⬝ᵥ Q.col j := by
      change
        ((((EuclideanSpace.basisFun n ℝ).toBasis.toMatrix b).transpose.map
              (algebraMap ℝ ℂ)) * Q) (Sum.inr ()) j =
          (fun k => ((b (Sum.inr ())) k : ℂ)) ⬝ᵥ Q.col j
      exact transpose_basisFun_toMatrix_mul_apply_eq_dotProduct (b := b) (Q := Q)
        (i := Sum.inr ()) (j := j)
    have hi_last : Sum.inr () ∉ Set.range (oddPairIndexEmbedding hrle) := by
      intro hmem
      rcases hmem with ⟨⟨s, u⟩, hu⟩
      cases hu
    have hLastZero :
        (fun k => ((b (Sum.inr ())) k : ℂ)) ⬝ᵥ Q.col j = 0 := by
      exact dotProduct_eq_zero_of_mem_span_of_orthogonal_to_pairFamily
        (u := b (Sum.inr ())) (w := w)
        (orthogonal_to_complexPairRealImagEuclideanFamily_of_not_mem_range_odd hb hi_last) hcolSpan
    rw [hrow_last, hLastZero]

theorem noRealRootStepCancellationComplexIsotropicRealPairBlockParityStatement_theorem :
    NoRealRootStepCancellationComplexIsotropicRealPairBlockParityStatement :=
  ⟨noRealRootStepCancellationComplexIsotropicRealPairBlockEvenStatement_theorem,
    noRealRootStepCancellationComplexIsotropicRealPairBlockOddStatement_theorem⟩

@[simp] theorem mapEvalComplex_apply
    {ι κ : Type*}
    (z : ℂ)
    (A : Matrix ι κ Poly)
    (i : ι)
    (j : κ) :
    mapEvalComplex z A i j = eval₂ (algebraMap ℝ ℂ) z (A i j) := rfl

@[simp] theorem mapEvalComplex_transpose
    {ι κ : Type*}
    (z : ℂ)
    (A : Matrix ι κ Poly) :
    mapEvalComplex z A.transpose = (mapEvalComplex z A).transpose := by
  ext i j
  rfl

@[simp] theorem mapEvalComplex_mul
    {ι κ μ : Type*}
    [Fintype κ]
    (z : ℂ)
    (A : Matrix ι κ Poly)
    (B : Matrix κ μ Poly) :
    mapEvalComplex z (A * B) = mapEvalComplex z A * mapEvalComplex z B := by
  simpa [mapEvalComplex] using
    (Matrix.map_mul (f := Polynomial.eval₂RingHom (algebraMap ℝ ℂ) z) (L := A) (M := B))

@[simp] theorem mapEvalComplex_constPolyMat
    {ι κ : Type*}
    (z : ℂ)
    (A : Matrix ι κ ℝ) :
    mapEvalComplex z (constPolyMat A) = A.map (algebraMap ℝ ℂ) := by
  ext i j
  simp [mapEvalComplex, constPolyMat]

@[simp] theorem constPolyMat_one
    {ι : Type*}
    [DecidableEq ι] :
    constPolyMat (1 : Matrix ι ι ℝ) = (1 : Matrix ι ι Poly) := by
  ext i j
  by_cases h : i = j
  · subst h
    simp [constPolyMat]
  · simp [constPolyMat, h]

end MatrixSOS
