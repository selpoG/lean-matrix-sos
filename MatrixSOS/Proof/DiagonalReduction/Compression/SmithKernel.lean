/-
Copyright (c) 2026 selpo. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: selpo
-/

import MatrixSOS.Proof.DiagonalReduction.StdBasis
import Mathlib.LinearAlgebra.FreeModule.PID

/-!
# Kernel compression using Smith normal form
-/

open Matrix Polynomial
open scoped Matrix
noncomputable section

namespace MatrixSOS

theorem exists_smith_normal_form_for_submodule
    {m : ℕ}
    (K : Submodule Poly (V m)) :
    ∃ (n o : ℕ) (hno : n ≤ o)
      (bTop : Module.Basis (Fin o) Poly ↥(⊤ : Submodule Poly (V m)))
      (bKer : Module.Basis (Fin n) Poly ↥K)
      (a : Fin n → Poly),
      ∀ i : Fin n,
        (↑(bKer i) : V m) = a i • ((↑(bTop (Fin.castLE hno i)) : V m)) := by
  simpa [stdBasisV] using
    (Submodule.exists_smith_normal_form_of_le
      (b := stdBasisV m)
      (N := K)
      (O := (⊤ : Submodule Poly (V m)))
      (show K ≤ (⊤ : Submodule Poly (V m)) from by
        intro x hx
        simp))

theorem exists_smith_normal_form_for_ker
    {m : ℕ}
    {W : Type*}
    [AddCommGroup W] [Module Poly W] [Module.Free Poly W] [Module.Finite Poly W]
    (f : V m →ₗ[Poly] W) :
    ∃ (r o : ℕ) (hro : r ≤ o)
      (bTop : Module.Basis (Fin o) Poly ↥(⊤ : Submodule Poly (V m)))
      (bKer : Module.Basis (Fin r) Poly ↥(LinearMap.ker f))
      (a : Fin r → Poly),
      ∀ i : Fin r,
        (↑(bKer i) : V m) = a i • ((↑(bTop (Fin.castLE hro i)) : V m)) :=
  exists_smith_normal_form_for_submodule (LinearMap.ker f)

lemma smith_coeff_ne_zero
    {m n o : ℕ}
    {N : Submodule Poly (V m)}
    {hno : n ≤ o}
    {bTop : Module.Basis (Fin o) Poly ↥(⊤ : Submodule Poly (V m))}
    {bN : Module.Basis (Fin n) Poly ↥N}
    {a : Fin n → Poly}
    (hsmith :
      ∀ i : Fin n,
        (↑(bN i) : V m) = a i • ((↑(bTop (Fin.castLE hno i)) : V m))) :
    ∀ i : Fin n, a i ≠ 0 := by
  intro i hi
  have hzeroV : (↑(bN i) : V m) = 0 := by
    simpa [hi] using hsmith i
  have hzeroSub : (bN i : ↥N) = 0 := by
    apply Subtype.ext
    simpa using hzeroV
  exact bN.ne_zero i hzeroSub

lemma smith_prefix_mem_ker_of_linearMap
    {m k n o : ℕ}
    {f : V m →ₗ[Poly] V k}
    {hno : n ≤ o}
    {bTop : Module.Basis (Fin o) Poly ↥(⊤ : Submodule Poly (V m))}
    {bKer : Module.Basis (Fin n) Poly ↥(LinearMap.ker f)}
    {a : Fin n → Poly}
    (hsmith :
      ∀ i : Fin n,
        (↑(bKer i) : V m) = a i • ((↑(bTop (Fin.castLE hno i)) : V m))) :
    ∀ i : Fin n, ((↑(bTop (Fin.castLE hno i)) : V m)) ∈ LinearMap.ker f := by
  intro i
  refine LinearMap.mem_ker.2 ?_
  have hker : f (↑(bKer i) : V m) = 0 := (bKer i).2
  rw [hsmith i, map_smul] at hker
  funext j
  have hcoord : a i * f ((↑(bTop (Fin.castLE hno i)) : V m)) j = 0 := by
    simpa using congrArg (fun w => w j) hker
  have hai : a i ≠ 0 := smith_coeff_ne_zero hsmith i
  rcases mul_eq_zero.mp hcoord with hzero | hzero
  · exact (hai hzero).elim
  · exact hzero

end MatrixSOS
