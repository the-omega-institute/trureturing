/- GID: D5/S3/Combinatorics/Partitions/SpechtSchurPieri
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Partitions/SpechtSchurPieri
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Selected tableau and Schur suppliers for the ordinary Specht Frobenius comparison. -/

/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license. Authors: The Tau Ceti contributors.
Selected declarations from TauCeti 5a01f5fe3621126cccf9ba22e700493cbc7b7156.
Namespaces and root references adapted to the existing D5 source chain.
License, selection, consumers and retirement:
Library/FiniteGroups/tauceti2026spechtpolytabloids.md.
Unfinished escape audit: https://github.com/the-omega-institute/trureturing/issues/24542.
-/
import D5.S3.Combinatorics.Partitions.SpechtSchurBialternant
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.Order.Preorder.Finite

namespace D5.S3.Combinatorics.Partitions.SpechtPolytabloid
noncomputable section
open scoped BigOperators

namespace TauCeti

open Equiv Finset

variable {n : ℕ} {α : Type*} [Preorder α] [DecidableLE α] {β η : Fin n → α}

theorem sum_sign_filter_forall_le_of_antitone (hβ : Antitone β) (hη : Antitone η) :
    ∑ τ : Perm (Fin n) with (∀ j, β j ≤ η (τ j)), (Perm.sign τ : ℤ) =
      if ∀ i j, β j ≤ η i ↔ i ≤ j then 1 else 0 := by
  classical
  set M : Matrix (Fin n) (Fin n) ℤ := Matrix.of fun j i => if β j ≤ η i then 1 else 0 with hM

  have hdet : M.det = ∑ τ : Perm (Fin n) with (∀ j, β j ≤ η (τ j)), (Perm.sign τ : ℤ) := by
    rw [← M.det_transpose, Matrix.det_apply', Finset.sum_filter]
    refine Finset.sum_congr rfl fun τ _ => ?_
    have hprod : ∏ i, M.transpose (τ i) i = if ∀ j, β j ≤ η (τ j) then (1 : ℤ) else 0 := by
      simp [hM, Fintype.prod_boole]
    rw [hprod]
    split_ifs <;> simp
  rw [← hdet]
  split_ifs with h
  ·
    have hlow : M.IsLowerTriangular := by
      intro r c hrc
      have hne : ¬ β r ≤ η c := (h c r).not.mpr (not_le.mpr (OrderDual.toDual_lt_toDual.mp hrc))
      simp [hM, hne]
    rw [Matrix.det_of_isLowerTriangular M hlow]
    exact Finset.prod_eq_one fun j _ => by simp [hM, (h j j).mpr le_rfl]
  by_cases hempty : ∃ j, ∀ i, ¬ β j ≤ η i
  ·
    obtain ⟨j, hj⟩ := hempty
    exact Matrix.det_eq_zero_of_row_eq_zero j fun i => by simp [hM, hj i]

  simp only [not_exists, not_forall, not_not] at hempty
  set S : Fin n → Finset (Fin n) := fun j => univ.filter fun i => β j ≤ η i
  have hSne : ∀ j, (S j).Nonempty := fun j => by
    obtain ⟨i, hi⟩ := hempty j
    exact ⟨i, mem_filter.mpr ⟨mem_univ _, hi⟩⟩
  set c : Fin n → Fin n := fun j => (S j).max' (hSne j)
  have hmem : ∀ i j : Fin n, β j ≤ η i ↔ i ≤ c j := by
    refine fun i j => ⟨fun hij => (S j).le_max' i (mem_filter.mpr ⟨mem_univ _, hij⟩), fun hij => ?_⟩
    have hcj : β j ≤ η (c j) := (mem_filter.mp ((S j).max'_mem (hSne j))).2
    exact hcj.trans (hη hij)
  have hmono : Monotone c := fun j j' hjj' =>
    (hmem (c j) j').mp ((hβ hjj').trans ((hmem (c j) j).mpr le_rfl))

  by_cases hinj : Function.Injective c
  · refine absurd (fun i j => ?_) h
    rw [hmem i j, (hmono.strictMono_of_injective hinj).apply_eq]
  · simp only [Function.Injective, not_forall] at hinj
    obtain ⟨j, j', hcjj', hjj'⟩ := hinj
    refine Matrix.det_zero_of_row_eq hjj' (funext fun i => ?_)
    have hiff : β j ≤ η i ↔ β j' ≤ η i := by rw [hmem i j, hmem i j', hcjj']
    simp only [hM, Matrix.of_apply]
    exact if_congr hiff rfl rfl

end TauCeti

open MvPolynomial Finset

namespace TauCeti

open _root_.YoungDiagram (ofPartition card_ofPartition)

section Alternant

variable {R : Type*} [CommRing R]

open scoped Classical in
theorem hsymm_mul_alternant_betaNumber {N : ℕ} (ν : YoungDiagram) (hν : ν.colLen 0 ≤ N) (r : ℕ) :
    hsymm (Fin N) R r * alternant (Fin N) R (fun j => ν.betaNumber N j) =
      ∑ μ : (ν.card + r).Partition with
          ((ofPartition μ).InterlacedBy ν ∧ (ofPartition μ).colLen 0 ≤ N),
        alternant (Fin N) R (fun j => (ofPartition μ).betaNumber N j) := by

  classical
  set β : Fin N → ℕ := fun j => ν.betaNumber N j with hβ
  have hβanti : StrictAnti β := ν.strictAnti_betaNumber N
  have hβsum : ∑ i : Fin N, β i = ν.card + ∑ j : Fin N, (N - 1 - (j : ℕ)) := ν.sum_betaNumber hν
  rw [hsymm_mul_alternant]

  rw [← Finset.sum_filter_of_ne
    (p := fun γ : Fin N → ℕ => Function.Injective fun i => β i + γ i) fun γ _ hγ => by
      by_contra hninj
      exact hγ (alternant_eq_zero_of_not_injective hninj)]

  set P : Finset (ν.card + r).Partition :=
    {μ | (ofPartition μ).colLen 0 ≤ N} with hP
  set T : (ν.card + r).Partition → Finset (Equiv.Perm (Fin N)) :=
    fun μ => {τ | ∀ j, β j ≤ (ofPartition μ).betaNumber N (τ j)} with hT
  have hval : ∀ x ∈ P.sigma T, ∀ i,
      β i + ((ofPartition x.1).betaNumber N (x.2 i) - β i) =
        (ofPartition x.1).betaNumber N (x.2 i) := by
    intro x hx i
    have hdom := (Finset.mem_filter.mp (Finset.mem_sigma.mp hx).2).2
    have := hdom i
    omega
  have hfun : ∀ x ∈ P.sigma T,
      (fun i => β i + ((ofPartition x.1).betaNumber N (x.2 i) - β i)) =
        (fun j : Fin N => (ofPartition x.1).betaNumber N j) ∘ ⇑x.2 :=
    fun x hx => funext fun i => hval x hx i
  have hbij : ∑ x ∈ P.sigma T,
        alternant (Fin N) R (fun j => (ofPartition x.1).betaNumber N (x.2 j)) =
      ∑ γ ∈ {γ ∈ Finset.piAntidiag (univ : Finset (Fin N)) r |
          Function.Injective fun i => β i + γ i},
        alternant (Fin N) R (fun i => β i + γ i) := by
    refine Finset.sum_bij
      (fun x _ => fun i => (ofPartition x.1).betaNumber N (x.2 i) - β i) ?_ ?_ ?_ ?_
    ·
      intro x hx
      have hcol : (ofPartition x.1).colLen 0 ≤ N :=
        (Finset.mem_filter.mp (Finset.mem_sigma.mp hx).1).2
      refine Finset.mem_filter.mpr
        ⟨Finset.mem_piAntidiag.mpr ⟨?_, fun i _ => Finset.mem_univ i⟩, ?_⟩
      · have hsum1 : ∑ i : Fin N, (β i + ((ofPartition x.1).betaNumber N (x.2 i) - β i)) =
            ∑ j : Fin N, (ofPartition x.1).betaNumber N j := by
          rw [Finset.sum_congr rfl fun i _ => hval x hx i]
          exact Equiv.sum_comp x.2 fun j : Fin N => (ofPartition x.1).betaNumber N j
        rw [Finset.sum_add_distrib, hβsum, (ofPartition x.1).sum_betaNumber hcol,
          card_ofPartition] at hsum1
        omega
      · rw [hfun x hx]
        exact ((ofPartition x.1).strictAnti_betaNumber N).injective.comp x.2.injective
    ·
      intro x hx y hy hxy
      have hxy' : (fun i => β i + ((ofPartition x.1).betaNumber N (x.2 i) - β i)) =
          (fun i => β i + ((ofPartition y.1).betaNumber N (y.2 i) - β i)) :=
        funext fun i => by rw [congrFun hxy i]
      have hsx : StrictAnti ((fun i => β i + ((ofPartition y.1).betaNumber N (y.2 i) - β i)) ∘
          ⇑(x.2).symm) := by
        rw [← hxy', hfun x hx]
        simpa [Function.comp_def] using (ofPartition x.1).strictAnti_betaNumber N
      have hsy : StrictAnti ((fun i => β i + ((ofPartition y.1).betaNumber N (y.2 i) - β i)) ∘
          ⇑(y.2).symm) := by
        rw [hfun y hy]
        simpa [Function.comp_def] using (ofPartition y.1).strictAnti_betaNumber N
      have hp : x.2 = y.2 := by
        simpa using congrArg Equiv.symm (hsx.perm_eq hsy)
      have hbx : ∀ i, (ofPartition x.1).betaNumber N (x.2 i) =
          (ofPartition y.1).betaNumber N (y.2 i) := fun i => by
        have h1 := hval x hx i
        have h2 := hval y hy i
        have h3 := congrFun hxy i
        omega
      have hbeta : ∀ j : Fin N,
          (ofPartition x.1).betaNumber N j = (ofPartition y.1).betaNumber N j := fun j => by
        have h := hbx ((x.2).symm j)
        rw [← hp] at h
        simpa using h
      have hshape : ofPartition x.1 = ofPartition y.1 :=
        YoungDiagram.eq_of_betaNumber_eq (Finset.mem_filter.mp (Finset.mem_sigma.mp hx).1).2
          (Finset.mem_filter.mp (Finset.mem_sigma.mp hy).1).2
          fun i hi => hbeta ⟨i, hi⟩
      exact Sigma.ext (YoungDiagram.ofPartition_injective hshape) (by rw [hp])
    ·
      intro γ hγ
      obtain ⟨hγmem, hγinj⟩ := Finset.mem_filter.mp hγ
      obtain ⟨τ₀, hτ₀⟩ := hγinj.exists_strictAnti_comp
      obtain ⟨μ₀, hμ₀col, hμ₀beta⟩ := YoungDiagram.exists_eq_betaNumber_of_strictAnti hτ₀
      have hsumγ : ∑ i : Fin N, γ i = r := (Finset.mem_piAntidiag.mp hγmem).1
      have hcard : μ₀.card = ν.card + r := by
        have h1 : ∑ j : Fin N, μ₀.betaNumber N j = ∑ i : Fin N, (β i + γ i) := by
          rw [Finset.sum_congr rfl fun j _ => hμ₀beta j]
          exact Equiv.sum_comp τ₀ fun i : Fin N => β i + γ i
        rw [μ₀.sum_betaNumber hμ₀col, Finset.sum_add_distrib, hβsum, hsumγ] at h1
        omega
      refine ⟨⟨μ₀.toPartition hcard, τ₀.symm⟩, Finset.mem_sigma.mpr ⟨?_, ?_⟩, ?_⟩
      · exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, by rwa [_root_.YoungDiagram.ofPartition_toPartition]⟩
      · refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun j => ?_⟩
        rw [_root_.YoungDiagram.ofPartition_toPartition, hμ₀beta]
        simp only [Function.comp_apply, Equiv.apply_symm_apply]
        exact Nat.le_add_right _ _
      · refine funext fun i => ?_
        rw [_root_.YoungDiagram.ofPartition_toPartition, hμ₀beta]
        simp only [Function.comp_apply, Equiv.apply_symm_apply]
        omega
    · intro x hx
      exact congrArg (alternant (Fin N) R) (funext fun i => (hval x hx i).symm)
  rw [← hbij, Finset.sum_sigma]

  have hterm : ∀ μ ∈ P,
      ∑ τ ∈ T μ, alternant (Fin N) R (fun j => (ofPartition μ).betaNumber N (τ j)) =
        if (ofPartition μ).InterlacedBy ν then
          alternant (Fin N) R (fun j => (ofPartition μ).betaNumber N j) else 0 := by
    intro μ hμ
    have hcol : (ofPartition μ).colLen 0 ≤ N := (Finset.mem_filter.mp hμ).2
    have hstep : ∀ τ : Equiv.Perm (Fin N),
        alternant (Fin N) R (fun j => (ofPartition μ).betaNumber N (τ j)) =
          (Equiv.Perm.sign τ : ℤ) •
            alternant (Fin N) R (fun j => (ofPartition μ).betaNumber N j) := by
      intro τ

      have hcomp : (fun j : Fin N => (ofPartition μ).betaNumber N (τ j)) =
          (fun j : Fin N => (ofPartition μ).betaNumber N j) ∘ ⇑τ := rfl
      rw [hcomp, alternant_comp_perm]
      simp [Units.smul_def]
    rw [hT, Finset.sum_congr rfl fun τ _ => hstep τ, ← Finset.sum_smul,
      sum_sign_filter_forall_le_of_antitone hβanti.antitone
        ((ofPartition μ).strictAnti_betaNumber N).antitone]

    simp only [hβ, forall_betaNumber_le_iff_interlacedBy hcol hν]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_filter, hP, Finset.filter_filter]
  refine Finset.sum_congr (Finset.filter_congr fun μ _ => ?_) fun _ _ => rfl
  exact and_comm

end Alternant

section SchurPolynomials

variable {R : Type*} [CommSemiring R]

open scoped Classical in
private theorem mul_diagramSchurPoly_of_mul_alternant_betaNumber {N n : ℕ}
    (p : MvPolynomial (Fin N) ℕ) (ν : YoungDiagram) (P : n.Partition → Prop)
    (hP : ∀ μ, P μ → ν ≤ ofPartition μ)
    (halt : ν.colLen 0 ≤ N →
      MvPolynomial.map (Nat.castRingHom ℤ) p * alternant (Fin N) ℤ (fun j => ν.betaNumber N j) =
        ∑ μ : n.Partition with (P μ ∧ (ofPartition μ).colLen 0 ≤ N),
          alternant (Fin N) ℤ fun j => (ofPartition μ).betaNumber N j) :
    MvPolynomial.map (Nat.castRingHom R) p * diagramSchurPoly N R ν =
      ∑ μ : n.Partition with P μ, diagramSchurPoly N R (ofPartition μ) := by

  have hℤ : MvPolynomial.map (Nat.castRingHom ℤ) p * diagramSchurPoly N ℤ ν =
      ∑ μ : n.Partition with P μ, diagramSchurPoly N ℤ (ofPartition μ) := by
    by_cases hν : ν.colLen 0 ≤ N
    ·
      refine mul_right_cancel₀ (alternant_ne_zero_of_injective (injective_staircase N)) ?_
      rw [mul_assoc, diagramSchurPoly_mul_alternant N ν hν, halt hν, sum_mul, ← filter_filter,
        sum_filter]
      refine sum_congr rfl fun μ _ => ?_
      split_ifs with hμ
      · rw [diagramSchurPoly_mul_alternant N _ hμ]
      · rw [diagramSchurPoly_eq_zero_of_lt_colLen (Nat.lt_of_not_le hμ), zero_mul]
    ·
      have hν' : N < ν.colLen 0 := Nat.lt_of_not_le hν
      rw [diagramSchurPoly_eq_zero_of_lt_colLen hν', mul_zero]
      refine (sum_eq_zero fun μ hμ => ?_).symm
      exact diagramSchurPoly_eq_zero_of_lt_colLen (hν'.trans_le
        (YoungDiagram.colLen_le_of_le (hP μ (mem_filter.mp hμ).2) 0))
  have hℕ : p * diagramSchurPoly N ℕ ν =
      ∑ μ : n.Partition with P μ, diagramSchurPoly N ℕ (ofPartition μ) :=
    MvPolynomial.map_injective (Nat.castRingHom ℤ) Nat.cast_injective <| by
      simpa [map_diagramSchurPoly, map_sum] using hℤ
  simpa [map_diagramSchurPoly, map_sum] using
    congrArg (MvPolynomial.map (Nat.castRingHom R)) hℕ

open scoped Classical in
theorem hsymm_mul_diagramSchurPoly {N : ℕ} (ν : YoungDiagram) (r : ℕ) :
    hsymm (Fin N) R r * diagramSchurPoly N R ν =
      ∑ μ : (ν.card + r).Partition with (ofPartition μ).InterlacedBy ν,
        diagramSchurPoly N R (ofPartition μ) := by
  have h := mul_diagramSchurPoly_of_mul_alternant_betaNumber (R := R) (hsymm (Fin N) ℕ r) ν
    (fun μ => (ofPartition μ).InterlacedBy ν) (fun _ hμ => hμ.le)
    fun hν => by rw [map_hsymm]; exact hsymm_mul_alternant_betaNumber ν hν r
  rwa [map_hsymm] at h

end SchurPolynomials

end TauCeti

end
end D5.S3.Combinatorics.Partitions.SpechtPolytabloid
