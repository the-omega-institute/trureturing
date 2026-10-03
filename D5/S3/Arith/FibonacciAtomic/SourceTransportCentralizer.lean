/- GID: D5/S3/Arith/FibonacciAtomic/SourceTransportCentralizer
   generality: G
   mirror-B: D5/B/S3/Arith/FibonacciAtomic/SourceTransportCentralizer
   mirror-E: none(waiver:unbounded-symbolic-proof)
   anchors: []
   utility: none
   digest: The ordered Fibonacci source centralizer consists of unique nonnegative iterates. -/

import D5.S3.Arith.FibonacciAtomic.GenealogicalFiberTransport
import Mathlib.Logic.Equiv.Set

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Arith.FibonacciAtomic.SourceTransportCentralizer

open GenealogicalFiberTransport (Source substitution composition Fiber fiberMap)
open GraftAffineClosure (step)

/-- On the actual free ordered source trees, the stability equation classifies
the alpha orbit, and every pairing-preserving total map commuting with the
Fibonacci substitution is one unique iterate. Every such map is injective;
only exponent zero is bijective on the whole source. Each positive iterate has
one two-sided inverse on its actual image and none on the whole source. -/
theorem source_transport_centralizer :
    (∀ u : Source,
      substitution (substitution u) = FreeMagma.mul (substitution u) u ↔
        ∃ k : ℕ, substitution^[k] (.of true) = u) ∧
    (∀ F : Source → Source,
      ((∀ s t, F (FreeMagma.mul s t) = FreeMagma.mul (F s) (F t)) ∧
        (∀ t, F (substitution t) = substitution (F t))) ↔
      ∃! k : ℕ, F = substitution^[k]) ∧
    (∀ F : Source → Source,
      ((∀ s t, F (FreeMagma.mul s t) = FreeMagma.mul (F s) (F t)) ∧
        (∀ t, F (substitution t) = substitution (F t))) →
      Function.Injective F) ∧
    (∀ k : ℕ, Function.Bijective (substitution^[k]) ↔ k = 0) ∧
    (∀ k : ℕ, 0 < k →
      (∃! δ : Set.range (substitution^[k]) → Source,
        (∀ t : Source, δ ⟨substitution^[k] t, ⟨t, rfl⟩⟩ = t) ∧
        (∀ y : Set.range (substitution^[k]),
          (⟨substitution^[k] (δ y), ⟨δ y, rfl⟩⟩ :
            Set.range (substitution^[k])) = y)) ∧
      ¬ ∃ δ : Source → Source,
        Function.LeftInverse δ (substitution^[k]) ∧
        Function.RightInverse δ (substitution^[k])) := by
  classical
  have transport (t : Source) : composition (substitution t) = step (composition t) :=
    (fiberMap (composition t) 1 ⟨t, rfl⟩).property
  have hinj : Function.Injective substitution := by
    intro x y hxy
    have hc : composition x = composition y := by
      have h := (transport x).symm.trans ((congrArg composition hxy).trans (transport y))
      have h₁ := congrArg Prod.fst h
      have h₂ := congrArg Prod.snd h
      dsimp [step] at h₁ h₂
      apply Prod.ext <;> omega
    let v := composition x + (1, 0)
    have hv : 1 ≤ v.1 + v.2 := by
      dsimp [v]
      omega
    let x' : Fiber v := ⟨FreeMagma.mul x (.of true), rfl⟩
    let y' : Fiber v := ⟨FreeMagma.mul y (.of true), by
      change composition y + (1, 0) = composition x + (1, 0)
      rw [hc]⟩
    have hi := ((GenealogicalFiberTransport.result.1 v.1 v.2 hv).2.2.2.2.1 1).1
    have hf : fiberMap v 1 x' = fiberMap v 1 y' := by
      apply Subtype.ext
      change FreeMagma.mul (substitution x) (substitution (.of true)) =
        FreeMagma.mul (substitution y) (substitution (.of true))
      rw [hxy]
    have h := congrArg Subtype.val (hi hf)
    change FreeMagma.mul x (.of true) = FreeMagma.mul y (.of true) at h
    injection h with hleft
  have no_alpha (t : Source) : substitution t ≠ .of true := by
    intro he
    have ht := transport t
    rw [he] at ht
    have h₁ := congrArg Prod.fst ht
    have h₂ := congrArg Prod.snd ht
    simp only [composition, step] at h₁ h₂
    omega
  have avoid_alpha (k : ℕ) (hk : 0 < k) (t : Source) :
      substitution^[k] t ≠ .of true := by
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    rw [Function.iterate_succ_apply']
    exact no_alpha _
  have classify : ∀ u : Source,
      substitution (substitution u) = FreeMagma.mul (substitution u) u →
      ∃ k : ℕ, substitution^[k] (.of true) = u := by
    intro u
    induction u with
    | of b =>
      intro _
      cases b with
      | false => exact ⟨1, rfl⟩
      | true => exact ⟨0, rfl⟩
    | mul s t _ ht =>
      intro he
      change FreeMagma.mul (substitution (substitution s)) (substitution (substitution t)) =
        FreeMagma.mul (FreeMagma.mul (substitution s) (substitution t)) (FreeMagma.mul s t) at he
      injection he with h₁ h₂
      have hst : s = substitution t :=
        hinj (hinj (h₁.trans (congrArg substitution h₂).symm))
      have het : substitution (substitution t) = FreeMagma.mul (substitution t) t := by
        simpa only [hst] using h₂
      obtain ⟨k, hk⟩ := ht het
      refine ⟨k + 2, ?_⟩
      rw [show k + 2 = k + 1 + 1 by omega, Function.iterate_succ_apply',
        Function.iterate_succ_apply', hk]
      exact h₂
  have stability : ∀ u : Source,
      substitution (substitution u) = FreeMagma.mul (substitution u) u ↔
      ∃ k : ℕ, substitution^[k] (.of true) = u := by
    intro u
    constructor
    · exact classify u
    · rintro ⟨k, rfl⟩
      induction k with
      | zero => rfl
      | succ k ih =>
        have h := congrArg substitution ih
        change substitution (substitution (substitution (substitution^[k] (.of true)))) =
          FreeMagma.mul (substitution (substitution (substitution^[k] (.of true))))
            (substitution (substitution^[k] (.of true))) at h
        simpa only [Function.iterate_succ_apply'] using h
  have orbit_injective : Function.Injective (fun k : ℕ => substitution^[k] (.of true)) := by
    intro m
    induction m with
    | zero =>
      intro n he
      cases n with
      | zero => rfl
      | succ n => exact False.elim (avoid_alpha (n + 1) (by omega) (.of true) he.symm)
    | succ m ih =>
      intro n he
      cases n with
      | zero => exact False.elim (avoid_alpha (m + 1) (by omega) (.of true) he)
      | succ n =>
        exact congrArg Nat.succ (ih (hinj (by
          simpa only [Function.iterate_succ_apply'] using he)))
  have preserves (k : ℕ) : ∀ s t : Source,
      substitution^[k] (FreeMagma.mul s t) =
        FreeMagma.mul (substitution^[k] s) (substitution^[k] t) :=
    Function.Semiconj₂.iterate
      (show Function.Semiconj₂ substitution FreeMagma.mul FreeMagma.mul from
        fun s t => substitution.map_mul s t) k
  have centralizer (F : Source → Source) :
      ((∀ s t, F (FreeMagma.mul s t) = FreeMagma.mul (F s) (F t)) ∧
        (∀ t, F (substitution t) = substitution (F t))) ↔
      ∃! k : ℕ, F = substitution^[k] := by
    constructor
    · rintro ⟨hpair, hcomm⟩
      have hbeta : F (.of false) = substitution (F (.of true)) := hcomm (.of true)
      have he : substitution (substitution (F (.of true))) =
          FreeMagma.mul (substitution (F (.of true))) (F (.of true)) := by
        calc
          _ = substitution (F (.of false)) := congrArg substitution hbeta.symm
          _ = F (substitution (.of false)) := (hcomm (.of false)).symm
          _ = FreeMagma.mul (F (.of false)) (F (.of true)) := hpair _ _
          _ = _ := congrArg (fun z => FreeMagma.mul z (F (.of true))) hbeta
      obtain ⟨k, hk⟩ := (stability (F (.of true))).mp he
      have hF : F = substitution^[k] := by
        let f : Source →ₙ* Source := ⟨F, hpair⟩
        let g : Source →ₙ* Source := ⟨substitution^[k], preserves k⟩
        have hfg : f = g := FreeMagma.hom_ext (by
          funext b
          cases b with
          | true => exact hk.symm
          | false =>
            change F (.of false) = substitution^[k] (substitution (.of true))
            rw [hbeta, ← hk]
            exact ((Function.Commute.iterate_self (substitution : Source → Source) k)
              (.of true)).symm)
        exact congrArg (fun h : Source →ₙ* Source => (h : Source → Source)) hfg
      refine ⟨k, hF, ?_⟩
      intro j hj
      apply orbit_injective
      exact congrFun (hj.symm.trans hF) (.of true)
    · rintro ⟨k, rfl, _⟩
      exact ⟨preserves k,
        Function.Commute.iterate_self (substitution : Source → Source) k⟩
  refine ⟨stability, centralizer, ?_, ?_, ?_⟩
  · intro F hF
    obtain ⟨k, rfl, _⟩ := (centralizer F).mp hF
    exact hinj.iterate k
  · intro k
    constructor
    · intro hbij
      by_contra hk
      obtain ⟨t, ht⟩ := hbij.2 (.of true)
      exact avoid_alpha k (by omega) t ht
    · rintro rfl
      exact Function.bijective_id
  · intro k hk
    constructor
    · let e := Equiv.ofInjective (substitution^[k]) (hinj.iterate k)
      refine ⟨e.symm, ⟨?_, ?_⟩, ?_⟩
      · exact Equiv.ofInjective_symm_apply (hinj.iterate k)
      · intro y
        apply Subtype.ext
        exact Equiv.apply_ofInjective_symm (hinj.iterate k) y
      · intro δ hδ
        funext y
        apply hinj.iterate k
        exact (congrArg Subtype.val (hδ.2 y)).trans
          (Equiv.apply_ofInjective_symm (hinj.iterate k) y).symm
    · rintro ⟨δ, _, hright⟩
      exact avoid_alpha k hk (δ (.of true)) (hright (.of true))

end D5.S3.Arith.FibonacciAtomic.SourceTransportCentralizer
