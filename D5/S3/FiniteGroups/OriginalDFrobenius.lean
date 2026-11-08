/- GID: D5/S3/FiniteGroups/OriginalDFrobenius
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/OriginalDFrobenius
   mirror-E: none(waiver:algebraically-proved)
   anchors: []
   utility: none
   digest: Frobenius divisibility over the original Schur division ring. -/

import D5.S3.FiniteGroups.OriginalDClifford
import D5.S3.FiniteGroups.NormalizerImageAction
import D5.S3.FiniteGroups.OriginalDRegularAction
import Mathlib.GroupTheory.SchurZassenhaus
import Mathlib.GroupTheory.Sylow
import Mathlib.RepresentationTheory.Invariants

/-!
The Hall coprimality argument below is the consumed portion of
Yawara Ishida, yawara/odd-order, revision
ba8ec35982ceecbd31ca987cbe0cee30477f4883,
OddOrder/Isaacs/Ch06_FrobeniusActions/KernelComplement.lean, lines 53–103.
Copyright (c) 2026 Yawara Ishida. Released under Apache-2.0.
Schur–Zassenhaus is reused directly from pinned Mathlib.
-/

noncomputable section
namespace D5.S3.FiniteGroups.OriginalDFrobenius

set_option backward.isDefEq.respectTransparency false
open scoped MonoidAlgebra
open OriginalDCliffordCandidate
open D5.S3.FiniteGroups.CliffordDecomposition.Representation
open D5.S3.FiniteGroups.CliffordConstituents.TauCeti.Representation

universe uk uG uV
variable {G : Type uG} [Group G]

private theorem exists_complement [Finite G] (N : Subgroup G) [N.Normal]
    (hfix : ∀ g : G, g ∉ N → ∀ n : N, MulAut.conjNormal g n = n → n = 1) :
    ∃ C : Subgroup G, N.IsComplement' C := by
  classical
  have h4 : ∀ n ∈ N, n ≠ 1 → Subgroup.centralizer ({n} : Set G) ≤ N := by
    intro n hn hn1 g hg
    by_contra hgN
    have hcomm : g * n = n * g := Subgroup.mem_centralizer_singleton_iff.mp hg
    have hfixed : MulAut.conjNormal g (⟨n, hn⟩ : N) = (⟨n, hn⟩ : N) := by
      apply Subtype.ext
      change g * n * g⁻¹ = n
      rw [hcomm, mul_inv_cancel_right]
    exact hn1 (congrArg (fun z : N => (z : G)) (hfix g hgN ⟨n, hn⟩ hfixed))
  have hcop : Nat.Coprime (Nat.card N) N.index := by
    by_contra hncop
    obtain ⟨p, hp, hpN, hpI⟩ := Nat.Prime.not_coprime_iff_dvd.mp hncop
    have : Fact p.Prime := ⟨hp⟩
    -- Cauchy: an element `x ∈ N` of order `p`.
    obtain ⟨x₀, hx₀⟩ := exists_prime_orderOf_dvd_card' (G := ↥N) p hpN
    set x : G := (x₀ : G) with hx_def
    have hx_ord : orderOf x = p := by rw [hx_def, Subgroup.orderOf_coe]; exact hx₀
    have hx_ne : x ≠ 1 := by
      intro h1
      rw [h1, orderOf_one] at hx_ord
      exact hp.one_lt.ne' hx_ord.symm
    have hxN : x ∈ N := x₀.2
    -- extend `⟨x⟩` to a Sylow `p`-subgroup `S` of `G`
    have hzp : IsPGroup p (Subgroup.zpowers x) := by
      refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, hx_ord, pow_one]
    obtain ⟨S, hzS⟩ := hzp.exists_le_sylow
    have hxS : x ∈ (S : Subgroup G) := hzS (Subgroup.mem_zpowers x)
    have hS_nontrivial : Nontrivial ↥(S : Subgroup G) :=
      ⟨⟨⟨x, hxS⟩, 1, fun h => hx_ne (congrArg Subtype.val h)⟩⟩
    -- the center of `S` is a nontrivial subgroup of `C_G(x) ≤ N`
    have : Nontrivial (Subgroup.center ↥(S : Subgroup G)) :=
      S.isPGroup'.center_nontrivial
    obtain ⟨z₀, hz₀_ne⟩ := exists_ne (1 : Subgroup.center ↥(S : Subgroup G))
    set z : G := ((z₀ : ↥(S : Subgroup G)) : G) with hz_def
    have hz_ne : z ≠ 1 := by
      intro h1
      exact hz₀_ne (Subtype.ext (Subtype.ext h1))
    have hz_comm : ∀ s : ↥(S : Subgroup G), (s : G) * z = z * (s : G) := by
      intro s
      have := (Subgroup.mem_center_iff.mp z₀.2 s)
      exact congrArg Subtype.val this
    have hzN : z ∈ N := by
      refine h4 x hxN hx_ne ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hz_comm ⟨x, hxS⟩).symm
    -- so `S ≤ C_G(z) ≤ N`
    have hS_le_N : (S : Subgroup G) ≤ N := by
      refine le_trans ?_ (h4 z hzN hz_ne)
      intro s hs
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hz_comm ⟨s, hs⟩
    -- contradiction: the full `p`-part of `|G|` divides `|N|`, yet `p ∣ [G:N]`
    have hcardS : Nat.card ↥(S : Subgroup G) = p ^ (Nat.card G).factorization p :=
      S.card_eq_multiplicity
    have hdvd_pow : p ^ ((Nat.card G).factorization p + 1) ∣ Nat.card G := by
      rw [pow_succ, ← hcardS, ← Subgroup.card_mul_index (H := N)]
      exact mul_dvd_mul (hcardS ▸ Subgroup.card_dvd_of_le hS_le_N) hpI
    have := (Nat.Prime.pow_dvd_iff_le_factorization hp Nat.card_pos.ne').mp hdvd_pow
    omega
  -- Step 2: Schur-Zassenhaus complement.
  obtain ⟨A, hA⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  exact ⟨A, hA⟩

section ActualCenter
open NormalizerImageAction
variable {k : Type uk} [Field k] {M : Type uV} [AddCommGroup M] [Module k M]
  (r : G →* (M ≃ₗ[k] M)) (L : Subgroup G) [L.Normal]
  {D : Type*} [DivisionRing D] [Module D M] [SMulCommClass k D M]
  (t : G →* Module.End D M) (ht : ∀ g x, t g x = r g x)

private theorem image_D_linear (a : Image r L) (d : D) (x : M) :
    (a : Module.End k M) (d • x) = d • (a : Module.End k M) x := by
  obtain ⟨b, hb⟩ := a.property
  change q r L b = a.val at hb
  rw [← hb]
  induction b using MonoidAlgebra.induction_linear with
  | zero => simp
  | add b c hb hc => simp only [map_add, LinearMap.add_apply, smul_add, hb, hc]
  | single n c =>
    have he : q r L (MonoidAlgebra.single n c) = c • (r (n : G)).toLinearMap := by
      change Representation.asAlgebraHom ((representation r).comp L.subtype) _ = _
      rw [Representation.asAlgebraHom_single]
      rfl
    rw [he]
    change c • r (n : G) (d • x) = d • (c • r (n : G) x)
    rw [← ht, (t (n : G)).map_smul, smul_comm]

end ActualCenter

section Component
variable {k : Type uk} [Field k] {V : Type uV} [AddCommGroup V] [Module k V]
  {N : Subgroup G} [N.Normal] (ρ : Representation k G V)
  [FiniteDimensional k V] [ρ.IsIrreducible]
  (σ : Subrepresentation (ρ.comp N.subtype)) (hσ : IsAtom σ)

private abbrev P := isotypicComponent k[N] (Representation.asModule (ρ.comp N.subtype))
  σ.asSubmodule

private abbrev U := originalDBaseComponent ρ σ hσ
private abbrev H := originalDActualInertia ρ σ hσ

private theorem le_inertia : N ≤ H ρ σ hσ := by
  intro n hn
  change (U ρ σ hσ).map (originalDTranslate ρ n).toLinearMap = U ρ σ hσ
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    exact (P ρ σ).smul_mem (MonoidAlgebra.of k N ⟨n, hn⟩) hx
  · intro x hx
    refine ⟨ρ n⁻¹ x, ?_, ?_⟩
    · exact (P ρ σ).smul_mem (MonoidAlgebra.of k N ⟨n⁻¹, N.inv_mem hn⟩) hx
    · exact Representation.self_inv_apply ρ n x

private theorem action_mem (h : H ρ σ hσ) (u : U ρ σ hσ) :
    ρ (h : G) (u : Representation.asModule (ρ.comp N.subtype)) ∈ U ρ σ hσ := by
  have hh := h.property
  change (U ρ σ hσ).map (originalDTranslate ρ (h : G)).toLinearMap = U ρ σ hσ at hh
  rw [← hh]
  exact Submodule.mem_map_of_mem u.property

private def componentAction : H ρ σ hσ →* (U ρ σ hσ ≃ₗ[k] U ρ σ hσ) where
  toFun h := {
    toFun u := ⟨ρ (h : G) u, action_mem ρ σ hσ h u⟩
    invFun u := ⟨ρ ((h⁻¹ : H ρ σ hσ) : G) u, action_mem ρ σ hσ h⁻¹ u⟩
    left_inv u := Subtype.ext (Representation.inv_self_apply ρ (h : G) u)
    right_inv u := Subtype.ext (Representation.self_inv_apply ρ (h : G) u)
    map_add' u v := Subtype.ext ((ρ (h : G)).map_add u v)
    map_smul' c u := Subtype.ext ((ρ (h : G)).map_smul c u) }
  map_one' := by ext u; exact Subtype.ext (by change ρ 1 (u : V) = u; simp)
  map_mul' h g := by
    ext u
    apply Subtype.ext
    change ρ ((h : G) * (g : G)) (u : V) = ρ (h : G) (ρ (g : G) u)
    rw [map_mul]
    rfl

private def componentDAction : H ρ σ hσ →* Module.End (Module.End k[G] ρ.asModule) (U ρ σ hσ) where
  toFun h := {
    toFun := componentAction ρ σ hσ h
    map_add' := (componentAction ρ σ hσ h).map_add
    map_smul' d u := Subtype.ext ((originalDTranslate ρ (h : G)).map_smul d u) }
  map_one' := by ext u; exact congrArg Subtype.val (LinearEquiv.congr_fun (map_one (componentAction ρ σ hσ)) u)
  map_mul' h g := by ext u; exact congrArg Subtype.val (LinearEquiv.congr_fun (map_mul (componentAction ρ σ hσ) h g) u)

end Component
end D5.S3.FiniteGroups.OriginalDFrobenius
