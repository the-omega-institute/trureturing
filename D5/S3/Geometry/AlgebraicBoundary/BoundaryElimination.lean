/- GID: D5/S3/Geometry/AlgebraicBoundary/BoundaryElimination
   generality: G
   mirror-B: D5/B/S3/Geometry/AlgebraicBoundary/BoundaryElimination
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: An entire cone boundary patch obstructs nonzero transverse elimination identities. -/

import D5.S3.Geometry.AlgebraicBoundary.InteriorCubicFactor
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.RingTheory.Polynomial.Resultant.Basic
import Mathlib.RingTheory.Polynomial.GaussLemma
import Mathlib.RingTheory.MvPolynomial.Basic

/-! Boundary projection supplies the geometric input to polynomial elimination. -/

noncomputable section

open Set Filter
open scoped Topology

namespace D5.S3.Geometry.AlgebraicBoundary.BoundaryElimination

open private cone_interior_add_positive
  from D5.S3.Geometry.AlgebraicBoundary.InteriorCubicFactor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem cone_boundary_patch (C : ProperCone ℝ E) {e z : E}
    (he : e ∈ interior (C : Set E)) (hz : z ∈ frontier (C : Set E))
    {N : Set E} (hN : N ∈ 𝓝 z) :
    ∀ᶠ v in 𝓝 (0 : E), ∃ t : ℝ,
      z + v + t • e ∈ frontier (C : Set E) ∧ z + v + t • e ∈ N := by
  have hc : Continuous (fun w : E × ℝ => z + w.1 + w.2 • e) :=
    (continuous_const.add continuous_fst).add (continuous_snd.smul continuous_const)
  have hpre : {w : E × ℝ | z + w.1 + w.2 • e ∈ N} ∈ 𝓝 ((0 : E), (0 : ℝ)) := by
    exact hc.continuousAt.preimage_mem_nhds (by simpa using hN)
  rw [nhds_prod_eq] at hpre
  obtain ⟨U, hU, V, hV, hUV⟩ := Filter.mem_prod_iff.mp hpre
  obtain ⟨a, b, ⟨ha, hb⟩, hab⟩ := mem_nhds_iff_exists_Ioo_subset.mp hV
  let α := a / 2
  let β := b / 2
  have hα : α < 0 := by dsimp [α]; linarith
  have hβ : 0 < β := by dsimp [β]; linarith
  have hI : Icc α β ⊆ V := by
    intro t ht
    apply hab
    dsimp [α, β] at ht
    rcases ht with ⟨htl, htr⟩
    constructor <;> linarith
  have hzC : z ∈ C := (C.isClosed.frontier_eq ▸ hz).1
  have hzni : z ∉ interior (C : Set E) := (C.isClosed.frontier_eq ▸ hz).2
  have hp : z + β • e ∈ interior (C : Set E) :=
    cone_interior_add_positive C he hzC hβ
  have hm : z + α • e ∉ C := by
    intro h
    have hi := cone_interior_add_positive C he h (neg_pos.mpr hα)
    apply hzni
    simpa [← add_assoc, ← add_smul] using hi
  have hplus : ∀ᶠ v in 𝓝 (0 : E), z + v + β • e ∈ interior (C : Set E) := by
    exact ((continuous_const.add continuous_id).add continuous_const).continuousAt.eventually
      (isOpen_interior.mem_nhds (by simpa using hp))
  have hminus : ∀ᶠ v in 𝓝 (0 : E), z + v + α • e ∉ C := by
    exact ((continuous_const.add continuous_id).add continuous_const).continuousAt.eventually
      (C.isClosed.isOpen_compl.mem_nhds (by simpa using hm))
  filter_upwards [hU, hplus, hminus] with v hv hvp hvm
  let F : ℝ → E := fun t => z + v + t • e
  have hFc : Continuous F := continuous_const.add (continuous_id.smul continuous_const)
  have hconn : IsPreconnected (F '' Icc α β) := isPreconnected_Icc.image F hFc.continuousOn
  have hends : α ≤ β := hα.le.trans hβ.le
  have hex : ∃ t ∈ Icc α β, F t ∈ frontier (C : Set E) := by
    by_contra! hn
    have hcover : F '' Icc α β ⊆ interior (C : Set E) ∪ (C : Set E)ᶜ := by
      rintro y ⟨t, ht, rfl⟩
      by_cases h : F t ∈ C
      · left
        by_contra hi
        exact hn t ht (C.isClosed.frontier_eq ▸ ⟨h, hi⟩)
      · exact Or.inr h
    rcases hconn.subset_or_subset isOpen_interior C.isClosed.isOpen_compl
      (Set.disjoint_left.mpr (fun _ hi ho => ho (interior_subset hi))) hcover with h | h
    · exact hvm (interior_subset (h ⟨α, ⟨le_rfl, hends⟩, rfl⟩))
    · exact (h ⟨β, ⟨hends, le_rfl⟩, rfl⟩) (interior_subset hvp)
  obtain ⟨t, ht, htf⟩ := hex
  exact ⟨t, htf, hUV (show (v, t) ∈ U ×ˢ V from ⟨hv, hI ht⟩)⟩

/-- A factor that is indispensable at an actual boundary point cannot admit a
nonzero elimination identity with another entire-boundary equation. The identity
is an input to this bridge; it is not inferred from polynomial coprimality here. -/
private theorem boundary_eliminant_eq_zero {κ : Type*}
    (C : ProperCone ℝ E) {e z : E}
    (he : e ∈ interior (C : Set E)) (hz : z ∈ frontier (C : Set E))
    (π : E →L[ℝ] (κ → ℝ)) (J : (κ → ℝ) →L[ℝ] E)
    (hπe : π e = 0) (hπJ : ∀ v, π (J v) = v)
    (f g h A B : E → ℝ) (hg : Continuous g) (hgz : g z ≠ 0)
    (hfg : ∀ y ∈ frontier (C : Set E), f y * g y = 0)
    (hh : ∀ y ∈ frontier (C : Set E), h y = 0)
    (R : MvPolynomial κ ℝ)
    (hid : ∀ y, A y * f y + B y * h y = MvPolynomial.eval (π y) R) : R = 0 := by
  classical
  have hN : {y | g y ≠ 0} ∈ 𝓝 z :=
    (hg.isOpen_preimage _ isOpen_ne).mem_nhds hgz
  have hpatch := cone_boundary_patch C he hz hN
  have hparam : Tendsto (fun v : κ → ℝ => J (v - π z)) (𝓝 (π z)) (𝓝 (0 : E)) := by
    have hc : Continuous (fun v : κ → ℝ => J (v - π z)) :=
      J.continuous.comp (continuous_id.sub continuous_const)
    simpa using hc.tendsto (π z)
  have hzero : ∀ᶠ v in 𝓝 (π z), MvPolynomial.eval v R = 0 := by
    filter_upwards [hparam.eventually hpatch] with v hv
    obtain ⟨t, htf, htg⟩ := hv
    let y := z + J (v - π z) + t • e
    have hfy : f y = 0 := (mul_eq_zero.mp (hfg y htf)).resolve_right htg
    have hpy : π y = v := by simp [y, map_add, map_smul, hπJ, hπe]
    have hi := hid y
    rw [hfy, hh y htf, mul_zero, mul_zero, zero_add, hpy] at hi
    exact hi.symm
  obtain ⟨U, hUsub, hUo, haU⟩ := mem_nhds_iff.mp hzero
  obtain ⟨I, s, hs, hsU⟩ := isOpen_pi_iff.mp hUo (π z) haU
  let T (i : κ) : Set ℝ := if i ∈ I then s i else univ
  have hT (i : κ) : (T i).Infinite := by
    by_cases hi : i ∈ I
    · exact infinite_of_mem_nhds ((π z) i) (by simpa [T, hi] using
        ((hs i hi).1.mem_nhds (hs i hi).2))
    · simpa [T, hi] using infinite_univ (α := ℝ)
  have hTU : univ.pi T ⊆ U := by
    simpa only [T, ← Finset.mem_coe, univ_pi_ite] using hsU
  apply MvPolynomial.funext_set T hT
  intro v hv
  simpa using hUsub (hTU hv)

/-- An irreducible nonconstant polynomial factor visible on a genuine cone
boundary patch divides every entire-boundary equation, in actual transverse
polynomial coordinates. No degree bound is imposed on either polynomial. -/
private theorem visible_irreducible_factor_dvd {κ : Type*}
    (C : ProperCone ℝ E) {e z : E}
    (he : e ∈ interior (C : Set E)) (hz : z ∈ frontier (C : Set E))
    (π : E →L[ℝ] (κ → ℝ)) (J : (κ → ℝ) →L[ℝ] E)
    (hπe : π e = 0) (hπJ : ∀ v, π (J v) = v)
    (u : E → ℝ) (P Q : Polynomial (MvPolynomial κ ℝ))
    (hP : Irreducible P) (hPd : P.natDegree ≠ 0)
    (g : E → ℝ) (hg : Continuous g) (hgz : g z ≠ 0)
    (hPg : ∀ y ∈ frontier (C : Set E),
      P.eval₂ (MvPolynomial.eval (π y)) (u y) * g y = 0)
    (hQ : ∀ y ∈ frontier (C : Set E),
      Q.eval₂ (MvPolynomial.eval (π y)) (u y) = 0) : P ∣ Q := by
  classical
  let R := P.resultant Q
  obtain ⟨A, B, _, _, hAB⟩ := Polynomial.exists_mul_add_mul_eq_C_resultant
    P Q le_rfl le_rfl (Or.inl hPd)
  have hR : R = 0 := boundary_eliminant_eq_zero C he hz π J hπe hπJ
    (fun y => P.eval₂ (MvPolynomial.eval (π y)) (u y)) g
    (fun y => Q.eval₂ (MvPolynomial.eval (π y)) (u y))
    (fun y => A.eval₂ (MvPolynomial.eval (π y)) (u y))
    (fun y => B.eval₂ (MvPolynomial.eval (π y)) (u y)) hg hgz hPg hQ R (by
      intro y
      have hv := congrArg (Polynomial.eval₂RingHom (MvPolynomial.eval (π y)) (u y)) hAB
      simpa [Polynomial.eval₂RingHom, R, mul_comm] using hv)
  let K := FractionRing (MvPolynomial κ ℝ)
  let φ := algebraMap (MvPolynomial κ ℝ) K
  have hPp := hP.isPrimitive hPd
  have hPi : Irreducible (P.map φ) :=
    (hPp.irreducible_iff_irreducible_map_fraction_map (K := K)).mp hP
  have hres : (P.map φ).resultant (Q.map φ) = 0 := by
    have hmap := Polynomial.resultant_map_map P Q P.natDegree Q.natDegree φ
    rw [Polynomial.natDegree_map_eq_of_injective (IsFractionRing.injective _ _),
      Polynomial.natDegree_map_eq_of_injective (IsFractionRing.injective _ _)]
    simpa [R, hR] using hmap
  have hcop := (Polynomial.resultant_eq_zero_iff.mp hres).2
  exact hPp.dvd_of_fraction_map_dvd_fraction_map (hPi.dvd_iff_not_isCoprime.mpr hcop)

end D5.S3.Geometry.AlgebraicBoundary.BoundaryElimination
