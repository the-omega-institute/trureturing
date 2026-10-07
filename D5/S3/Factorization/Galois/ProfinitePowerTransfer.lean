/- GID: D5/S3/Factorization/Galois/ProfinitePowerTransfer
   generality: G
   mirror-B: D5/B/S3/Factorization/Galois/ProfinitePowerTransfer
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Uniform finite-group power width transfers through continuous finite quotients. -/
import D5.S3.Factorization.Galois.PowerCompactness
import Mathlib.Topology.Algebra.ClopenNhdofOne
import Mathlib.Data.Finset.Card

set_option autoImplicit false

open D5.S3.Factorization.Galois.NormalCorePower
  D5.S3.Factorization.Galois.PowerCompactness

namespace D5.S3.Factorization.Galois.ProfinitePowerTransfer

universe u

/-- At most `d` algebraic generators in a finite group. -/
def GeneratedByAtMost (Q : Type u) [Group Q] (d : ℕ) : Prop :=
  ∃ S : Finset Q, S.card ≤ d ∧ Subgroup.closure (S : Set Q) = ⊤

/-- The finite-group uniform power-width input of Nikolov–Segal.
This definition declares a proposition; its proof is not supplied by this module. -/
def FinitePowerWidth (d m w : ℕ) : Prop :=
  ∀ (Q : Type u) [Group Q] [Finite Q],
    GeneratedByAtMost Q d → HasPowerWidth Q m w

variable {G : Type u} [Group G]

theorem map_mem_powerSubgroup {Q : Type u} [Group Q] (f : G →* Q) (m : ℕ)
    {g : G} (hg : g ∈ powerSubgroup G m) : f g ∈ powerSubgroup Q m := by
  have hle : powerSubgroup G m ≤ (powerSubgroup Q m).comap f := by
    apply (Subgroup.closure_le _).mpr
    rintro _ ⟨g, rfl⟩
    change f (g ^ m) ∈ powerSubgroup Q m
    rw [map_pow]
    exact pow_mem_powerSubgroup m _
  exact hle hg

theorem map_powerProduct {Q : Type u} [Group Q] (f : G →* Q) (m w : ℕ)
    (a : Fin w → G) :
    f (powerProduct m w a) = powerProduct m w (fun i => f (a i)) := by
  simp only [powerProduct, map_list_prod, List.map_map, Function.comp_def, map_pow]

variable [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]

/-- Dense generators descend to algebraic generators of each continuous finite quotient.
Continuity is used only for the topological quotient by an open normal subgroup. -/
theorem finite_quotient_generated (S : Finset G)
    (hS : (Subgroup.closure (S : Set G)).topologicalClosure = ⊤)
    (N : OpenNormalSubgroup G) : GeneratedByAtMost (G ⧸ N.toSubgroup) S.card := by
  classical
  let f := QuotientGroup.mk' N.toSubgroup
  refine ⟨S.image f, Finset.card_image_le, ?_⟩
  have hdense :=
    (QuotientGroup.mk'_surjective N.toSubgroup).denseRange.topologicalClosure_map_subgroup
    (f := f) QuotientGroup.continuous_mk hS
  have hmap : (Subgroup.closure (S : Set G)).map f =
      Subgroup.closure ((S.image f : Finset (G ⧸ N.toSubgroup)) : Set (G ⧸ N.toSubgroup)) := by
    rw [MonoidHom.map_closure]
    congr 1
    exact (Finset.coe_image).symm
  rw [hmap] at hdense
  apply top_unique
  rw [← hdense]
  exact Subgroup.topologicalClosure_minimal _ le_rfl
    (Set.toFinite _).isClosed

variable [TotallyDisconnectedSpace G]

/-- Finite quotients detect membership in a closed set. The proof uses Mathlib's open-normal
neighborhood theorem, rather than postulating separation or continuity of an abstract quotient. -/
theorem mem_closed_of_finite_quotients (K : Set G) (hK : IsClosed K) (g : G)
    (hquot : ∀ N : OpenNormalSubgroup G,
      ∃ k ∈ K, QuotientGroup.mk' N.toSubgroup g = QuotientGroup.mk' N.toSubgroup k) :
    g ∈ K := by
  by_contra hg
  have hW : IsOpen ((fun z : G => g * z) ⁻¹' Kᶜ) :=
    hK.isOpen_compl.preimage (continuous_const.mul continuous_id)
  have h1 : (1 : G) ∈ (fun z : G => g * z) ⁻¹' Kᶜ := by simpa using hg
  obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hW h1
  obtain ⟨k, hk, heq⟩ := hquot N
  obtain ⟨z, hz, hgz⟩ := (QuotientGroup.mk'_eq_mk' N.toSubgroup).mp heq
  apply hN hz
  change g * z ∈ K
  rw [hgz]
  exact hk

/-- Uniform width in all finite `S.card`-generated groups transfers to the profinite group
with dense generators `S`. The finite-product image is compact, hence closed. -/
theorem profinite_hasPowerWidth_of_finite (S : Finset G)
    (hS : (Subgroup.closure (S : Set G)).topologicalClosure = ⊤) (m w : ℕ)
    (hwidth : FinitePowerWidth.{u} S.card m w) : HasPowerWidth G m w := by
  have : T2Space G := IsTopologicalGroup.t2Space_iff_one_closed.mpr
    (by simp)
  intro g hg
  apply mem_closed_of_finite_quotients (Set.range (powerProduct (G := G) m w))
    (isCompact_range (continuous_powerProduct m w)).isClosed g
  intro N
  let f := QuotientGroup.mk' N.toSubgroup
  obtain ⟨a, ha⟩ := hwidth (G ⧸ N.toSubgroup) (finite_quotient_generated S hS N)
    (f g) (map_mem_powerSubgroup f m hg)
  let b : Fin w → G := fun i => (a i).out
  have hb (i : Fin w) : f (b i) = a i := QuotientGroup.out_eq' _
  refine ⟨powerProduct m w b, ⟨b, rfl⟩, ?_⟩
  change f g = f (powerProduct m w b)
  rw [map_powerProduct, show (fun i => f (b i)) = a from funext hb]
  exact ha.symm

theorem isClosed_powerSubgroup_of_finite_width (S : Finset G)
    (hS : (Subgroup.closure (S : Set G)).topologicalClosure = ⊤) (m w : ℕ)
    (hwidth : FinitePowerWidth.{u} S.card m w) : IsClosed (powerSubgroup G m : Set G) := by
  have : T2Space G := IsTopologicalGroup.t2Space_iff_one_closed.mpr
    (by simp)
  exact isClosed_powerSubgroup_of_width m w (profinite_hasPowerWidth_of_finite S hS m w hwidth)

end D5.S3.Factorization.Galois.ProfinitePowerTransfer
