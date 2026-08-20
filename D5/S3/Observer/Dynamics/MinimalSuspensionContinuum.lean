/- GID: D5/S3/Observer/Dynamics/MinimalSuspensionContinuum
   generality: G
   mirror-B: D5/B/S3/Observer/Dynamics/MinimalSuspensionContinuum
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   digest: A minimal compact suspension with positive continuous roof is compact and connected. -/

import Mathlib.Dynamics.Minimal
import Mathlib.Topology.Connected.Basic
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Real
import Mathlib.Topology.UnitInterval

/- Library-search audit trail (2026-08-20):
   * Repository and pinned-Mathlib searches found no mapping-torus or suspension-space
     construction packaging the source theorem.
   * Pinned Mathlib exact hits `isConnected_range`, `IsConnected.iUnion_of_chain`,
     `Dense.prod`, `Dense.quotient`, `IsConnected.closure`, and
     `Quotient.compactSpace` supply the fiber, connected-chain, density, closure,
     and compact-quotient steps and are applied below.
   * Pinned Mathlib also contains `MulAction.dense_orbit` for typeclass-based
     minimal actions.  The theorem states the equivalent dense forward-orbit
     condition publicly because its homeomorphism is supplied as data. -/

noncomputable section

namespace D5.S3.Observer.Dynamics.MinimalSuspensionContinuum

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- The normalized leaf coordinate; physical height is obtained by multiplying
by the roof value at the base point. -/
abbrev RoofCoordinate := Set.Icc (0 : ℝ) 1

private instance roofCoordinateCompactSpace : CompactSpace RoofCoordinate := by
  change CompactSpace (Set.Icc (0 : ℝ) 1)
  infer_instance

private instance roofCoordinateConnectedSpace : ConnectedSpace RoofCoordinate := by
  change ConnectedSpace (Set.Icc (0 : ℝ) 1)
  infer_instance

/-- The compact fundamental domain before its roof endpoints are glued. -/
abbrev SuspensionDomain (K : Type*) := K × RoofCoordinate

/-- Physical height in the roof-scaled fundamental domain. -/
def physicalHeight {K : Type*} (r : K → ℝ) (p : SuspensionDomain K) : ℝ :=
  p.2.1 * r p.1

/-- Endpoint identification in physical roof coordinates. -/
def suspensionRelation {K : Type*} (T : K ≃ K) (r : K → ℝ)
    (p q : SuspensionDomain K) : Prop :=
  p = q ∨
    (physicalHeight r p = r p.1 ∧ physicalHeight r q = 0 ∧ T p.1 = q.1) ∨
    (physicalHeight r q = r q.1 ∧ physicalHeight r p = 0 ∧ T q.1 = p.1)

private theorem physicalHeight_eq_roof_iff {K : Type*} (r : K → ℝ)
    (hpos : ∀ x, 0 < r x) (p : SuspensionDomain K) :
    physicalHeight r p = r p.1 ↔ p.2.1 = 1 := by
  constructor
  · intro h
    dsimp [physicalHeight] at h
    have hp := hpos p.1
    have hz : (p.2.1 - 1) * r p.1 = 0 := by
      calc
        (p.2.1 - 1) * r p.1 = p.2.1 * r p.1 - 1 * r p.1 := sub_mul _ _ _
        _ = r p.1 - r p.1 := by rw [h, one_mul]
        _ = 0 := sub_self _
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_right hp.ne')
  · rintro h
    simp [physicalHeight, h]

private theorem physicalHeight_eq_zero_iff {K : Type*} (r : K → ℝ)
    (hpos : ∀ x, 0 < r x) (p : SuspensionDomain K) :
    physicalHeight r p = 0 ↔ p.2.1 = 0 := by
  constructor
  · intro h
    dsimp [physicalHeight] at h
    have hp := hpos p.1
    exact (mul_eq_zero.mp h).resolve_right hp.ne'
  · rintro h
    simp [physicalHeight, h]

private theorem suspensionRelation_trans {K : Type*} (T : K ≃ K) (r : K → ℝ)
    (hpos : ∀ x, 0 < r x) {p q z : SuspensionDomain K}
    (hpq : suspensionRelation T r p q) (hqz : suspensionRelation T r q z) :
    suspensionRelation T r p z := by
  rcases hpq with rfl | hpq | hpq
  · exact hqz
  · rcases hqz with rfl | hqz | hqz
    · exact Or.inr (Or.inl hpq)
    · have hq0 := (physicalHeight_eq_zero_iff r hpos q).mp hpq.2.1
      have hq1 := (physicalHeight_eq_roof_iff r hpos q).mp hqz.1
      exact False.elim (zero_ne_one (hq0.symm.trans hq1))
    · left
      apply Prod.ext
      · exact T.injective (hpq.2.2.trans hqz.2.2.symm)
      · apply Subtype.ext
        exact ((physicalHeight_eq_roof_iff r hpos p).mp hpq.1).trans
          ((physicalHeight_eq_roof_iff r hpos z).mp hqz.1).symm
  · rcases hqz with rfl | hqz | hqz
    · exact Or.inr (Or.inr hpq)
    · left
      apply Prod.ext
      · exact hpq.2.2.symm.trans hqz.2.2
      · apply Subtype.ext
        exact ((physicalHeight_eq_zero_iff r hpos p).mp hpq.2.1).trans
          ((physicalHeight_eq_zero_iff r hpos z).mp hqz.2.1).symm
    · have hq1 := (physicalHeight_eq_roof_iff r hpos q).mp hpq.1
      have hq0 := (physicalHeight_eq_zero_iff r hpos q).mp hqz.2.1
      exact False.elim (one_ne_zero (hq1.symm.trans hq0))

/-- The physical endpoint relation is an equivalence relation for a strictly
positive roof. -/
def suspensionSetoid {K : Type*} (T : K ≃ K) (r : K → ℝ)
    (hpos : ∀ x, 0 < r x) : Setoid (SuspensionDomain K) where
  r := suspensionRelation T r
  iseqv := {
    refl := fun p => by
      simp [suspensionRelation]
    symm := by
      intro p q hpq
      rcases hpq with rfl | hpq | hpq
      · exact Or.inl rfl
      · exact Or.inr (Or.inr hpq)
      · exact Or.inr (Or.inl hpq)
    trans := suspensionRelation_trans T r hpos }

/-- The roof suspension, represented by its compact physical fundamental
domain with upper and lower endpoints glued by the base homeomorphism. -/
abbrev Suspension {K : Type*} [TopologicalSpace K] (T : K ≃ₜ K) (r : K → ℝ)
    (hpos : ∀ x, 0 < r x) :=
  Quotient (suspensionSetoid T.toEquiv r hpos)

private def suspensionFiber {K : Type*} [TopologicalSpace K]
    (T : K ≃ₜ K) (r : K → ℝ) (hpos : ∀ x, 0 < r x) (x : K) :
    Set (Suspension T r hpos) :=
  Set.range fun u : RoofCoordinate => Quotient.mk' (s := suspensionSetoid T.toEquiv r hpos) (x, u)

private theorem suspensionFiber_connected {K : Type*} [TopologicalSpace K]
    (T : K ≃ₜ K) (r : K → ℝ) (hpos : ∀ x, 0 < r x) (x : K) :
    IsConnected (suspensionFiber T r hpos x) := by
  apply isConnected_range
  exact continuous_quotient_mk'.comp (continuous_const.prodMk continuous_id)

private theorem adjacent_fibers_meet {K : Type*} [TopologicalSpace K]
    (T : K ≃ₜ K) (r : K → ℝ) (hpos : ∀ x, 0 < r x) (x : K) :
    (suspensionFiber T r hpos x ∩ suspensionFiber T r hpos (T x)).Nonempty := by
  let top : RoofCoordinate := ⟨1, by simp⟩
  let bottom : RoofCoordinate := ⟨0, by simp⟩
  refine ⟨Quotient.mk' (s := suspensionSetoid T.toEquiv r hpos) (x, top), ?_, ?_⟩
  · exact ⟨top, rfl⟩
  · refine ⟨bottom, ?_⟩
    apply Quotient.sound
    refine Or.inr (Or.inr ⟨?_, ?_, rfl⟩)
    · change (1 : ℝ) * r x = r x
      simp
    · change (0 : ℝ) * r (T x) = 0
      simp

/-- A compact metric base, a minimal homeomorphism, and a continuous strictly
positive roof produce a compact connected suspension continuum. -/
theorem minimal_suspension_compact_connected
    {K : Type*} [MetricSpace K] [CompactSpace K] [Nonempty K]
    (T : K ≃ₜ K) (r : K → ℝ) (_hr : Continuous r) (hpos : ∀ x, 0 < r x)
    (hminimal : ∀ x : K, Dense (Set.range fun n : ℕ => (T ^ n) x)) :
    IsCompact (Set.univ : Set (Suspension T r hpos)) ∧
      IsConnected (Set.univ : Set (Suspension T r hpos)) := by
  constructor
  · exact isCompact_univ
  · letI : Setoid (SuspensionDomain K) := suspensionSetoid T.toEquiv r hpos
    let x0 : K := Classical.choice (inferInstance : Nonempty K)
    let fibers : ℕ → Set (Suspension T r hpos) := fun n =>
      suspensionFiber T r hpos ((T ^ n) x0)
    have hfibers : ∀ n, IsConnected (fibers n) := by
      intro n
      exact suspensionFiber_connected T r hpos ((T ^ n) x0)
    have hpow : ∀ n : ℕ, (T ^ (n + 1)) x0 = T ((T ^ n) x0) := by
      intro n
      have h := congrArg (fun S : K ≃ₜ K => S x0) (pow_succ' T n)
      simpa using h
    have hmeet : ∀ n, (fibers n ∩ fibers (Order.succ n)).Nonempty := by
      intro n
      change
        (suspensionFiber T r hpos ((T ^ n) x0) ∩
          suspensionFiber T r hpos ((T ^ (Order.succ n)) x0)).Nonempty
      rw [show Order.succ n = n + 1 by rfl, hpow n]
      exact adjacent_fibers_meet T r hpos ((T ^ n) x0)
    have horbitConnected : IsConnected (⋃ n, fibers n) :=
      IsConnected.iUnion_of_chain hfibers hmeet
    let orbit : Set K := Set.range fun n : ℕ => (T ^ n) x0
    have horbitDense : Dense orbit := hminimal x0
    have hdomainDense :
        Dense (orbit ×ˢ (Set.univ : Set RoofCoordinate)) :=
      horbitDense.prod dense_univ
    have hquotientDense : Dense
        (Quotient.mk' (s := suspensionSetoid T.toEquiv r hpos) ''
          (orbit ×ˢ (Set.univ : Set RoofCoordinate))) :=
      hdomainDense.quotient
    have hsubset :
        Quotient.mk' (s := suspensionSetoid T.toEquiv r hpos) ''
            (orbit ×ˢ (Set.univ : Set RoofCoordinate)) ⊆
          ⋃ n, fibers n := by
      rintro y ⟨p, hp, rfl⟩
      rcases p with ⟨x, u⟩
      rcases hp.1 with ⟨n, hn⟩
      change (T ^ n) x0 = x at hn
      subst x
      exact Set.mem_iUnion.2 ⟨n, ⟨u, rfl⟩⟩
    have hunionDense : Dense (⋃ n, fibers n) :=
      hquotientDense.mono hsubset
    rw [← hunionDense.closure_eq]
    exact horbitConnected.closure

/-- A singleton compact metric base with constant roof satisfies every public
hypothesis of the suspension theorem. -/
example :
    ∃ (T : PUnit ≃ₜ PUnit) (r : PUnit → ℝ),
      Continuous r ∧ (∀ x, 0 < r x) ∧
        ∀ x, Dense (Set.range fun n : ℕ => (T ^ n) x) := by
  refine ⟨Homeomorph.refl PUnit, fun _ => 1, continuous_const, by simp, ?_⟩
  intro x
  have hrange :
      Set.range (fun n : ℕ => ((Homeomorph.refl PUnit) ^ n) x) = Set.univ := by
    ext y
    constructor
    · intro
      trivial
    · intro
      refine ⟨0, ?_⟩
      simp
  rw [hrange]
  exact dense_univ

#print axioms minimal_suspension_compact_connected

end D5.S3.Observer.Dynamics.MinimalSuspensionContinuum
