/- GID: D5/S3/Combinatorics/Graph/StarForming/HeawoodMatrixAction
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Graph/StarForming/HeawoodMatrixAction
   mirror-E: none(waiver:registration-template-not-established)
   anchors: []
   utility: none
   digest: Binary matrix units act equivariantly on the Fano flag gain. -/

import D5.S3.Combinatorics.Graph.StarForming.HeawoodLift

namespace D5.S3.Combinatorics.Graph.StarForming.HeawoodMatrixAction

open HeawoodSwitching HeawoodLift Matrix
open scoped BigOperators
noncomputable section

private abbrev Vector := Fin 3 → F2
private abbrev NonzeroVector := {v : Vector // v ≠ 0}

private theorem coordinate_nonzero : ∀ p : Fin 7, coordinate p ≠ 0 := by decide +kernel

private def coordinates : Fin 7 ≃ NonzeroVector :=
  Equiv.ofBijective (fun p => ⟨coordinate p, coordinate_nonzero p⟩) (by
    constructor
    · intro p q h
      have hinj : Function.Injective coordinate := by decide +kernel
      exact hinj (congrArg Subtype.val h)
    · intro v
      have hall : ∀ x : Vector, x ≠ 0 → ∃ p : Fin 7, coordinate p = x := by decide +kernel
      obtain ⟨p, hp⟩ := hall v.val v.property
      exact ⟨p, Subtype.ext hp⟩)

private def pointAction (g : Matˣ) : NonzeroVector ≃ NonzeroVector where
  toFun v := ⟨(g : Mat) *ᵥ v.val, by
    intro h
    have hg := congrArg (fun x : Vector => (↑g⁻¹ : Mat) *ᵥ x) h
    rw [mulVec_mulVec, Units.inv_mul, one_mulVec, mulVec_zero] at hg
    exact v.property hg⟩
  invFun v := ⟨(↑g⁻¹ : Mat) *ᵥ v.val, by
    intro h
    have hg := congrArg (fun x : Vector => (g : Mat) *ᵥ x) h
    rw [mulVec_mulVec, Units.mul_inv, one_mulVec, mulVec_zero] at hg
    exact v.property hg⟩
  left_inv v := Subtype.ext (by
    change (↑g⁻¹ : Mat) *ᵥ ((g : Mat) *ᵥ v.val) = v.val
    rw [mulVec_mulVec, Units.inv_mul, one_mulVec])
  right_inv v := Subtype.ext (by
    change (g : Mat) *ᵥ ((↑g⁻¹ : Mat) *ᵥ v.val) = v.val
    rw [mulVec_mulVec, Units.mul_inv, one_mulVec])

private def lineAction (g : Matˣ) : NonzeroVector ≃ NonzeroVector where
  toFun v := ⟨v.val ᵥ* (↑g⁻¹ : Mat), by
    intro h
    have hg := congrArg (fun x : Vector => x ᵥ* (g : Mat)) h
    rw [vecMul_vecMul, Units.inv_mul, vecMul_one, zero_vecMul] at hg
    exact v.property hg⟩
  invFun v := ⟨v.val ᵥ* (g : Mat), by
    intro h
    have hg := congrArg (fun x : Vector => x ᵥ* (↑g⁻¹ : Mat)) h
    rw [vecMul_vecMul, Units.mul_inv, vecMul_one, zero_vecMul] at hg
    exact v.property hg⟩
  left_inv v := Subtype.ext (by
    change (v.val ᵥ* (↑g⁻¹ : Mat)) ᵥ* (g : Mat) = v.val
    rw [vecMul_vecMul, Units.inv_mul, vecMul_one])
  right_inv v := Subtype.ext (by
    change (v.val ᵥ* (g : Mat)) ᵥ* (↑g⁻¹ : Mat) = v.val
    rw [vecMul_vecMul, Units.mul_inv, vecMul_one])

private def onPoint (g : Matˣ) : Fin 7 ≃ Fin 7 :=
  (coordinates.trans (pointAction g)).trans coordinates.symm

private def onLine (g : Matˣ) : Fin 7 ≃ Fin 7 :=
  (coordinates.trans (lineAction g)).trans coordinates.symm

private theorem point_coordinates (g : Matˣ) (p : Fin 7) :
    coordinate (onPoint g p) = (g : Mat) *ᵥ coordinate p :=
  congrArg Subtype.val (coordinates.apply_symm_apply (pointAction g (coordinates p)))

private theorem line_coordinates (g : Matˣ) (l : Fin 7) :
    coordinate (onLine g l) = coordinate l ᵥ* (↑g⁻¹ : Mat) :=
  congrArg Subtype.val (coordinates.apply_symm_apply (lineAction g (coordinates l)))

private theorem pairing_preserved (g : Matˣ) (p l : Fin 7) :
    coordinate (onPoint g p) ⬝ᵥ coordinate (onLine g l) = coordinate p ⬝ᵥ coordinate l := by
  rw [point_coordinates, line_coordinates, dotProduct_comm,
    dotProduct_mulVec, vecMul_vecMul, Units.inv_mul, vecMul_one, dotProduct_comm]

private abbrev IncidentPair :=
  {pl : Fin 7 × Fin 7 // coordinate pl.1 ⬝ᵥ coordinate pl.2 = 0}

private theorem flag_pairing : ∀ e : Fin 21,
    coordinate (flags e).1 ⬝ᵥ coordinate (flags e).2 = 0 := by decide +kernel

private def flagNames : Fin 21 ≃ IncidentPair :=
  Equiv.ofBijective (fun e => ⟨flags e, flag_pairing e⟩) (by
    constructor
    · intro e f h
      obtain ⟨i, _, hi⟩ := (flags_complete _ _).mp (flag_pairing e)
      exact (hi e (Prod.eta _).symm).trans
        (hi f ((congrArg Subtype.val h).symm.trans (Prod.eta _).symm)).symm
    · rintro ⟨⟨p, l⟩, h⟩
      obtain ⟨e, he, _⟩ := (flags_complete p l).mp h
      exact ⟨e, Subtype.ext he⟩)

private def incidentAction (g : Matˣ) : IncidentPair ≃ IncidentPair :=
  Equiv.subtypeEquiv ((onPoint g).prodCongr (onLine g)) (fun pl => by
    change (coordinate pl.1 ⬝ᵥ coordinate pl.2 = 0) ↔
      (coordinate (onPoint g pl.1) ⬝ᵥ coordinate (onLine g pl.2) = 0)
    rw [pairing_preserved])

private def onFlag (g : Matˣ) : Fin 21 ≃ Fin 21 :=
  (flagNames.trans (incidentAction g)).trans flagNames.symm

private theorem flag_coordinates (g : Matˣ) (e : Fin 21) :
    flags (onFlag g e) = (onPoint g (flags e).1, onLine g (flags e).2) :=
  congrArg Subtype.val (flagNames.apply_symm_apply (incidentAction g (flagNames e)))

private def transport (g : Matˣ) (s : Signing) : Signing :=
  fun e => s ((onFlag g).symm e)

private theorem phi_outer_sum (s : Signing) :
    phi s = ∑ e : Fin 21, s e • vecMulVec (coordinate (flags e).1) (coordinate (flags e).2) := by
  ext i j
  change (∑ e : Fin 21, s e * coordinate (flags e).1 i * coordinate (flags e).2 j) = _
  simp [Matrix.sum_apply, Matrix.smul_apply, vecMulVec_apply, mul_assoc]

private theorem phi_transport (g : Matˣ) (s : Signing) :
    phi (transport g s) = (g : Mat) * phi s * (↑g⁻¹ : Mat) := by
  rw [phi_outer_sum, phi_outer_sum]
  simp only [Finset.mul_sum, Finset.sum_mul, Matrix.mul_smul, Matrix.smul_mul,
    mul_vecMulVec, vecMulVec_mul]
  calc
    _ = ∑ e : Fin 21, transport g s (onFlag g e) •
        vecMulVec (coordinate (flags (onFlag g e)).1) (coordinate (flags (onFlag g e)).2) :=
      ((onFlag g).sum_comp _).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro e _
      rw [flag_coordinates]
      simp only [transport, Equiv.symm_apply_apply, point_coordinates, line_coordinates]

private def onVertex (g : Matˣ) : Vertex ≃ Vertex :=
  (finSumFinEquiv.symm.trans ((onPoint g).sumCongr (onLine g))).trans finSumFinEquiv

private theorem point_transport (g : Matˣ) (e : Fin 21) :
    onVertex g (point e) = point (onFlag g e) := by
  have hp (f : Fin 21) : point f = Fin.castAdd 7 (flags f).1 := rfl
  simp [onVertex, hp, flag_coordinates]

private theorem line_transport (g : Matˣ) (e : Fin 21) :
    onVertex g (line e) = line (onFlag g e) := by
  have hl (f : Fin 21) : line f = Fin.natAdd 7 (flags f).2 := rfl
  simp [onVertex, hl, flag_coordinates]

private theorem incidence_transport (g : Matˣ) (e : Fin 21) (v w : Vertex) :
    incident (onFlag g e) (onVertex g v) (onVertex g w) ↔ incident e v w := by
  simp only [incident, ← point_transport, ← line_transport, Equiv.apply_eq_iff_eq]

private theorem adjacency_transport (g : Matˣ) (v w : Vertex) :
    base.Adj (onVertex g v) (onVertex g w) ↔ base.Adj v w := by
  constructor
  · rintro ⟨f, hf⟩
    obtain ⟨e, rfl⟩ := (onFlag g).surjective f
    exact ⟨e, (incidence_transport g e v w).mp hf⟩
  · rintro ⟨e, he⟩
    exact ⟨onFlag g e, (incidence_transport g e v w).mpr he⟩

private theorem incident_index (e : Fin 21) (v w : Vertex) (h : incident e v w) :
    edgeIndex v w = e := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact index_flag e
  · exact (index_symm _ _).trans (index_flag e)

private theorem index_transport (g : Matˣ) (v w : Vertex) (h : base.Adj v w) :
    edgeIndex (onVertex g v) (onVertex g w) = onFlag g (edgeIndex v w) :=
  incident_index _ _ _ ((incidence_transport g _ v w).mpr (index_endpoints v w h))

private def liftIso (g : Matˣ) (s : Signing) : graph s ≃g graph (transport g s) where
  toEquiv := (onVertex g).prodCongr (Equiv.refl F2)
  map_rel_iff' := by
    intro x y
    change (base.Adj (onVertex g x.1) (onVertex g y.1) ∧
      x.2 + y.2 = transport g s (edgeIndex (onVertex g x.1) (onVertex g y.1))) ↔
        (base.Adj x.1 y.1 ∧ x.2 + y.2 = s (edgeIndex x.1 y.1))
    rw [adjacency_transport]
    by_cases h : base.Adj x.1 y.1
    · rw [index_transport g x.1 y.1 h]
      simp [transport]
    · simp [h]

/-- Conjugate linear gains yield an isomorphism of the actual two-sheet graphs. -/
theorem isomorphic_of_phi_conjugate (s t : Signing) (g : Matˣ)
    (h : phi t = (g : Mat) * phi s * (↑g⁻¹ : Mat)) : Nonempty (graph s ≃g graph t) := by
  obtain ⟨e⟩ := isomorphic_of_phi_eq (transport g s) t ((phi_transport g s).trans h.symm)
  exact ⟨(liftIso g s).trans e⟩

end
end D5.S3.Combinatorics.Graph.StarForming.HeawoodMatrixAction
