import CFMPDoubleHalfPlane1490Transient
import Batteries.Tactic.OpenPrivate

set_option autoImplicit false
noncomputable section
namespace D5.S3.Geometry.Gluing.RawFaceEdgeBand1511Candidate
open D5.S3.Geometry.Hyperideal.EdgeStarTransitions (RawFacePairing)
open D5.S3.Geometry.Gluing.RawFaceCapSliceCandidate
open D5.S3.Geometry.Gluing.RawFaceInteriorEdge1436Candidate
open private sigma_face from CFMPRawFaceCapSlice1053Transient
open Topology Set

abbrev Band (a b δ : ℝ) := {p : ℝ × ℝ // a < p.1 ∧ p.1 < b ∧ 0 ≤ p.2 ∧ p.2 < δ}

def coords (e : Equiv.Perm (Fin 4)) (p : ℝ × ℝ) : Fin 4 → ℝ :=
  fun i => ![0,p.1,p.2,1-p.1-p.2] (e.symm i)

theorem coords_values (e : Equiv.Perm (Fin 4)) (p : ℝ × ℝ) :
    coords e p (e 0) = 0 ∧ coords e p (e 1) = p.1 ∧
      coords e p (e 2) = p.2 ∧ coords e p (e 3) = 1-p.1-p.2 := by
  simp [coords]

theorem coords_simplex (e : Equiv.Perm (Fin 4)) (p : ℝ × ℝ)
    (hu : 0 ≤ p.1) (hv : 0 ≤ p.2) (hs : p.1+p.2 ≤ 1) :
    (∀ i, 0 ≤ coords e p i) ∧ (∑ i, coords e p i) = 1 := by
  constructor
  · intro i
    change 0 ≤ (![0,p.1,p.2,1-p.1-p.2] : Fin 4 → ℝ) (e.symm i)
    generalize e.symm i = k
    fin_cases k <;> simp [coords] <;> linarith
  · have hh := e.symm.sum_comp (![0,p.1,p.2,1-p.1-p.2] : Fin 4 → ℝ)
    change (∑ i, (![0,p.1,p.2,1-p.1-p.2] : Fin 4 → ℝ) (e.symm i)) = 1
    rw [hh]
    simp [Fin.sum_univ_succ] <;> ring

theorem coords_inverse (e : Equiv.Perm (Fin 4)) (v : Fin 4 → ℝ)
    (h0 : v (e 0) = 0) (hs : (∑ i, v i) = 1) :
    coords e (v (e 1),v (e 2)) = v := by
  have he : (∑ i, v (e i)) = 1 := (Fintype.sum_equiv e (fun i => v (e i)) v (fun _ => rfl)).trans hs
  simp only [Fin.sum_univ_succ] at he
  funext i
  obtain ⟨k,rfl⟩ := e.surjective i
  fin_cases k <;> simp [coords,h0] at * <;> linarith

variable {T : Type*}

def point (P : RawFacePairing T) (ν : Vertex P) (t : T) (e : Equiv.Perm (Fin 4))
    (hc : label P (t,e 0) = ν) {a b δ : ℝ} (ha : 0 < a) (hb : b+δ < 1)
    (p : Band a b δ) : Point P ν := by
  have h := coords_simplex e p.val (le_of_lt (ha.trans p.property.1))
    p.property.2.2.1 (by linarith [p.property.2.1,p.property.2.2.2])
  exact ⟨((t,e 0),coords e p.val),(coords_values e p.val).1,h.1,h.2,hc⟩

def Patch (P : RawFacePairing T) (ν : Vertex P) (t : T) (e : Equiv.Perm (Fin 4))
    (a b δ : ℝ) : Set (Point P ν) :=
  {x | x.val.1 = (t,e 0) ∧ a < x.val.2 (e 1) ∧ x.val.2 (e 1) < b ∧ x.val.2 (e 2) < δ}

def patchPoint (P : RawFacePairing T) (ν : Vertex P) (t : T) (e : Equiv.Perm (Fin 4))
    (hc : label P (t,e 0) = ν) {a b δ : ℝ} (ha : 0 < a) (hb : b+δ < 1)
    (p : Band a b δ) : ↥(Patch P ν t e a b δ) := by
  refine ⟨point P ν t e hc ha hb p,rfl,?_,?_,?_⟩
  · change a < coords e p.val (e 1)
    simpa only [(coords_values e p.val).2.1] using p.property.1
  · change coords e p.val (e 1) < b
    simpa only [(coords_values e p.val).2.1] using p.property.2.1
  · change coords e p.val (e 2) < δ
    simpa only [(coords_values e p.val).2.2.1] using p.property.2.2.2

def patchCoordinates (P : RawFacePairing T) (ν : Vertex P) (t : T)
    (e : Equiv.Perm (Fin 4)) (a b δ : ℝ) (x : ↥(Patch P ν t e a b δ)) : Band a b δ :=
  ⟨(x.val.val.2 (e 1),x.val.val.2 (e 2)),x.property.2.1,x.property.2.2.1,
    x.val.property.2.1 _,x.property.2.2.2⟩

def originalBandHomeomorph [TopologicalSpace T] (P : RawFacePairing T) (ν : Vertex P) (t : T)
    (e : Equiv.Perm (Fin 4)) (hc : label P (t,e 0) = ν)
    {a b δ : ℝ} (ha : 0 < a) (hb : b+δ < 1) : Band a b δ ≃ₜ ↥(Patch P ν t e a b δ) where
  toFun := patchPoint P ν t e hc ha hb
  invFun := patchCoordinates P ν t e a b δ
  left_inv p := by
    apply Subtype.ext
    exact Prod.ext (coords_values e p.val).2.1 (coords_values e p.val).2.2.1
  right_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · exact x.property.1.symm
    · change coords e (x.val.val.2 (e 1),x.val.val.2 (e 2)) = x.val.val.2
      have h0 := x.val.property.1
      rw [x.property.1] at h0
      exact coords_inverse e x.val.val.2 h0 x.val.property.2.2.1
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    apply Continuous.prodMk continuous_const
    apply continuous_pi
    intro i
    change Continuous (fun p : Band a b δ => coords e p.val i)
    unfold coords
    generalize e.symm i = k
    fin_cases k <;> fun_prop
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact ((continuous_apply (e 1)).comp
      (continuous_snd.comp (continuous_subtype_val.comp continuous_subtype_val))).prodMk
      ((continuous_apply (e 2)).comp
        (continuous_snd.comp (continuous_subtype_val.comp continuous_subtype_val)))

section Topology
variable [TopologicalSpace T] [DiscreteTopology T]
theorem patch_open (P : RawFacePairing T) (ν : Vertex P) (t : T)
    (e : Equiv.Perm (Fin 4)) (a b δ : ℝ) : IsOpen (Patch P ν t e a b δ) := by
  have htag : IsOpen {x : Point P ν | x.val.1 = (t,e 0)} :=
    (isOpen_discrete {(t,e 0)}).preimage (continuous_fst.comp continuous_subtype_val)
  have h1 : Continuous (fun x : Point P ν => x.val.2 (e 1)) :=
    (continuous_apply (e 1)).comp (continuous_snd.comp continuous_subtype_val)
  have h2 : Continuous (fun x : Point P ν => x.val.2 (e 2)) :=
    (continuous_apply (e 2)).comp (continuous_snd.comp continuous_subtype_val)
  exact htag.inter ((isOpen_lt continuous_const h1).inter
    ((isOpen_lt h1 continuous_const).inter (isOpen_lt h2 continuous_const)))

theorem point_openEmbedding (P : RawFacePairing T) (ν : Vertex P) (t : T)
    (e : Equiv.Perm (Fin 4)) (hc : label P (t,e 0) = ν)
    {a b δ : ℝ} (ha : 0 < a) (hb : b+δ < 1) :
    IsOpenEmbedding (point P ν t e hc ha hb) :=
  (patch_open P ν t e a b δ).isOpenEmbedding_subtypeVal.comp
    (originalBandHomeomorph P ν t e hc ha hb).isOpenEmbedding
end Topology

def partnerTet (P : RawFacePairing T) (t : T) (e : Equiv.Perm (Fin 4)) : T :=
  (P.facePair (t,e 2)).1

def partnerFrame (P : RawFacePairing T) (t : T) (e : Equiv.Perm (Fin 4)) :
    Equiv.Perm (Fin 4) := e.trans (sigma P (t,e 2))

theorem paired_label (P : RawFacePairing T) (ν : Vertex P) (t : T)
    (e : Equiv.Perm (Fin 4)) (hc : label P (t,e 0) = ν) :
    label P (partnerTet P t e,partnerFrame P t e 0) = ν := by
  have h := coords_simplex e (1,0) (by norm_num) (by norm_num) (by norm_num)
  let x : Point P ν := ⟨((t,e 0),coords e (1,0)),(coords_values e (1,0)).1,h.1,h.2,hc⟩
  have hf : e 2 ≠ x.val.1.2 := e.injective.ne (by decide)
  exact (pairedPoint P x (e 2) hf).property.2.2.2

theorem point_partner (P : RawFacePairing T) (ν : Vertex P) (t : T)
    (e : Equiv.Perm (Fin 4)) (hc : label P (t,e 0) = ν)
    {a b δ : ℝ} (ha : 0 < a) (hb : b+δ < 1) (p : Band a b δ) :
    point P ν (partnerTet P t e) (partnerFrame P t e) (paired_label P ν t e hc) ha hb p =
      pairedPoint P (point P ν t e hc ha hb p) (e 2) (e.injective.ne (by decide)) := by
  rfl

theorem branches_disjoint (P : RawFacePairing T) (ν : Vertex P) (t : T)
    (e : Equiv.Perm (Fin 4)) (hc : label P (t,e 0) = ν)
    {a b δ : ℝ} (ha : 0 < a) (hb : b+δ < 1) (hδa : δ ≤ a) (hbδ : b+2*δ ≤ 1)
    (p q : Band a b δ) :
    point P ν t e hc ha hb p ≠
      point P ν (partnerTet P t e) (partnerFrame P t e) (paired_label P ν t e hc) ha hb q := by
  intro he
  have ht := congrArg (fun x : Point P ν => x.val.1.1) he
  have hj := congrArg (fun x : Point P ν => x.val.1.2) he
  change t = partnerTet P t e at ht
  change e 0 = partnerFrame P t e 0 at hj
  let f' := partnerFrame P t e 2
  have hf0 : f' ≠ e 0 := by
    rw [hj]
    exact (partnerFrame P t e).injective.ne (by decide)
  have hf2 : f' ≠ e 2 := by
    intro h
    have hp : P.facePair (t,e 2) = (t,e 2) := Prod.ext ht.symm (by
      change (P.facePair (t,e 2)).2 = e 2
      rw [← sigma_face P (t,e 2)]
      exact h)
    exact P.pairFixedFree (t,e 2) hp
  have hv := congrArg (fun x : Point P ν => x.val.2 f') he
  change coords e p.val f' = coords (partnerFrame P t e) q.val f' at hv
  rw [(coords_values (partnerFrame P t e) q.val).2.2.1] at hv
  have hcases : f' = e 0 ∨ f' = e 1 ∨ f' = e 2 ∨ f' = e 3 := by
    obtain ⟨i,hi⟩ := e.surjective f'
    fin_cases i
    · exact Or.inl hi.symm
    · exact Or.inr (Or.inl hi.symm)
    · exact Or.inr (Or.inr (Or.inl hi.symm))
    · exact Or.inr (Or.inr (Or.inr hi.symm))
  rcases hcases with h | h | h | h
  · exact hf0 h
  · rw [h,(coords_values e p.val).2.1] at hv
    linarith [p.property.1,q.property.2.2.2]
  · exact hf2 h
  · rw [h,(coords_values e p.val).2.2.2] at hv
    linarith [p.property.2.1,p.property.2.2.2,q.property.2.2.2]

end D5.S3.Geometry.Gluing.RawFaceEdgeBand1511Candidate

run_cmd do
  let env := (← Lean.getEnv).setExporting false
  for name in [``D5.S3.Geometry.Gluing.RawFaceEdgeBand1511Candidate.coords_values,
      ``D5.S3.Geometry.Gluing.RawFaceEdgeBand1511Candidate.coords_simplex,
      ``D5.S3.Geometry.Gluing.RawFaceEdgeBand1511Candidate.coords_inverse,
      ``D5.S3.Geometry.Gluing.RawFaceEdgeBand1511Candidate.originalBandHomeomorph,
      ``D5.S3.Geometry.Gluing.RawFaceEdgeBand1511Candidate.patch_open,
      ``D5.S3.Geometry.Gluing.RawFaceEdgeBand1511Candidate.point_openEmbedding,
      ``D5.S3.Geometry.Gluing.RawFaceEdgeBand1511Candidate.paired_label,
      ``D5.S3.Geometry.Gluing.RawFaceEdgeBand1511Candidate.point_partner,
      ``D5.S3.Geometry.Gluing.RawFaceEdgeBand1511Candidate.branches_disjoint] do
    unless (env.checked.get.find? name).isSome do
      Lean.throwError m!"CFMP1511 missing {name}"
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        Lean.throwError m!"CFMP1511 disallowed {ax}"
    Lean.logInfo m!"CFMP1511 CHECKED {name} axioms={axioms}"
