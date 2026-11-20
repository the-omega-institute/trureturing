/- GID: D5/S3/Combinatorics/Probability/JointNamingReplyCompletion
   generality: G
   mirror-B: D5/B/S3/Combinatorics/Probability/JointNamingReplyCompletion
   mirror-E: none(waiver:symbolic-probability-estimate)
   anchors: []
   utility: none
   digest: The ordered reply law and updated uniform completion kernel preserve the joint sampling law. -/

import D5.S3.Combinatorics.Probability.NamingUpdate
import D5.S3.Combinatorics.Probability.OrderedNamingReply

set_option autoImplicit false
set_option relaxedAutoImplicit false

open D5.S0.Diagonal.Probability.EquivariantEscape (uniformPmf)
open D5.S3.Combinatorics.Probability.NamingRestrictionLaw (namingMass)
open D5.S3.Combinatorics.Probability.NamingUpdate (agrees unused uniform_after_reveal)
open D5.S3.Combinatorics.Probability.OrderedNamingReply
open D5.S3.Combinatorics.Probability.PartialNameAssignment (Candidates)
open scoped ENNReal

namespace D5.S3.Combinatorics.Probability.JointNamingReplyCompletion

section Disintegration

variable {X Y : Type*}

private theorem reply_fiber_support (μ : PMF X) (read : X → Y) (reply : Y)
    (h : reply ∈ (μ.map read).support) :
    ∃ x ∈ {x : X | read x = reply}, x ∈ μ.support := by
  rw [PMF.support_map] at h
  obtain ⟨x, hx, hr⟩ := h
  exact ⟨x, hr, hx⟩

private theorem map_pair_mass (μ : PMF X) (reply : Y) (y : Y) (x : X) :
    (μ.map (Prod.mk reply)) (y,x) =
      @ite ℝ≥0∞ (y = reply) (Classical.propDecidable _) (μ x) 0 := by
  classical
  rw [PMF.map_apply]
  by_cases h : y = reply
  · simp [h, Prod.mk.injEq, tsum_ite_eq']
  · simp [h, Prod.mk.injEq]

private theorem joint_mass (μ : PMF X) (read : X → Y) (y : Y) (x : X) :
    (μ.map (fun a => (read a, a))) (y,x) =
      @ite ℝ≥0∞ (y = read x) (Classical.propDecidable _) (μ x) 0 := by
  classical
  rw [PMF.map_apply]
  calc
    _ = ∑' a : X, if x = a then if y = read x then μ x else 0 else 0 := by
      refine tsum_congr fun a => ?_
      by_cases h : x = a
      · subst a
        simp
      · simp [Prod.mk.injEq, h]
    _ = _ := tsum_ite_eq' x _

private theorem sample_reply_then_conditional (μ : PMF X) (read : X → Y) :
    let q := μ.map read
    (q.bindOnSupport fun reply h =>
      (μ.filter {x | read x = reply} (reply_fiber_support μ read reply h)).map (Prod.mk reply)) =
      μ.map (fun x => (read x, x)) := by
  classical
  intro q
  apply PMF.ext
  rintro ⟨y, x⟩
  rw [PMF.bindOnSupport_apply, joint_mass]
  rw [show (∑' a : Y, q a *
      (if h : q a = 0 then 0 else
        ((μ.filter {z | read z = a} (reply_fiber_support μ read a h)).map (Prod.mk a)) (y,x))) =
      q y * (if h : q y = 0 then 0 else
        ((μ.filter {z | read z = y} (reply_fiber_support μ read y h)).map (Prod.mk y)) (y,x)) from ?_]
  · by_cases hRead : y = read x
    · rw [ite_eq_left hRead]
      by_cases hq : q y = 0
      · simp only [hq, zero_mul]
        by_contra hn
        have hys : y ∈ q.support := by
          change y ∈ (μ.map read).support
          rw [PMF.support_map]
          exact ⟨x, Ne.symm hn, hRead.symm⟩
        exact hys hq
      · rw [dite_eq_right hq, map_pair_mass, ite_eq_left rfl, PMF.filter_apply,
          Set.indicator_of_mem (show x ∈ {z | read z = y} from hRead.symm)]
        have hNorm : (∑' a : X, ({z | read z = y} : Set X).indicator μ a) = q y := by
          rw [PMF.map_apply]
          exact tsum_congr fun a => by simp [Set.indicator_apply, eq_comm]
        rw [hNorm, mul_left_comm, ENNReal.mul_inv_cancel hq (q.apply_ne_top y), mul_one]
    · rw [ite_eq_right hRead]
      by_cases hq : q y = 0
      · simp [hq]
      · rw [dite_eq_right hq, map_pair_mass, ite_eq_left rfl,
          PMF.filter_apply_eq_zero_of_notMem _ (show x ∉ {z | read z = y} from Ne.symm hRead),
          mul_zero]
  · calc
      _ = ∑' a : Y, if y = a then
            q y * (if h : q y = 0 then 0 else
              ((μ.filter {z | read z = y} (reply_fiber_support μ read y h)).map (Prod.mk y)) (y,x))
          else 0 := by
        apply tsum_congr
        intro a
        by_cases ha : y = a
        · subst a
          simp
        · rw [ite_eq_right ha]
          by_cases hq : q a = 0
          · simp [hq]
          · simp [hq, ha]
      _ = _ := tsum_ite_eq' y _

end Disintegration

section ExpandedNaming

variable {V N I : Type*} [DecidableEq V] [Fintype V]

/-- The initial named vertices together with all vertices selected by the request. -/
noncomputable def namedAfter (K : Finset V) (read : I → V) : Finset V := by
  classical
  exact K ∪ Finset.univ.filter (· ∈ Set.range read)

private theorem mem_namedAfter (K : Finset V) (read : I → V) (v : V) :
    v ∈ namedAfter K read ↔ v ∈ K ∨ ∃ i, read i = v := by
  classical
  simp [namedAfter]

/-- Observing an ordered reply identifies the expanded partial naming and
leaves the law uniform over its remaining completions. -/
private theorem uniform_after_ordered_reply [Finite N]
    (K : Finset V) (A : Finset N) (known : K ↪ N) (read : I → V) (reply : I → N)
    (hReply : ∃ f : Candidates K A known, (fun i => f.1 (read i)) = reply) :
    let L := namedAfter K read
    let _ : Fintype (Candidates K A known) := Fintype.ofFinite _
    let _ : Nonempty (Candidates K A known) := ⟨hReply.choose⟩
    let μ := uniformPmf (Candidates K A known)
    let T : Set (Candidates K A known) := {f | (fun i => f.1 (read i)) = reply}
    ∃ expanded : L ↪ N,
      (∀ i (hi : read i ∈ L), expanded ⟨read i, hi⟩ = reply i) ∧
      (∀ f : Candidates K A known, f ∈ T ↔ agrees expanded f.1) ∧
      ∃ h : Nonempty (Candidates L (unused A L expanded) expanded),
        let _ : Fintype (Candidates L (unused A L expanded) expanded) := Fintype.ofFinite _
        let _ : Nonempty (Candidates L (unused A L expanded) expanded) := h
        ∀ hp : ∃ f ∈ T, f ∈ μ.support,
          (μ.filter T hp).map Subtype.val =
            (uniformPmf (Candidates L (unused A L expanded) expanded)).map Subtype.val := by
  classical
  intro L _ _ μ T
  let ref := hReply.choose
  have href : (fun i => ref.1 (read i)) = reply := hReply.choose_spec
  let expanded : L ↪ N := (Function.Embedding.subtype (· ∈ L)).trans ref.1
  have hKL : K ⊆ L := fun _ hv => (mem_namedAfter K read _).2 (Or.inl hv)
  have hOld (x : K) : expanded ⟨x.1, hKL x.2⟩ = known x := ref.2.1 x
  have hNew (x : L) (hx : x.1 ∉ K) : expanded x ∈ A := ref.2.2 ⟨x.1, hx⟩
  have hRows (f : Candidates K A known) : f ∈ T ↔ agrees expanded f.1 := by
    constructor
    · intro hf x
      change f.1 x.1 = ref.1 x.1
      rcases (mem_namedAfter K read x.1).1 x.2 with hOldX | ⟨i, hi⟩
      · exact (f.2.1 ⟨x.1, hOldX⟩).trans (ref.2.1 ⟨x.1, hOldX⟩).symm
      · change (fun i => f.1 (read i)) = reply at hf
        rw [← hi]
        exact (congrFun hf i).trans (congrFun href i).symm
    · intro hf
      change (fun i => f.1 (read i)) = reply
      funext i
      have hi : read i ∈ L := (mem_namedAfter K read _).2 (Or.inr ⟨i, rfl⟩)
      exact (hf ⟨read i, hi⟩).trans (congrFun href i)
  refine ⟨expanded, fun i _ => congrFun href i, hRows, ?_⟩
  have hRef : Nonempty {f : Candidates K A known // agrees expanded f.1} :=
    ⟨⟨ref, fun _ => rfl⟩⟩
  obtain ⟨e, -, hUpdate⟩ := uniform_after_reveal hKL A known expanded hOld hNew hRef
  refine ⟨hRef.map e, ?_⟩
  intro _ _ hp
  have hEvent : T = {f | agrees expanded f.1} := Set.ext hRows
  revert hp
  rw [hEvent]
  intro hp
  exact hUpdate hp

end ExpandedNaming

section JointLaw

variable {V N I : Type*} [DecidableEq V] [Fintype V] [Finite N]

private theorem postcompose_support_bind {α β γ : Type*}
    (q : PMF α) (K : ∀ a ∈ q.support, PMF β) (f : β → γ) :
    (q.bindOnSupport K).map f =
      q.bindOnSupport (fun a ha => (K a ha).map f) := by
  change (q.bindOnSupport K).bind (PMF.pure ∘ f) = _
  rw [← PMF.bindOnSupport_eq_bind, PMF.bindOnSupport_bindOnSupport]
  simp only [PMF.bindOnSupport_eq_bind, PMF.bind_pure_comp]

/-- Sampling a reply first and then a compatible completion has the same joint
law as sampling the full injective naming before reading the reply. -/
theorem joint_ordered_reply_completion
    (K : Finset V) (A : Finset N) (known : K ↪ N) (hsep : ∀ x, known x ∉ A)
    (h : Nonempty (Candidates K A known)) (read : I → V) :
    let L := namedAfter K read
    let _ : Fintype (Candidates K A known) := Fintype.ofFinite _
    let _ : Nonempty (Candidates K A known) := h
    let μ := uniformPmf (Candidates K A known)
    let q := μ.map (fun f i => f.1 (read i))
    let mass := namingMass (Nat.card (FreshVertices K read ↪ A))
    (∀ reply : I → N, q reply =
      @ite ℝ≥0∞ (IsConsistentReply K A known read reply) (Classical.propDecidable _) mass 0) ∧
    ∃ kernel : ∀ reply ∈ q.support, PMF (V ↪ N),
      (∀ reply hp, ∃ expanded : L ↪ N,
        (∀ i (hi : read i ∈ L), expanded ⟨read i, hi⟩ = reply i) ∧
        ∃ h : Nonempty (Candidates L (unused A L expanded) expanded),
          let _ : Fintype (Candidates L (unused A L expanded) expanded) := Fintype.ofFinite _
          let _ : Nonempty (Candidates L (unused A L expanded) expanded) := h
          kernel reply hp =
            (uniformPmf (Candidates L (unused A L expanded) expanded)).map Subtype.val) ∧
      (q.bindOnSupport fun reply hp => (kernel reply hp).map (Prod.mk reply)) =
        μ.map (fun f => ((fun i => f.1 (read i)), f.1)) := by
  classical
  intro L _ _ μ q mass
  refine ⟨ordered_reply_mass K A known hsep h read, ?_⟩
  let observe (f : Candidates K A known) := fun i => f.1 (read i)
  let hasCompletion (reply : I → N) (hp : reply ∈ q.support) :
      ∃ f ∈ {x | observe x = reply}, f ∈ μ.support :=
    reply_fiber_support μ observe reply hp
  let posterior (reply : I → N) (hp : reply ∈ q.support) :=
    μ.filter {f | observe f = reply} (hasCompletion reply hp)
  refine ⟨fun reply hp => (posterior reply hp).map Subtype.val, ?_, ?_⟩
  · intro reply hp
    obtain ⟨f, hf, _⟩ := hasCompletion reply hp
    obtain ⟨expanded, hRows, _, hNew, hCond⟩ :=
      uniform_after_ordered_reply K A known read reply ⟨f, hf⟩
    exact ⟨expanded, hRows, hNew, hCond (hasCompletion reply hp)⟩
  · have hJoint : (q.bindOnSupport fun reply hp => (posterior reply hp).map (Prod.mk reply)) =
        μ.map (fun f => (observe f, f)) :=
      sample_reply_then_conditional μ observe
    have hProjection := congrArg
      (fun measure : PMF ((I → N) × Candidates K A known) =>
        measure.map (fun x => (x.1, x.2.1))) hJoint
    rw [postcompose_support_bind] at hProjection
    simpa only [PMF.map_comp, Function.comp_def] using hProjection

end JointLaw

end D5.S3.Combinatorics.Probability.JointNamingReplyCompletion
