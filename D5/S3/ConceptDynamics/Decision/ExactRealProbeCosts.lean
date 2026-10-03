/- GID: D5/S3/ConceptDynamics/Decision/ExactRealProbeCosts
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Decision/ExactRealProbeCosts
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact probes separate certificates from discovery costs. -/

import D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization
import Mathlib.Topology.UnitInterval

/-!
The source is the exact real probe interface in definition 22.3 of
FIB_SCALE_READOUT_PERMISSION_GEOMETRY. Parameters retain their exact values.
Histories reuse the dependent passive history carrier. The controller extends
history policies by an explicit stall action. Finite runs have no uniform depth
bound; repeated parameters are allowed and charged once. A stall has no finite
run witness, as does an infinite query execution. Neither source identity nor
its Boolean task label is available to the controller.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.ConceptDynamics.Decision.ExactRealProbeCosts

open unitInterval
open D5.S3.ConceptDynamics.Experiment.PassivePolicyNormalization (Hist)

noncomputable section

abbrev Source := I × Bool
abbrev History := Hist (fun _ : I => Bool)
abbrev Controller := History → Option (Sum I Bool)

/-- A probe flips the task bit exactly at the source coordinate. -/
def response (a : I) (s : Source) : Bool :=
  if a = s.1 then !s.2 else s.2

/-- Every recorded response is the actual response of the specified source. -/
def Consistent (h : History) (s : Source) : Prop :=
  ∀ p ∈ h, response p.1 s = p.2

/-- The complete compatibility fiber forces the returned task bit. -/
def Sound (h : History) (b : Bool) : Prop :=
  ∀ s, Consistent h s → s.2 = b

/-- The finite set of different exact query parameters in a history. -/
def parameters (h : History) : Finset I := by
  classical
  exact (h.map Sigma.fst).toFinset

/-- Repeated queries contribute no extra charge. -/
def queryCount (h : History) : Nat := (parameters h).card

/-- Finite execution from a given prefix, retaining its additional ordered record.
There is no constructor for a stall and no depth bound on finite executions. -/
inductive Run (π : Controller) (s : Source) : History → History → Bool → Prop
  | stop (h : History) (b : Bool) (decision : π h = some (.inr b)) :
      Run π s h [] b
  | query (h : History) (a : I) (t : History) (b : Bool)
      (decision : π h = some (.inl a))
      (next : Run π s (h ++ [⟨a, response a s⟩]) t b) :
      Run π s h (⟨a, response a s⟩ :: t) b

/-- Total correctness on the whole source domain. -/
def Correct (π : Controller) : Prop :=
  ∀ s, ∃ h, Run π s [] h s.2

/-- Two initial parameters, followed by a third only when the responses differ. -/
def threeProbe (a c d : I) : Controller := fun h =>
  match h with
  | [] => some (.inl a)
  | [_] => some (.inl c)
  | [p, q] => if p.2 = q.2 then some (.inr p.2) else some (.inl d)
  | _ :: _ :: p :: _ => some (.inr p.2)

/-- The midpoint is a legal exact query parameter. -/
def midpoint : I := ⟨1 / 2, by constructor <;> norm_num⟩

/-- Every source has a sound certificate of exactly two different parameters;
no compatible sound history can use fewer parameters. -/
theorem result :
    ∀ s : Source,
      (∀ h, Consistent h s → Sound h s.2 → 2 ≤ queryCount h) ∧
      ∃ h, Consistent h s ∧ Sound h s.2 ∧ queryCount h = 2 := by
  classical
  have mem_parameters (h : History) (p : Sigma (fun _ : I => Bool)) (hp : p ∈ h) :
      p.1 ∈ parameters h := by
    simp only [parameters, List.mem_toFinset, List.mem_map]
    exact ⟨p, hp, rfl⟩
  have zero_ne_one : (0 : I) ≠ 1 := by
    intro he
    have := congrArg (fun a : I => (a : ℝ)) he
    norm_num at this
  have middle_ne_zero : midpoint ≠ (0 : I) := by
    intro he
    have := congrArg (fun a : I => (a : ℝ)) he
    norm_num [midpoint] at this
  have middle_ne_one : midpoint ≠ (1 : I) := by
    intro he
    have := congrArg (fun a : I => (a : ℝ)) he
    norm_num [midpoint] at this
  have singleton_obstruction (h : History) (s : Source) (hc : Consistent h s)
      (hs : Sound h s.2) : 2 ≤ queryCount h := by
    by_contra hn
    have hcard : (parameters h).card ≤ 1 := by unfold queryCount at hn; omega
    obtain ⟨a, ha⟩ := Finset.card_le_one_iff_subset_singleton.mp hcard
    let r := response a s
    let z : I := if a = 0 then 1 else 0
    have hza : z ≠ a := by
      dsimp [z]
      split_ifs with hzero
      · subst a; exact zero_ne_one.symm
      · exact Ne.symm hzero
    have compat_flip : Consistent h (a, !r) := by
      intro p hp
      have hpa : p.1 = a := Finset.mem_singleton.mp (ha (mem_parameters h p hp))
      have hpr := hc p hp
      rw [hpa] at hpr ⊢
      simpa [response, r] using hpr
    have compat_plain : Consistent h (z, r) := by
      intro p hp
      have hpa : p.1 = a := Finset.mem_singleton.mp (ha (mem_parameters h p hp))
      have hpr := hc p hp
      rw [hpa] at hpr ⊢
      simpa [response, hza.symm, r] using hpr
    have hflip := hs (a, !r) compat_flip
    have hplain := hs (z, r) compat_plain
    have absurd : (!r) = r := hflip.trans hplain.symm
    cases r <;> simp at absurd
  have pair_certificate (s : Source) (a c : I) (hac : a ≠ c)
      (hax : a ≠ s.1) (hcx : c ≠ s.1) :
      ∃ h, Consistent h s ∧ Sound h s.2 ∧ queryCount h = 2 := by
    refine ⟨[⟨a, s.2⟩, ⟨c, s.2⟩], ?_, ?_, ?_⟩
    · intro p hp
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with rfl | rfl <;> simp [response, hax, hcx]
    · intro t ht
      have hta := ht ⟨a, s.2⟩ (by simp)
      have htc := ht ⟨c, s.2⟩ (by simp)
      by_cases hat : a = t.1
      · have hct : c ≠ t.1 := by intro he; exact hac (hat.trans he.symm)
        simpa [response, hct] using htc
      · simpa [response, hat] using hta
    · simp [queryCount, parameters, hac]
  intro s
  refine ⟨fun h hc hs => singleton_obstruction h s hc hs, ?_⟩
  by_cases hx0 : s.1 = 0
  · exact pair_certificate s midpoint 1 middle_ne_one
      (by simpa [hx0] using middle_ne_zero) (by simpa [hx0] using zero_ne_one.symm)
  by_cases hx1 : s.1 = 1
  · exact pair_certificate s 0 midpoint middle_ne_zero.symm
      (by simpa [hx1] using zero_ne_one) (by simpa [hx1] using middle_ne_one)
  · exact pair_certificate s 0 1 zero_ne_one (Ne.symm hx0) (Ne.symm hx1)

end

end D5.S3.ConceptDynamics.Decision.ExactRealProbeCosts
