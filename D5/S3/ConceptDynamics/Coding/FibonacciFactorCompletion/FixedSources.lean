/- GID: D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/FixedSources
   generality: G
   mirror-B: D5/B/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/FixedSources
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Fixed literal tails supply every history and common-stem operation counts. -/

import D5.S3.ConceptDynamics.Coding.DecoderOperationTrace
import D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Instances.Discrete
import Mathlib.Topology.Constructions
import Mathlib.Data.Finset.Card
import Mathlib.Order.Interval.Set.OrdConnected
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Data.Real.ENatENNReal
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Data.EReal.Basic
import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations
import D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry

set_option autoImplicit false

namespace D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedSources

open D5.S3.ConceptDynamics.Coding.FibonacciLiteralSource
open D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.Operations
open D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.TailGeometry
open D5.S3.ConceptDynamics.Coding.DecoderOperationTrace
open Filter Topology
open scoped Topology
set_option maxHeartbeats 1000000

def choiceBlocks {α : Type} (words : Bool → List α) : List Bool → List α
  | [] => []
  | i :: zs => words i ++ choiceBlocks words zs

theorem choice_lengths (R : Bool → List Label) (W : Bool → List Color)
    (hlen : ∀ i, (R i).length = (W i).length) (zs : List Bool) :
    (choiceBlocks R zs).length = (choiceBlocks W zs).length := by
  induction zs with
  | nil => rfl
  | cons i zs ih => simp only [choiceBlocks, List.length_append, hlen, ih]

theorem legal_append (s e q : Guard) (u v : List Label)
    (hu : LegalWord s e u) (hv : LegalWord e q v) : LegalWord s q (u ++ v) := by
  induction u generalizing s with
  | nil =>
    have hse : s = e := by simpa [LegalWord, walk] using hu
    simpa [hse] using hv
  | cons l u ih =>
    cases hn : nextGuard s l with
    | none => simp [LegalWord, walk, hn] at hu
    | some s' =>
      have hu' : LegalWord s' e u := by simpa [LegalWord, walk, hn] using hu
      simpa [LegalWord, walk, hn] using ih s' hu'

theorem choices_legal (s : Guard) (R : Bool → List Label)
    (hR : ∀ i, LegalWord s s (R i)) (zs : List Bool) :
    LegalWord s s (choiceBlocks R zs) := by
  induction zs with
  | nil => rfl
  | cons i zs ih => exact legal_append s s s (R i) _ (hR i) ih

private theorem choices_interior (R : Bool → List Label) (lo hi : ℝ)
    (invariant : ∀ i z, lo ≤ z → z ≤ hi → lo ≤ compose (R i) z ∧ compose (R i) z ≤ hi)
    (x : ℝ) (hxlo : lo < x) (hxhi : x < hi) (zs : List Bool) :
    lo < compose (choiceBlocks R zs) x ∧ compose (choiceBlocks R zs) x < hi := by
  induction zs with
  | nil => exact ⟨hxlo, hxhi⟩
  | cons i zs ih =>
    have width : lo ≤ hi := (hxlo.trans hxhi).le
    have h := compose_strict_inside (R i) lo hi (compose (choiceBlocks R zs) x) lo hi
      ih.1 ih.2 (invariant i lo le_rfl width) (invariant i hi width le_rfl)
    simpa only [choiceBlocks, literal_source_geometry.2.2.2.2] using h

private theorem choices_actual_slots (o : Ownership) (θ : ℝ) (hθ : 0 ≤ θ)
    (lo hi : ℝ) (R : Bool → List Label) (W : Bool → List Color)
    (hlen : ∀ i, (R i).length = (W i).length)
    (invariant : ∀ i z, lo ≤ z → z ≤ hi → lo ≤ compose (R i) z ∧ compose (R i) z ≤ hi)
    (cert : ∀ i, EndpointCertificate θ lo hi (R i) (W i))
    (x : ℝ) (hxlo : lo < x) (hxhi : x < hi) (zs : List Bool) :
    BlockSupply o θ false (choiceBlocks R zs) (choiceBlocks W zs) x := by
  induction zs with
  | nil => intro r hr; simp [choiceBlocks] at hr
  | cons i zs ih =>
    have hinside := choices_interior R lo hi invariant x hxlo hxhi zs
    exact block_supply_append o θ (R i) _ (W i) _ (hlen i) x
      (certificate_actual_slots o θ hθ lo hi (R i) (W i) (cert i) _ hinside.1 hinside.2) ih

/-- One finite history followed by the literal zero-error future of the same fixed tail. -/
noncomputable def recordWithTail (o : Ownership) (cs : List Color) (w : List Label)
    (p : ℕ) : Color :=
  if hp : p < cs.length then cs[p] else observe o (coordinate w (p - cs.length)) 0

private theorem actual_prefix_record (o : Ownership) (θ : ℝ) (hθ : 0 ≤ θ)
    (s e : Guard) (A : List Label) (cs : List Color) (hlen : A.length = cs.length)
    (hA : LegalWord .G0 s A) (w : List Label) (hw : LegalWord s e w)
    (supply : BlockSupply o θ false A cs (coordinate w 0)) :
    OperationRecord o θ .closed (address (A ++ w)) (recordWithTail o cs w) ∧
      OperationFiniteSource (address (A ++ w)) := by
  classical
  have legal := legal_append .G0 s e A w hA hw
  obtain ⟨path, hp0, hedge, hsupp, hrec⟩ := literal_address_path .G0 e (A ++ w) legal
  have supplied (j : Fin cs.length) : ∃ error : ℝ,
      |error| ≤ θ ∧ observe o (compose (A.drop j.val) (coordinate w 0)) error = cs[j.val] := by
    simpa only [Bool.false_eq_true, if_false] using supply j.val j.isLt
  choose error hbound hcolor using supplied
  let errors : ℕ → ℝ := fun p => if hp : p < cs.length then error ⟨p, hp⟩ else 0
  have past (p : ℕ) (hp : p < cs.length) :
      coordinate (A ++ w) p = compose (A.drop p) (coordinate w 0) := by
    have hp' : p ≤ A.length := by omega
    simp only [coordinate, List.drop_append_of_le_length hp',
      literal_source_geometry.2.2.2.2, List.drop_zero]
  have future (p : ℕ) (hp : cs.length ≤ p) :
      coordinate (A ++ w) p = coordinate w (p - cs.length) := by
    have hp' : A.length ≤ p := by omega
    simp only [coordinate, List.drop_append, List.drop_eq_nil_of_le hp', List.nil_append, hlen]
  refine ⟨⟨coordinate (A ++ w), ⟨path, hp0, hedge, hsupp, hrec⟩, errors, ?_, ?_⟩, ?_⟩
  · intro p
    by_cases hp : p < cs.length
    · simpa only [errors, dif_pos hp] using hbound ⟨p, hp⟩
    · simpa only [errors, dif_neg hp, abs_zero] using hθ
  · intro p
    by_cases hp : p < cs.length
    · simpa only [recordWithTail, dif_pos hp, errors, past p hp] using hcolor ⟨p, hp⟩
    · simp only [recordWithTail, dif_neg hp, errors, future p (le_of_not_gt hp)]
  · refine ⟨(A ++ w).length, ?_⟩
    intro p hp
    simp only [address, List.getElem?_eq_none hp, Option.getD_none]

/-- The finite endpoint certificate constructs one fixed finite actual tail
serving every finite choice history. It does not assume any record family. -/
theorem fixed_finite_tail_all_histories
    (o : Ownership) (θ : ℝ) (hθ : 0 ≤ θ)
    (s : Guard) (P : List Label) (h : List Color) (hP : LegalWord .G0 s P)
    (hPlen : P.length = h.length)
    (R : Bool → List Label) (W : Bool → List Color)
    (hR : ∀ i, LegalWord s s (R i)) (hlen : ∀ i, (R i).length = (W i).length)
    (lo hi : ℝ) (hwidth : lo < hi)
    (hsupport : ∀ z ∈ Set.Icc lo hi, InSupport s z)
    (invariant : ∀ i z, lo ≤ z → z ≤ hi → lo ≤ compose (R i) z ∧ compose (R i) z ≤ hi)
    (stemCert : EndpointCertificate θ lo hi P h)
    (returnCert : ∀ i, EndpointCertificate θ lo hi (R i) (W i)) :
    ∃ (e : Guard) (w : List Label), LegalWord s e w ∧
      lo < coordinate w 0 ∧ coordinate w 0 < hi ∧
      ∀ zs : List Bool,
        OperationRecord o θ .closed (address ((P ++ choiceBlocks R zs) ++ w))
          (recordWithTail o (h ++ choiceBlocks W zs) w) ∧
        OperationFiniteSource (address ((P ++ choiceBlocks R zs) ++ w)) ∧
        ∀ p, recordWithTail o (h ++ choiceBlocks W zs) w
          ((h ++ choiceBlocks W zs).length + p) = observe o (coordinate w p) 0 := by
  obtain ⟨e, w, hw, hxlo, hxhi, hfinite, hpath⟩ :=
    finite_tail_interior s lo hi hwidth hsupport
  refine ⟨e, w, hw, hxlo, hxhi, ?_⟩
  intro zs
  have inside := choices_interior R lo hi invariant (coordinate w 0) hxlo hxhi zs
  have stemSupply := certificate_actual_slots o θ hθ lo hi P h stemCert _ inside.1 inside.2
  have returnSupply := choices_actual_slots o θ hθ lo hi R W hlen invariant returnCert
    (coordinate w 0) hxlo hxhi zs
  have allSupply := block_supply_append o θ P (choiceBlocks R zs) h (choiceBlocks W zs)
    hPlen (coordinate w 0) stemSupply returnSupply
  have allLegal := legal_append .G0 s s P (choiceBlocks R zs) hP (choices_legal s R hR zs)
  have allLength : (P ++ choiceBlocks R zs).length = (h ++ choiceBlocks W zs).length := by
    simp only [List.length_append, hPlen, choice_lengths R W hlen zs]
  obtain ⟨actual, finite⟩ := actual_prefix_record o θ hθ s e (P ++ choiceBlocks R zs)
    (h ++ choiceBlocks W zs) allLength allLegal w hw allSupply
  refine ⟨actual, finite, ?_⟩
  intro p
  have hp : ¬ (h ++ choiceBlocks W zs).length + p < (h ++ choiceBlocks W zs).length := by omega
  simp only [recordWithTail, dif_neg hp, Nat.add_sub_cancel_left]




theorem prefix_coordinates (A : List Label) (beta : ℕ → Label) (X : ℕ → ℝ)
    (z : ℝ) (prefixLabels : ∀ p (hp : p < A.length), beta p = A[p])
    (recurrence : ∀ p, X p = branch (beta p) (X (p+1)))
    (terminal : X A.length = z) :
    ∀ p, p ≤ A.length → X p = compose (A.drop p) z := by
  induction A generalizing beta X with
  | nil =>
    intro p hp
    have hp0 : p = 0 := by simpa using hp
    subst p
    simpa only [List.length_nil, List.drop_nil, compose] using terminal
  | cons l A ih =>
    have hpre : ∀ p (hp : p < A.length), beta (p+1) = A[p] := by
      intro p hp
      have hh := prefixLabels (p+1) (by simp; omega)
      change beta (p+1) = A[p] at hh
      exact hh
    have hend : X (A.length+1) = z := by simpa only [List.length_cons] using terminal
    have ht := ih (fun p => beta (p+1)) (fun p => X (p+1)) hpre
      (fun p => by simpa only [Nat.add_assoc] using recurrence (p+1)) hend
    intro p hp
    cases p with
    | zero =>
      rw [recurrence 0, prefixLabels 0 (by simp), ht 0 (Nat.zero_le _)]
      rfl
    | succ p =>
      simpa only [List.drop_succ_cons, Nat.succ_eq_add_one] using ht p (by simp at hp; omega)

noncomputable def recordWithOmegaTail (o : Ownership) (cs : List Color)
    (x : ℕ → ℝ) (p : ℕ) : Color :=
  if hp : p < cs.length then cs[p] else observe o (x (p-cs.length)) 0

theorem actual_omega_prefix_record (o : Ownership) (θ : ℝ) (hθ : 0 ≤ θ)
    (s : Guard) (A : List Label) (cs : List Color) (hlen : A.length = cs.length)
    (hA : LegalWord .G0 s A)
    (tail : ℕ → Label) (x : ℕ → ℝ) (path : ℕ → Guard)
    (hp0 : path 0 = s)
    (hedge : ∀ p, nextGuard (path p) (tail p) = some (path (p+1)))
    (hsupp : ∀ p, InSupport (path p) (x p))
    (hrec : ∀ p, x p = branch (tail p) (x (p+1)))
    (supply : BlockSupply o θ false A cs (x 0)) :
    ∃ beta X, OperationOmega beta X ∧
      (∀ p (hp : p < A.length), beta p = A[p]) ∧
      (∀ p, beta (A.length+p) = tail p) ∧
      (∀ p, X (A.length+p) = x p) ∧
      OperationRecord o θ .closed beta (recordWithOmegaTail o cs x) := by
  classical
  obtain ⟨beta,X,q,hq0,hX0,he,hs,hr,pre,future,coords⟩ :=
    prepend_legal_tail .G0 s A hA tail x path hp0 hedge hsupp hrec
  have legal : OperationOmega beta X := ⟨q,hq0,he,hs,hr⟩
  have terminal : X A.length = x 0 := by simpa only [Nat.add_zero] using coords 0
  have past := prefix_coordinates A beta X (x 0) pre hr terminal
  have supplied (j : Fin cs.length) : ∃ e : ℝ,
      |e| ≤ θ ∧ observe o (X j.val) e = cs[j.val] := by
    rw [past j.val (by omega)]
    simpa only [Bool.false_eq_true, if_false] using supply j.val j.isLt
  choose error bound color using supplied
  let errors : ℕ → ℝ := fun p => if hp : p < cs.length then error ⟨p,hp⟩ else 0
  refine ⟨beta,X,legal,pre,future,coords,X,legal,errors,?_,?_⟩
  · intro p
    by_cases hp : p < cs.length
    · simpa only [errors,dif_pos hp] using bound ⟨p,hp⟩
    · simpa only [errors,dif_neg hp,abs_zero] using hθ
  · intro p
    by_cases hp : p < cs.length
    · simpa only [recordWithOmegaTail,errors,dif_pos hp] using color ⟨p,hp⟩
    · have hle : A.length ≤ p := by omega
      have hx : X p = x (p-cs.length) := by
        have hh := coords (p-A.length)
        rw [Nat.add_sub_of_le hle] at hh
        simpa only [hlen] using hh
      simp only [recordWithOmegaTail,errors,dif_neg hp,hx]

private theorem compose_identical_choices (V : List Label) (zs : List Bool) (z : ℝ) :
    compose (choiceBlocks (fun _ => V) zs) z = (compose V)^[zs.length] z := by
  induction zs with
  | nil => rfl
  | cons i zs ih =>
    simp only [choiceBlocks,literal_source_geometry.2.2.2.2,List.length_cons,
      Function.iterate_succ_apply',ih]

private theorem identical_choices_slots (o : Ownership) (θ : ℝ) (s : Guard)
    (Q V : List Label) (h : List Color) (W : Bool → List Color)
    (hQ : LegalWord .G0 s Q) (hV : LegalWord s s V)
    (hlen : ∀ i, V.length = (W i).length) (z : ℝ)
    (orbit : ∀ n, (compose V)^[n] z ∈ CompetingT o θ s Q V h W)
    (zs : List Bool) :
    BlockSupply o θ false (choiceBlocks (fun _ => V) zs) (choiceBlocks W zs) z := by
  induction zs with
  | nil => intro r hr; simp [choiceBlocks] at hr
  | cons i zs ih =>
    have ht := (competingT_mem_actual o θ s Q V h W hQ hV _).mp (orbit zs.length)
    have hv : BlockSupply o θ false V (W i)
        (compose (choiceBlocks (fun _ => V) zs) z) := by
      simpa only [compose_identical_choices] using ht.2.2 i
    exact block_supply_append o θ V _ (W i) _ (hlen i) z hv ih

private theorem block_supply_split (o : Ownership) (θ : ℝ)
    (A B : List Label) (h d : List Color) (hlen : A.length = h.length) (z : ℝ)
    (supply : BlockSupply o θ false (A++B) (h++d) z) :
    BlockSupply o θ false A h (compose B z) ∧ BlockSupply o θ false B d z := by
  constructor
  · intro r hr
    have hrall : r < (h++d).length := by simp; omega
    have hs := supply r hrall
    have hrA : r ≤ A.length := by omega
    simpa only [List.getElem_append_left hr,List.drop_append_of_le_length hrA,
      literal_source_geometry.2.2.2.2] using hs
  · intro r hr
    have hrall : h.length+r < (h++d).length := by simp; omega
    have hs := supply (h.length+r) hrall
    have hrge : A.length ≤ h.length+r := by omega
    have hcolor : (h++d)[h.length+r] = d[r] := by
      simpa only [Nat.add_sub_cancel_left] using List.getElem_append_right (by omega : h.length ≤ h.length+r)
    rw [hcolor] at hs
    rw [List.drop_append,List.drop_eq_nil_of_le hrge,List.nil_append] at hs
    simpa only [← hlen,Nat.add_sub_cancel_left] using hs

theorem competingT_orbit_iff_all_histories (o : Ownership) (θ : ℝ) (s : Guard)
    (Q V : List Label) (h : List Color) (W : Bool → List Color)
    (hQ : LegalWord .G0 s Q) (hV : LegalWord s s V)
    (hQlen : Q.length = h.length) (hlen : ∀ i, V.length = (W i).length) (z : ℝ) :
    (∀ n, (compose V)^[n] z ∈ CompetingT o θ s Q V h W) ↔
      InSupport s z ∧ ∀ zs : List Bool,
        BlockSupply o θ false (Q++choiceBlocks (fun _ => V) zs) (h++choiceBlocks W zs) z := by
  constructor
  · intro orbit
    have hz : z ∈ CompetingT o θ s Q V h W := by simpa using orbit 0
    refine ⟨hz.1,?_⟩
    intro zs
    have stem := ((competingT_mem_actual o θ s Q V h W hQ hV _).mp (orbit zs.length)).2.1
    have stem' : BlockSupply o θ false Q h (compose (choiceBlocks (fun _ => V) zs) z) := by
      simpa only [compose_identical_choices] using stem
    exact block_supply_append o θ Q _ h _ hQlen z stem'
      (identical_choices_slots o θ s Q V h W hQ hV hlen z orbit zs)
  · rintro ⟨hz,supplies⟩
    have supported (n : ℕ) : InSupport s ((compose V)^[n] z) := by
      induction n with
      | zero => exact hz
      | succ n ih =>
        rw [Function.iterate_succ_apply']
        exact literal_source_geometry.1 s s V _ hV ih
    intro n
    let zs : List Bool := List.replicate n false
    have hzs : zs.length = n := by simp [zs]
    have hs := (block_supply_split o θ Q _ h _ hQlen z (supplies zs)).1
    have hs' : BlockSupply o θ false Q h ((compose V)^[n] z) := by
      simpa only [compose_identical_choices,hzs] using hs
    apply (competingT_mem_actual o θ s Q V h W hQ hV _).mpr
    refine ⟨supported n,hs',?_⟩
    intro i
    have hs := (block_supply_split o θ Q _ h _ hQlen z (supplies (i::zs))).2
    change BlockSupply o θ false (V++choiceBlocks (fun _ => V) zs) (W i++choiceBlocks W zs) z at hs
    have hv := (block_supply_split o θ V _ (W i) _ (hlen i) z hs).1
    simpa only [compose_identical_choices,hzs] using hv

/-- One lawful competing tail supplies every finite synchronized color history. -/
theorem fixed_omega_tail_all_histories
    (o : Ownership) (θ : ℝ) (hθ : 0 ≤ θ) (s : Guard)
    (Q V : List Label) (h : List Color) (W : Bool → List Color)
    (hQ : LegalWord .G0 s Q) (hV : LegalWord s s V)
    (hQlen : Q.length = h.length) (hlen : ∀ i, V.length = (W i).length)
    (a y : ℝ) (ha : -1 < a) (ha1 : a < 1) (hane : a ≠ 0)
    (hslope : a = (-g)^V.length) (hfixed : compose V y = y)
    (hfeasible : if 0 < a then
      (CompetingT o θ s Q V h W).Nonempty ∧ y ∈ closure (CompetingT o θ s Q V h W)
      else y ∈ CompetingT o θ s Q V h W) :
    ∃ (tail : ℕ → Label) (x : ℕ → ℝ) (path : ℕ → Guard),
      path 0 = s ∧
      (∀ p, nextGuard (path p) (tail p) = some (path (p+1))) ∧
      (∀ p, InSupport (path p) (x p)) ∧
      (∀ p, x p = branch (tail p) (x (p+1))) ∧
      (∀ n, (compose V)^[n] (x 0) ∈ CompetingT o θ s Q V h W) ∧
      ∀ zs : List Bool, ∃ beta X, OperationOmega beta X ∧
        (∀ p (hp : p < (Q ++ choiceBlocks (fun _ => V) zs).length),
          beta p = (Q ++ choiceBlocks (fun _ => V) zs)[p]) ∧
        (∀ p, beta ((Q ++ choiceBlocks (fun _ => V) zs).length+p) = tail p) ∧
        (∀ p, X ((Q ++ choiceBlocks (fun _ => V) zs).length+p) = x p) ∧
        OperationRecord o θ .closed beta (recordWithOmegaTail o (h ++ choiceBlocks W zs) x) := by
  have hF : compose V = (fun z : ℝ => y+a*(z-y)) := by
    funext z
    have affine := literal_source_geometry.2.2.2.1 V y (z-y)
    have hsum : y+(z-y) = z := by ring
    simpa only [hsum,hfixed,← hslope] using affine
  obtain ⟨z,hzOrbit⟩ := (competing_tail_orbit_criterion _
    (competingT_ordConnected o θ hθ s Q V h W) a y ha ha1 hane).2.mpr hfeasible
  have orbit : ∀ n, (compose V)^[n] z ∈ CompetingT o θ s Q V h W := by
    intro n
    rw [hF]
    exact hzOrbit n
  have hzT : z ∈ CompetingT o θ s Q V h W := by simpa using orbit 0
  obtain ⟨tail,x,path,hp0,hx0,he,hs,hr⟩ := lawful_tail s z hzT.1
  refine ⟨tail,x,path,hp0,he,hs,hr,by simpa only [hx0] using orbit,?_⟩
  intro zs
  have supply := ((competingT_orbit_iff_all_histories o θ s Q V h W hQ hV hQlen hlen z).mp orbit).2 zs
  have supply' : BlockSupply o θ false (Q++choiceBlocks (fun _ => V) zs) (h++choiceBlocks W zs) (x 0) := by
    simpa only [hx0] using supply
  have hA := legal_append .G0 s s Q _ hQ (choices_legal s (fun _ => V) (fun _ => hV) zs)
  have hAlen : (Q ++ choiceBlocks (fun _ => V) zs).length = (h ++ choiceBlocks W zs).length := by
    simp only [List.length_append,hQlen,choice_lengths (fun _ => V) W hlen zs]
  exact actual_omega_prefix_record o θ hθ s _ _ hAlen hA tail x path hp0 he hs hr supply'



open D5.S3.ConceptDynamics.Coding.DecoderOperationTrace

private theorem uniform_choice_length {A : Type} (R : Bool → List A)
    (L : ℕ) (hlen : ∀ i, (R i).length = L) (zs : List Bool) :
    (choiceBlocks R zs).length = zs.length * L := by
  induction zs with
  | nil => simp only [choiceBlocks,List.length_nil,Nat.zero_mul]
  | cons i zs ih => simp only [choiceBlocks,List.length_append,hlen,ih,List.length_cons,Nat.succ_mul]; omega

private theorem uniform_choice_injective (R : Bool → List Label) (L : ℕ)
    (hlen : ∀ i, (R i).length = L) (hne : R false ≠ R true)
    (zs ys : List Bool) (hsize : zs.length = ys.length)
    (heq : choiceBlocks R zs = choiceBlocks R ys) : zs = ys := by
  induction zs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons j ys => simp at hsize
  | cons i zs ih =>
    cases ys with
    | nil => simp at hsize
    | cons j ys =>
      have head (i : Bool) (rs : List Bool) :
          (choiceBlocks R (i :: rs)).take L = R i := by
        change (R i ++ choiceBlocks R rs).take L = R i
        rw [← hlen i]
        exact List.take_left
      have hij : R i = R j := by
        calc R i = (choiceBlocks R (i :: zs)).take L := (head i zs).symm
             _ = (choiceBlocks R (j :: ys)).take L := congrArg (List.take L) heq
             _ = R j := head j ys
      have hchoice : i = j := by
        cases i <;> cases j
        · rfl
        · exact False.elim (hne hij)
        · exact False.elim (hne hij.symm)
        · rfl
      subst j
      have tail : choiceBlocks R zs = choiceBlocks R ys :=
        List.append_cancel_left (by simpa only [choiceBlocks] using heq)
      exact congrArg (List.cons i) (ih ys (by simpa only [List.length_cons,Nat.succ_inj] using hsize) tail)

def synchronousPrefix {A : Type} (P : List A) (R : Bool → List A)
    {n : ℕ} (z : Fin n → Bool) : List A := P ++ choiceBlocks R (List.ofFn z)

theorem synchronous_length {A : Type} (P : List A) (R : Bool → List A)
    (L : ℕ) (hlen : ∀ i, (R i).length = L) (n : ℕ) (z : Fin n → Bool) :
    (synchronousPrefix P R z).length = P.length + n*L := by
  simp only [synchronousPrefix,List.length_append,uniform_choice_length R L hlen,List.length_ofFn]

theorem address_prefix (A w : List Label) (p : ℕ) (hp : p < A.length) :
    address (A ++ w) p = A[p] := by
  have htotal : p < (A ++ w).length := by simp; omega
  simp only [address,List.getElem?_eq_getElem htotal,Option.getD_some,List.getElem_append_left hp]

theorem synchronous_address_injective (P : List Label) (R : Bool → List Label)
    (L : ℕ) (hlen : ∀ i, (R i).length = L) (hne : R false ≠ R true)
    (w : List Label) (n : ℕ) :
    Function.Injective (fun z : Fin n → Bool => address (synchronousPrefix P R z ++ w)) := by
  intro z z' heq
  have hsize : (synchronousPrefix P R z).length = (synchronousPrefix P R z').length := by
    rw [synchronous_length P R L hlen n z,synchronous_length P R L hlen n z']
  have hpref : synchronousPrefix P R z = synchronousPrefix P R z' := by
    apply List.ext_getElem hsize
    intro p hp hp'
    calc (synchronousPrefix P R z)[p] = address (synchronousPrefix P R z ++ w) p :=
           (address_prefix _ w p hp).symm
         _ = address (synchronousPrefix P R z' ++ w) p := congrFun heq p
         _ = (synchronousPrefix P R z')[p] := address_prefix _ w p hp'
  have blocks : choiceBlocks R (List.ofFn z) = choiceBlocks R (List.ofFn z') :=
    List.append_cancel_left hpref
  apply List.ofFn_injective
  exact uniform_choice_injective R L hlen hne _ _ (by simp) blocks

private theorem zero_record (o : Ownership) (θ : ℝ) (hθ : 0 ≤ θ)
    (e : Guard) (w : List Label) (hw : LegalWord .G0 e w) :
    OperationRecord o θ .closed (address w) (fun p => observe o (coordinate w p) 0) ∧
      OperationFiniteSource (address w) := by
  obtain ⟨path,hp0,he,hs,hr⟩ := literal_address_path .G0 e w hw
  refine ⟨⟨coordinate w,⟨path,hp0,he,hs,hr⟩,(fun _ => 0),?_,?_⟩,w.length,?_⟩
  · intro p
    simpa only [abs_zero] using hθ
  · intro p
    rfl
  · intro p hp
    simp only [address,List.getElem?_eq_none hp,Option.getD_none]

/-- Actual synchronized sources give the original arbitrary common-stem factor.
The finite hull and endpoint data are numerical inputs, not record or injection inputs. -/
theorem original_synchronous_common_stem {Configuration : Type*}
    (action : Configuration → Op Configuration Color Label) (initialConfiguration : Configuration)
    (o : Ownership) (θ : ℝ) (hθ : 0 ≤ θ)
    (s1 s2 : Guard) (P Q : List Label) (h : List Color)
    (hP : LegalWord .G0 s1 P) (hQ : LegalWord .G0 s2 Q)
    (hPlen : P.length = h.length) (hQlen : Q.length = h.length)
    (U : Bool → List Label) (V : List Label) (W : Bool → List Color)
    (L : ℕ) (hU : ∀ i, LegalWord s1 s1 (U i))
    (hV : LegalWord s2 s2 V) (hUlen : ∀ i, (U i).length = L)
    (hVlen : V.length = L) (hUWlen : ∀ i, (U i).length = (W i).length)
    (differentReturns : U false ≠ U true)
    (lo hi : ℝ) (hwidth : lo < hi)
    (hsupport : ∀ z ∈ Set.Icc lo hi, InSupport s1 z)
    (invariant : ∀ i z, lo ≤ z → z ≤ hi → lo ≤ compose (U i) z ∧ compose (U i) z ≤ hi)
    (stemCert : EndpointCertificate θ lo hi P h)
    (returnCert : ∀ i, EndpointCertificate θ lo hi (U i) (W i))
    (a y : ℝ) (ha : -1 < a) (ha1 : a < 1) (hane : a ≠ 0)
    (hslope : a = (-g)^V.length) (hfixed : compose V y = y)
    (hfeasible : if 0 < a then
      (CompetingT o θ s2 Q V h W).Nonempty ∧ y ∈ closure (CompetingT o θ s2 Q V h W)
      else y ∈ CompetingT o θ s2 Q V h W)
    (k : ℕ) (hk : k < P.length)
    (sameStem : ∀ p (hp : p < k), P[p] = Q[p]'(by omega))
    (differentStem : P[k] ≠ Q[k]'(by omega))
    (safety : ∀ alpha r, OperationRecord o θ .closed alpha r → ∀ t,
      Run action (full r) ⟨initialConfiguration,0,[]⟩ t →
      ∀ p (hp : p < t.output.length), t.output[p] = alpha p)
    (liveness : ∀ alpha r, OperationRecord o θ .closed alpha r → OperationFiniteSource alpha → ∀ p,
      ∃ t, Run action (full r) ⟨initialConfiguration,0,[]⟩ t ∧ p < t.output.length)
    (postprocessing : ∀ alpha r, OperationRecord o θ .closed alpha r →
      ∀ (c d : Configuration) (q : ℕ) (out batch : List Label)
      (f : Color → Option (Configuration × List Label)),
      Run action (full r) ⟨initialConfiguration,0,[]⟩ ⟨c,q,out⟩ →
      action c = .acquire f → f (r q) = some (d,batch) →
      ∃ t, Drain action ⟨d,q+1,out++batch⟩ t) :
    ∃ (e : Guard) (w : List Label) (eta : ℕ → Label) (x : ℕ → ℝ),
      LegalWord s1 e w ∧ lo < coordinate w 0 ∧ coordinate w 0 < hi ∧
      ∀ n : ℕ, ∃ (beta : (Fin n → Bool) → ℕ → Label)
        (cuts : (Fin n → Bool) → Frame Configuration Label) (states : Finset Configuration),
        (∀ (z : Fin n → Bool), OperationRecord o θ .closed
          (address (synchronousPrefix P U z ++ w))
          (recordWithTail o (synchronousPrefix h W z) w) ∧
          OperationFiniteSource (address (synchronousPrefix P U z ++ w))) ∧
        (∀ (z : Fin n → Bool), OperationRecord o θ .closed (beta z)
          (recordWithOmegaTail o (synchronousPrefix h W z) x)) ∧
        (∀ (z : Fin n → Bool) p (hp : p < (synchronousPrefix Q (fun _ => V) z).length),
          beta z p = (synchronousPrefix Q (fun _ => V) z)[p]) ∧
        (∀ (z : Fin n → Bool) p, beta z (P.length+n*L+p) = eta p) ∧
        (∀ (z : Fin n → Bool) p, recordWithTail o (synchronousPrefix h W z) w (P.length+n*L+p) =
          observe o (coordinate w p) 0) ∧
        Function.Injective (fun z : Fin n → Bool => address (synchronousPrefix P U z ++ w)) ∧
        (∀ (z : Fin n → Bool), Cut action initialConfiguration
          (front (recordWithTail o (synchronousPrefix h W z) w) (P.length+n*L)) (cuts z) ∧
          (cuts z).output.length ≤ k ∧
          (cuts z).output = (P.take k).take (cuts z).output.length ∧
          (cuts z).output <+: P.take k) ∧
        Function.Injective (fun z => ((cuts z).state,(cuts z).output)) ∧
        (∀ c, c ∈ states ↔ ∃ z, (cuts z).state = c) ∧
        2^n ≤ states.card*(k+1) := by
  classical
  have vWlen : ∀ i, V.length = (W i).length := fun i =>
    hVlen.trans ((hUlen i).symm.trans (hUWlen i))
  have wLen : ∀ i, (W i).length = L := fun i => (hUWlen i).symm.trans (hUlen i)
  obtain ⟨e,w,hw,hxlo,hxhi,highAll⟩ := fixed_finite_tail_all_histories o θ hθ
    s1 P h hP hPlen U W hU hUWlen lo hi hwidth hsupport invariant stemCert returnCert
  obtain ⟨eta,x,path,hp0,he,hs,hr,orbit,lowAll⟩ := fixed_omega_tail_all_histories
    o θ hθ s2 Q V h W hQ hV hQlen vWlen a y ha ha1 hane hslope hfixed hfeasible
  have z0 := zero_record o θ hθ .G0 [.L0] (by rfl)
  have z3 := zero_record o θ hθ .G0 [.L3] (by rfl)
  have processing := processing_of_safe_live_pair action initialConfiguration
    (OperationRecord o θ .closed) OperationFiniteSource safety liveness
    (address [.L0]) (address [.L3])
    (fun p => observe o (coordinate [.L0] p) 0) (fun p => observe o (coordinate [.L3] p) 0)
    z0.1 z3.1 z0.2 (by simp [address]) postprocessing
  refine ⟨e,w,eta,x,hw,hxlo,hxhi,?_⟩
  intro n
  choose beta X lowOmega lowPrefix lowFuture lowCoordinates lowRecord using lowAll
  let alpha : (Fin n → Bool) → ℕ → Label := fun z => address (synchronousPrefix P U z ++ w)
  let hRecord : (Fin n → Bool) → ℕ → Color := fun z => recordWithTail o (synchronousPrefix h W z) w
  let lRecord : (Fin n → Bool) → ℕ → Color := fun z => recordWithOmegaTail o (synchronousPrefix h W z) x
  have colorLength (z : Fin n → Bool) : (synchronousPrefix h W z).length = P.length+n*L := by
    rw [synchronous_length h W L wLen n z,← hPlen]
  have lowLength (z : Fin n → Bool) : (synchronousPrefix Q (fun _ => V) z).length = P.length+n*L := by
    rw [synchronous_length Q (fun _ => V) L (fun _ => hVlen) n z]
    omega
  have actualHigh (z : Fin n → Bool) : OperationRecord o θ .closed (alpha z) (hRecord z) ∧
      OperationFiniteSource (alpha z) := (highAll (List.ofFn z)).1 |> fun hrec =>
        ⟨hrec,(highAll (List.ofFn z)).2.1⟩
  have actualLow (z : Fin n → Bool) : OperationRecord o θ .closed (beta (List.ofFn z)) (lRecord z) :=
    lowRecord (List.ofFn z)
  have past (z : Fin n → Bool) (p : ℕ) (hp : p < P.length+n*L) : hRecord z p = lRecord z p := by
    have hpcs : p < (synchronousPrefix h W z).length := by rw [colorLength]; exact hp
    simp only [hRecord,lRecord,recordWithTail,recordWithOmegaTail,dif_pos hpcs]
  have futureLiteral (z : Fin n → Bool) (p : ℕ) : hRecord z (P.length+n*L+p) = observe o (coordinate w p) 0 := by
    have hh := (highAll (List.ofFn z)).2.2 p
    change recordWithTail o (synchronousPrefix h W z) w (P.length+n*L+p) = _
    rw [← colorLength z]
    exact hh
  have future (z z' : Fin n → Bool) (p : ℕ) : hRecord z (P.length+n*L+p) = hRecord z' (P.length+n*L+p) :=
    (futureLiteral z p).trans (futureLiteral z' p).symm
  have alphaAt (z : Fin n → Bool) (p : ℕ) (hp : p < P.length) : alpha z p = P[p] := by
    have hpa : p < (synchronousPrefix P U z).length := by simp only [synchronousPrefix,List.length_append]; omega
    simpa only [alpha,synchronousPrefix,List.getElem_append_left hp] using address_prefix _ w p hpa
  have betaAt (z : Fin n → Bool) (p : ℕ) (hp : p < Q.length) : beta (List.ofFn z) p = Q[p] := by
    have hpb : p < (synchronousPrefix Q (fun _ => V) z).length := by simp only [synchronousPrefix,List.length_append]; omega
    have hh := lowPrefix (List.ofFn z) p hpb
    change beta (List.ofFn z) p = (Q ++ choiceBlocks (fun _ => V) (List.ofFn z))[p] at hh
    exact hh.trans (List.getElem_append_left hp)
  have takeLength : (P.take k).length = k := by simp only [List.length_take,Nat.min_eq_left hk.le]
  have stemHigh (z : Fin n → Bool) (p : ℕ) (hp : p < (P.take k).length) : alpha z p = (P.take k)[p] := by
    have hpP : p < P.length := by rw [takeLength] at hp; omega
    simpa only [List.getElem_take] using alphaAt z p hpP
  have stemLow (z : Fin n → Bool) (p : ℕ) (hp : p < (P.take k).length) : beta (List.ofFn z) p = (P.take k)[p] := by
    have hpk : p < k := by rw [takeLength] at hp; exact hp
    have hpQ : p < Q.length := by omega
    calc beta (List.ofFn z) p = Q[p] := betaAt z p hpQ
         _ = P[p] := (sameStem p hpk).symm
         _ = (P.take k)[p] := by simp only [List.getElem_take]
  have different (z : Fin n → Bool) : alpha z (P.take k).length ≠ beta (List.ofFn z) (P.take k).length := by
    rw [takeLength,alphaAt z k hk,betaAt z k (by omega)]
    exact differentStem
  have inj := synchronous_address_injective P U L hUlen differentReturns w n
  obtain ⟨cuts,states,hcuts,joint,membership,count⟩ := original_operation_common_stem
    action initialConfiguration o θ .closed processing safety liveness alpha
    (fun z => beta (List.ofFn z)) hRecord lRecord (P.length+n*L) (P.take k)
    actualHigh actualLow past future stemHigh stemLow different inj
  refine ⟨fun z => beta (List.ofFn z),cuts,states,actualHigh,actualLow,?_,?_,futureLiteral,inj,?_,joint,membership,?_⟩
  · intro z p hp
    exact lowPrefix (List.ofFn z) p hp
  · intro z p
    have hh := lowFuture (List.ofFn z) p
    change beta (List.ofFn z) ((synchronousPrefix Q (fun _ => V) z).length+p) = eta p at hh
    rw [lowLength z] at hh
    exact hh
  · intro z
    simpa only [takeLength] using hcuts z
  · simpa only [Nat.card_eq_fintype_card,Fintype.card_fun,Fintype.card_fin,Fintype.card_bool,takeLength] using count



end D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion.FixedSources
