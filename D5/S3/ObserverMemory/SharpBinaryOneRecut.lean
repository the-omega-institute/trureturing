/- GID: D5/S3/ObserverMemory/SharpBinaryOneRecut
   generality: G
   mirror-B: D5/B/S3/ObserverMemory/SharpBinaryOneRecut
   mirror-E: none(waiver:symbolic-finite-relation-family)
   anchors: []
   utility: none
   digest: Binary recut fibers attain sharp bounds at every positive forward width. -/

import D5.S3.ObserverMemory.StrictAnchoredBoundary
import Mathlib.Data.List.OfFn
import Mathlib.Data.Fintype.Option
import Mathlib.Data.Fintype.BigOperators

/-! Actual binary recut bounds and exhaustive optional-index realizations. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Classical
namespace D5.S3.ObserverMemory.SharpBinaryOneRecut
open StrictAnchoredBoundary

abbrev Boundary := Set (List Bool) × List Bool
def derivative (S : Set (List Bool)) (b : Bool) : Set (List Bool) := {f | b :: f ∈ S}
def recut (z : Boundary) : Set (List Bool) := {f | z.2 ++ f ∈ z.1}
def currentFiber (C : Set (List Bool)) (k : Nat) (E : Set (List Bool)) : Set Boundary :=
  {z | z ∈ image C (k, 1) ∧ recut z = E}
def fixedBitFiber (C : Set (List Bool)) (k : Nat) (E : Set (List Bool)) (b : Bool) : Set Boundary :=
  {z | z ∈ currentFiber C k E ∧ z.2 = [b]}
def FullBranching (C : Set (List Bool)) (k : Nat) : Prop :=
  ∀ v : List Bool, v.length = k - 1 → (∃ f, v ++ f ∈ C) →
    ∀ b : Bool, ∃ f, (v ++ [b]) ++ f ∈ C

private theorem residual_finite (C : Set (List Bool)) (k : Nat) : (residualSet C k).Finite := by
  apply ((List.finite_length_eq Bool k).image (residual C)).subset
  rintro S ⟨v,hv,_,rfl⟩
  exact ⟨v,hv,rfl⟩

private theorem residual_nonempty (n : Nat) (C : Set (List Bool))
    (hl : ∀ w ∈ C, w.length = n) (hc : C.Nonempty) (k : Nat) (hk : k ≤ n) :
    (residualSet C k).Nonempty := by
  obtain ⟨w,hw⟩ := hc
  refine ⟨residual C (w.take k),w.take k,?_,?_,rfl⟩
  · simp [List.length_take,hl w hw,Nat.min_eq_left hk]
  · exact ⟨w.drop k,by simpa using hw⟩

private theorem residual_not_empty {C : Set (List Bool)} {k : Nat}
    {S : Set (List Bool)} (h : S ∈ residualSet C k) : S.Nonempty := by
  obtain ⟨v,_,⟨f,hf⟩,rfl⟩ := h
  exact ⟨f,hf⟩

private theorem shift (C : Set (List Bool)) (v : List Bool) (b : Bool) :
    residual C (v ++ [b]) = derivative (residual C v) b := by
  ext f; simp [StrictAnchoredBoundary.residual,derivative,List.append_assoc]

private theorem derivative_member {C : Set (List Bool)} {k : Nat} (hk : 1 ≤ k)
    {S : Set (List Bool)} (hS : S ∈ residualSet C (k - 1)) (b : Bool) :
    derivative S b = ∅ ∨ derivative S b ∈ residualSet C k := by
  by_cases he : derivative S b = ∅
  · exact Or.inl he
  · obtain ⟨f,hf⟩ := Set.nonempty_iff_ne_empty.mpr he
    obtain ⟨v,hv,_,rfl⟩ := hS
    refine Or.inr ⟨v ++ [b],?_,?_,shift C v b⟩
    · simp only [List.length_append,List.length_singleton]; omega
    · exact ⟨f,by simpa [derivative,StrictAnchoredBoundary.residual,List.append_assoc] using hf⟩

private theorem derivative_full {C : Set (List Bool)} {k : Nat} (hk : 1 ≤ k)
    (hb : FullBranching C k) {S : Set (List Bool)} (hS : S ∈ residualSet C (k - 1)) (b : Bool) :
    derivative S b ∈ residualSet C k := by
  obtain ⟨v,hv,hvC,rfl⟩ := hS
  refine ⟨v ++ [b],?_,hb v hv hvC b,shift C v b⟩
  simp only [List.length_append,List.length_singleton]; omega

private theorem image_data (n : Nat) (C : Set (List Bool))
    (hl : ∀ w ∈ C, w.length = n) (hc : C.Nonempty) (k : Nat) (hk : 1 ≤ k) (hkn : k ≤ n)
    {z : Boundary} (hz : z ∈ image C (k, 1)) :
    z.1 ∈ residualSet C (k - 1) ∧ z.2 = [z.2.headD false] ∧ recut z ∈ residualSet C k := by
  have hi := (strict_anchored_specialization n C hl hc k 1 hk hkn).2.2.1
  rw [hi] at hz
  rcases hz with ⟨hS,ht,⟨f,hf⟩⟩
  have ht' : z.2 = [z.2.headD false] := by
    cases h : z.2 with
    | nil => simp [h] at ht
    | cons b t =>
      have he : t = [] := by simpa [h] using ht
      simp [h,he]
  refine ⟨hS,ht',?_⟩
  have hd : recut z = derivative z.1 (z.2.headD false) := by rw [recut,ht']; rfl
  rw [hd]
  rcases derivative_member hk hS (z.2.headD false) with he | he
  · rw [ht'] at hf
    have hf' : f ∈ derivative z.1 (z.2.headD false) := hf
    rw [he] at hf'
    exact hf'.elim
  · exact he

private theorem previous_no_nil {n k : Nat} {C : Set (List Bool)}
    (hl : ∀ w ∈ C, w.length = n) (hk : 1 ≤ k) (hkn : k ≤ n)
    {S : Set (List Bool)} (hS : S ∈ residualSet C (k - 1)) : [] ∉ S := by
  obtain ⟨v,hv,_,rfl⟩ := hS
  intro h
  have he := hl _ h
  simp only [List.append_nil] at he
  omega

private theorem derivative_ext {S T : Set (List Bool)} (hS : [] ∉ S) (hT : [] ∉ T)
    (b : Bool) (hb : derivative S b = derivative T b)
    (ho : derivative S (!b) = derivative T (!b)) : S = T := by
  ext f
  cases f with
  | nil => simp [hS,hT]
  | cons c f =>
    have he : derivative S c = derivative T c := by cases b <;> cases c <;> assumption
    exact Set.ext_iff.mp he f

private theorem image_injective (n : Nat) (C : Set (List Bool))
    (hl : ∀ w ∈ C, w.length = n) (hc : C.Nonempty) (k : Nat) (hk : 1 ≤ k) (hkn : k ≤ n)
    {z w : Boundary} (hz : z ∈ image C (k, 1)) (hw : w ∈ image C (k, 1))
    (hr : recut z = recut w) (hb : z.2.headD false = w.2.headD false)
    (ho : derivative z.1 (!z.2.headD false) = derivative w.1 (!w.2.headD false)) : z = w := by
  obtain ⟨hzS,hzt,_⟩ := image_data n C hl hc k hk hkn hz
  obtain ⟨hwS,hwt,_⟩ := image_data n C hl hc k hk hkn hw
  have ht : z.2 = w.2 := by rw [hzt,hwt,hb]
  apply Prod.ext ?_ ht
  apply derivative_ext (previous_no_nil hl hk hkn hzS) (previous_no_nil hl hk hkn hwS)
    (z.2.headD false)
  · have hz : recut z = derivative z.1 (z.2.headD false) := by
      unfold recut; rw [hzt]; rfl
    have hw : recut w = derivative w.1 (w.2.headD false) := by
      unfold recut; rw [hwt]; rfl
    rw [hz,hw,← hb] at hr
    exact hr
  · simpa only [hb] using ho

private theorem bounds_with (n : Nat) (C : Set (List Bool))
    (hl : ∀ w ∈ C, w.length = n) (hc : C.Nonempty) (k : Nat) (hk : 1 ≤ k) (hkn : k ≤ n)
    (B : Set (Set (List Bool))) (hB : B.Finite)
    (hder : ∀ S ∈ residualSet C (k - 1), ∀ b, derivative S b ∈ B) :
    (∀ E, Nat.card (currentFiber C k E) ≤ 2 * Nat.card B ∧
      ∀ b, Nat.card (fixedBitFiber C k E b) ≤ Nat.card B) ∧
    Nat.card (image C (k, 1)) ≤ 2 * Nat.card (residualSet C k) * Nat.card B := by
  letI := hB.fintype
  letI := (residual_finite C k).fintype
  let opposite : image C (k, 1) → B := fun z =>
    ⟨derivative z.val.1 (!z.val.2.headD false),
      hder _ (image_data n C hl hc k hk hkn z.property).1 _⟩
  have inj : Function.Injective (fun z : image C (k, 1) =>
      ((⟨recut z.val,(image_data n C hl hc k hk hkn z.property).2.2⟩ : residualSet C k),
        z.val.2.headD false,opposite z)) := by
    intro z w he
    apply Subtype.ext
    exact image_injective n C hl hc k hk hkn z.property w.property
      (congrArg (fun p => p.1.val) he) (congrArg (fun p => p.2.1) he)
      (congrArg (fun p => p.2.2.val) he)
  constructor
  · intro E
    constructor
    · let f : currentFiber C k E → Bool × B := fun z =>
        (z.val.2.headD false,opposite ⟨z.val,z.property.1⟩)
      have hf : Function.Injective f := by
        intro z w he; apply Subtype.ext
        exact image_injective n C hl hc k hk hkn z.property.1 w.property.1
          (z.property.2.trans w.property.2.symm) (congrArg Prod.fst he)
          (congrArg (fun p => p.2.val) he)
      simpa [Nat.card_prod] using Nat.card_le_card_of_injective f hf
    · intro b
      let f : fixedBitFiber C k E b → B := fun z => opposite ⟨z.val,z.property.1.1⟩
      have hf : Function.Injective f := by
        intro z w he; apply Subtype.ext
        exact image_injective n C hl hc k hk hkn z.property.1.1 w.property.1.1
          (z.property.1.2.trans w.property.1.2.symm)
          (congrArg (fun t : List Bool => t.headD false) (z.property.2.trans w.property.2.symm))
          (congrArg Subtype.val he)
      exact Nat.card_le_card_of_injective f hf
  · have he := Nat.card_le_card_of_injective _ inj
    simpa [Nat.card_prod,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using he

def word {N : Nat} (i : Option (Fin N)) : List Bool :=
  List.ofFn (fun t : Fin N => decide (i = some t))
def payload {N : Nat} (i : Option (Fin N)) : Set (List Bool) :=
  {f | ∃ s, i = some s ∧ f = word (some s)}
def predecessor {N : Nat} (i j : Option (Fin N)) : Set (List Bool) :=
  {f | (∃ s, i = some s ∧ f = false :: word (some s)) ∨
    (∃ s, j = some s ∧ f = true :: word (some s))}
def anchor {N : Nat} (i j : Option (Fin N)) : List Bool := word i ++ word j
abbrev Spare (N : Nat) (full : Bool) := {i : Option (Fin N) // full = true → i ≠ none}
abbrev Point (N : Nat) (full : Bool) := Fin N × Bool × Spare N full
def indices {N : Nat} {full : Bool} (p : Point N full) : Option (Fin N) × Option (Fin N) :=
  if p.2.1 then (p.2.2.val,some p.1) else (some p.1,p.2.2.val)
def fine {N : Nat} {full : Bool} (p : Point N full) : Boundary :=
  (predecessor (indices p).1 (indices p).2,[p.2.1])
def selectorPrefix {N : Nat} {full : Bool} (p : Point N full) : List Bool :=
  anchor (indices p).1 (indices p).2 ++ [p.2.1]
def code {N : Nat} {full : Bool} (p : Point N full) : List Bool :=
  selectorPrefix p ++ word (some p.1)
def relation (N : Nat) (full : Bool) : Set (List Bool) := Set.range (@code N full)
def Admissible {N : Nat} (full : Bool) (i j : Option (Fin N)) : Prop :=
  (i ≠ none ∨ j ≠ none) ∧ (full = true → i ≠ none ∧ j ≠ none)

private theorem word_length {N : Nat} (i : Option (Fin N)) : (word i).length = N := by
  simp [word]
private theorem word_injective (N : Nat) : Function.Injective (@word N) := by
  intro i j h
  have he := List.ofFn_injective h
  cases i with
  | none =>
    cases j with
    | none => rfl
    | some t => have hh := congrFun he t; simp at hh
  | some s =>
    have hh := congrFun he s
    cases j with
    | none => simp at hh
    | some t =>
      by_contra hn
      have hst : s ≠ t := by simpa using hn
      simp [hst,Ne.symm hst] at hh
private theorem anchor_injective {N : Nat} {i j i' j' : Option (Fin N)}
    (h : anchor i j = anchor i' j') : i = i' ∧ j = j' := by
  have he := List.append_inj h ((word_length i).trans (word_length i').symm)
  exact ⟨word_injective N he.1,word_injective N he.2⟩
private theorem payload_injective (N : Nat) : Function.Injective (@payload N) := by
  intro i j he
  cases i with
  | none =>
    cases j with
    | none => rfl
    | some t =>
      have hh : word (some t) ∈ payload (some t) := ⟨t,rfl,rfl⟩
      rw [← he] at hh; simpa [payload] using hh
  | some s =>
    have hh : word (some s) ∈ payload (some s) := ⟨s,rfl,rfl⟩
    rw [he] at hh
    obtain ⟨t,rfl,ht⟩ := hh
    exact word_injective N ht
private theorem derivative_predecessor {N : Nat} (i j : Option (Fin N)) (b : Bool) :
    derivative (predecessor i j) b = payload (if b then j else i) := by
  cases b <;> ext f <;> simp [derivative,predecessor,payload]
private theorem predecessor_injective (N : Nat) :
    Function.Injective (fun ij : Option (Fin N) × Option (Fin N) => predecessor ij.1 ij.2) := by
  intro ij pq he
  have h0 := congrArg (fun S => derivative S false) he
  have h1 := congrArg (fun S => derivative S true) he
  simp only [derivative_predecessor,Bool.false_eq_true,ite_false,ite_true] at h0 h1
  exact Prod.ext (payload_injective N h0) (payload_injective N h1)
private theorem selected_indices {N : Nat} {full : Bool} (p : Point N full) :
    (if p.2.1 then (indices p).2 else (indices p).1) = some p.1 := by
  rcases p with ⟨s,b,t⟩; cases b <;> rfl
private theorem other_indices {N : Nat} {full : Bool} (p : Point N full) :
    (if p.2.1 then (indices p).1 else (indices p).2) = p.2.2.val := by
  rcases p with ⟨s,b,t⟩; cases b <;> rfl
private theorem fine_injective (N : Nat) (full : Bool) : Function.Injective (@fine N full) := by
  intro p q he
  have hi := predecessor_injective N (congrArg Prod.fst he)
  have hb : p.2.1 = q.2.1 := by simpa [fine] using congrArg Prod.snd he
  have hs := congrArg (fun ij => if p.2.1 then ij.2 else ij.1) hi
  have ht := congrArg (fun ij => if p.2.1 then ij.1 else ij.2) hi
  rw [selected_indices, hb,selected_indices] at hs
  rw [other_indices, hb,other_indices] at ht
  exact Prod.ext (Option.some.inj hs) (Prod.ext hb (Subtype.ext ht))
private theorem point_of_indices {N : Nat} {full : Bool} {i j : Option (Fin N)}
    (ha : Admissible full i j) (b : Bool) (s : Fin N)
    (hs : (if b then j else i) = some s) :
    ∃ p : Point N full, indices p = (i,j) ∧ p.2.1 = b ∧ p.1 = s := by
  cases b with
  | false =>
    change i = some s at hs; subst i
    exact ⟨(s,false,⟨j,fun hf => (ha.2 hf).2⟩),rfl,rfl,rfl⟩
  | true =>
    change j = some s at hs; subst j
    exact ⟨(s,true,⟨i,fun hf => (ha.2 hf).1⟩),rfl,rfl,rfl⟩
private theorem point_admissible {N : Nat} {full : Bool} (p : Point N full) :
    Admissible full (indices p).1 (indices p).2 := by
  rcases p with ⟨s,b,t⟩; cases b <;> simpa [indices,Admissible] using t.property
private theorem anchor_length {N : Nat} (i j : Option (Fin N)) : (anchor i j).length = 2 * N := by
  simp [anchor,word_length]; omega
private theorem prefix_length {N : Nat} {full : Bool} (p : Point N full) :
    (selectorPrefix p).length = 2 * N + 1 := by simp [selectorPrefix,anchor_length]
private theorem code_length {N : Nat} {full : Bool} (p : Point N full) :
    (code p).length = 3 * N + 1 := by simp [code,prefix_length,word_length]; omega

private theorem original_words (N : Nat) (full : Bool) (w : List Bool) :
    w ∈ relation N full ↔ ∃ i j : Option (Fin N), ∃ b : Bool, ∃ s : Fin N,
      Admissible full i j ∧ (if b then j else i) = some s ∧
      w = anchor i j ++ b :: word (some s) := by
  constructor
  · rintro ⟨p,rfl⟩
    exact ⟨(indices p).1,(indices p).2,p.2.1,p.1,point_admissible p,
      selected_indices p,by simp [code,selectorPrefix,List.append_assoc]⟩
  · rintro ⟨i,j,b,s,ha,hs,rfl⟩
    obtain ⟨p,hp,hb,ht⟩ := point_of_indices ha b s hs
    refine ⟨p,?_⟩
    simp [code,selectorPrefix,hp,hb,ht,List.append_assoc]

private theorem residual_anchor (N : Nat) (full : Bool) (i j : Option (Fin N))
    (ha : Admissible full i j) :
    residual (relation N full) (anchor i j) = predecessor i j := by
  ext f
  constructor
  · rintro ⟨p,hp⟩
    have hp' : anchor (indices p).1 (indices p).2 ++ p.2.1 :: word (some p.1) =
        anchor i j ++ f := by simpa [code,selectorPrefix,List.append_assoc] using hp
    have he := List.append_inj hp' ((anchor_length _ _).trans (anchor_length i j).symm)
    have hi := anchor_injective he.1
    have hf : f = p.2.1 :: word (some p.1) := by
      simpa [code,selectorPrefix,List.append_assoc] using he.2.symm
    have hs := selected_indices p
    rw [hi.1,hi.2] at hs
    cases h : p.2.1 with
    | false => exact Or.inl ⟨p.1,by simpa [h] using hs,by simpa [h] using hf⟩
    | true => exact Or.inr ⟨p.1,by simpa [h] using hs,by simpa [h] using hf⟩
  · rintro (⟨s,hs,rfl⟩ | ⟨s,hs,rfl⟩)
    · exact (original_words N full _).mpr ⟨i,j,false,s,ha,hs,rfl⟩
    · exact (original_words N full _).mpr ⟨i,j,true,s,ha,hs,rfl⟩

private theorem predecessor_nonempty {N : Nat} {full : Bool} {i j : Option (Fin N)}
    (ha : Admissible full i j) : (predecessor i j).Nonempty := by
  cases i with
  | some s => exact ⟨false :: word (some s),Or.inl ⟨s,rfl,rfl⟩⟩
  | none =>
    cases j with
    | some t => exact ⟨true :: word (some t),Or.inr ⟨t,rfl,rfl⟩⟩
    | none => exact (ha.1.elim (fun h => h rfl) (fun h => h rfl)).elim

private theorem anchor_realized {N : Nat} {full : Bool} {i j : Option (Fin N)}
    (ha : Admissible full i j) : ∃ f, anchor i j ++ f ∈ relation N full := by
  obtain ⟨f,hf⟩ := predecessor_nonempty ha
  exact ⟨f,(Set.ext_iff.mp (residual_anchor N full i j ha) f).mpr hf⟩

private theorem previous_prefix_complete {N : Nat} {full : Bool} {u : List Bool}
    (hu : u.length = 2 * N) : (∃ f, u ++ f ∈ relation N full) ↔
      ∃ i j : Option (Fin N), Admissible full i j ∧ u = anchor i j := by
  constructor
  · rintro ⟨f,p,hp⟩
    have hp' : anchor (indices p).1 (indices p).2 ++ p.2.1 :: word (some p.1) = u ++ f := by
      simpa [code,selectorPrefix,List.append_assoc] using hp
    have he := List.append_inj hp' ((anchor_length _ _).trans hu.symm)
    exact ⟨(indices p).1,(indices p).2,point_admissible p,he.1.symm⟩
  · rintro ⟨i,j,ha,rfl⟩; exact anchor_realized ha

private theorem current_prefix_complete {N : Nat} {full : Bool} {u : List Bool}
    (hu : u.length = 2 * N + 1) : (∃ f, u ++ f ∈ relation N full) ↔
      ∃ p : Point N full, u = selectorPrefix p := by
  constructor
  · rintro ⟨f,p,hp⟩
    exact ⟨p,(List.append_inj hp ((prefix_length p).trans hu.symm)).1.symm⟩
  · rintro ⟨p,rfl⟩; exact ⟨word (some p.1),p,rfl⟩

private theorem residual_prefix {N : Nat} {full : Bool} (p : Point N full) :
    residual (relation N full) (selectorPrefix p) = {word (some p.1)} := by
  rw [selectorPrefix,shift,residual_anchor N full _ _ (point_admissible p),
    derivative_predecessor,selected_indices]
  ext f; simp [payload]

private theorem actual_image (N : Nat) (full : Bool) :
    image (relation N full) (2 * N + 1, 1) = Set.range (@fine N full) := by
  ext z
  constructor
  · rintro ⟨s,rfl⟩
    have ht := congrArg Prod.snd s.property.1
    have hu := congrArg Prod.fst s.property.1
    change s.val.2.length = 1 at ht
    change s.val.1.length + s.val.2.length = 2 * N + 1 at hu
    have hp : (s.val.1 ++ s.val.2).length = 2 * N + 1 := by simp [hu]
    obtain ⟨p,he⟩ := (current_prefix_complete hp).mp s.property.2
    have hlen : s.val.1.length = (anchor (indices p).1 (indices p).2).length := by
      rw [anchor_length]; omega
    have hs := List.append_inj he hlen
    refine ⟨p,?_⟩
    change (predecessor (indices p).1 (indices p).2,[p.2.1]) =
      (residual (relation N full) s.val.1,s.val.2)
    rw [hs.1,hs.2,residual_anchor N full _ _ (point_admissible p)]
  · rintro ⟨p,rfl⟩
    let s : typedState (relation N full) (2 * N + 1, 1) :=
      ⟨(anchor (indices p).1 (indices p).2,[p.2.1]),
        by simp [publicType,anchor_length],⟨word (some p.1),p,rfl⟩⟩
    refine ⟨s,?_⟩
    change (residual (relation N full) (anchor (indices p).1 (indices p).2),[p.2.1]) = fine p
    rw [residual_anchor N full _ _ (point_admissible p)]; rfl

private theorem previous_residuals (N : Nat) (full : Bool) :
    residualSet (relation N full) (2 * N) =
      {S | ∃ i j : Option (Fin N), Admissible full i j ∧ predecessor i j = S} := by
  ext S
  constructor
  · rintro ⟨v,hv,hC,rfl⟩
    obtain ⟨i,j,ha,rfl⟩ := (previous_prefix_complete hv).mp hC
    exact ⟨i,j,ha,(residual_anchor N full i j ha).symm⟩
  · rintro ⟨i,j,ha,rfl⟩
    exact ⟨anchor i j,anchor_length i j,anchor_realized ha,residual_anchor N full i j ha⟩

private theorem current_residuals (N : Nat) (full : Bool) :
    residualSet (relation N full) (2 * N + 1) =
      Set.range (fun s : Fin N => ({word (some s)} : Set (List Bool))) := by
  ext S
  constructor
  · rintro ⟨v,hv,hC,rfl⟩
    obtain ⟨p,rfl⟩ := (current_prefix_complete hv).mp hC
    exact ⟨p.1,(residual_prefix p).symm⟩
  · rintro ⟨s,rfl⟩
    let p : Point N full := (s,false,⟨some s,by simp⟩)
    exact ⟨selectorPrefix p,prefix_length p,⟨word (some s),p,rfl⟩,residual_prefix p⟩

private theorem full_branching (N : Nat) : FullBranching (relation N true) (2 * N + 1) := by
  intro v hv hC b
  have hv' : v.length = 2 * N := by omega
  have hS : residual (relation N true) v ∈ residualSet (relation N true) (2 * N) :=
    ⟨v,hv',hC,rfl⟩
  rw [previous_residuals] at hS
  obtain ⟨i,j,ha,hij⟩ := hS
  have hs : (if b then j else i) ≠ none := by
    cases b
    · exact (ha.2 rfl).1
    · exact (ha.2 rfl).2
  obtain ⟨s,he⟩ := Option.ne_none_iff_exists'.mp hs
  have hf : word (some s) ∈ derivative (residual (relation N true) v) b := by
    rw [← hij,derivative_predecessor]
    exact ⟨s,he,rfl⟩
  exact ⟨word (some s),by
    simpa [derivative,StrictAnchoredBoundary.residual,List.append_assoc] using hf⟩

private theorem recut_fine {N : Nat} {full : Bool} (p : Point N full) :
    recut (fine p) = {word (some p.1)} := by
  change derivative (predecessor (indices p).1 (indices p).2) p.2.1 = _
  rw [derivative_predecessor,selected_indices]
  ext f; simp [payload]

private theorem singleton_injective (N : Nat) :
    Function.Injective (fun s : Fin N => ({word (some s)} : Set (List Bool))) := by
  intro s t h
  exact Option.some.inj (word_injective N (Set.singleton_injective h))

private theorem current_fiber_range {N : Nat} (full : Bool) (s : Fin N) :
    currentFiber (relation N full) (2 * N + 1) {word (some s)} =
      Set.range (fun bt : Bool × Spare N full => fine (s,bt)) := by
  ext z
  constructor
  · rintro ⟨hz,he⟩
    rw [actual_image] at hz
    obtain ⟨p,rfl⟩ := hz
    rw [recut_fine] at he
    have hs := singleton_injective N he
    exact ⟨p.2,by rw [← hs]⟩
  · rintro ⟨bt,rfl⟩
    exact ⟨by rw [actual_image]; exact ⟨(s,bt),rfl⟩,recut_fine (s,bt)⟩

private theorem fixed_fiber_range {N : Nat} (full : Bool) (s : Fin N) (b : Bool) :
    fixedBitFiber (relation N full) (2 * N + 1) {word (some s)} b =
      Set.range (fun t : Spare N full => fine (s,b,t)) := by
  ext z
  constructor
  · rintro ⟨hz,hb⟩
    rw [current_fiber_range] at hz
    obtain ⟨⟨c,t⟩,rfl⟩ := hz
    have he : c = b := by simpa [fine] using hb
    subst c; exact ⟨t,rfl⟩
  · rintro ⟨t,rfl⟩
    exact ⟨by rw [current_fiber_range]; exact ⟨(b,t),rfl⟩,rfl⟩

private theorem spare_card (N : Nat) (full : Bool) :
    Nat.card (Spare N full) = N + if full then 0 else 1 := by
  cases full with
  | false =>
    let e : Spare N false ≃ Option (Fin N) :=
      { toFun := Subtype.val, invFun := fun i => ⟨i,by simp⟩,
        left_inv := fun _ => rfl, right_inv := fun _ => rfl }
    rw [Nat.card_congr e,Nat.card_eq_fintype_card]
    simp
  | true =>
    let f : Fin N → Spare N true := fun s => ⟨some s,by simp⟩
    have hf : Function.Bijective f := by
      constructor
      · intro s t he; exact Option.some.inj (congrArg Subtype.val he)
      · intro t
        obtain ⟨s,hs⟩ := Option.ne_none_iff_exists'.mp (t.property rfl)
        exact ⟨s,Subtype.ext hs.symm⟩
    rw [← Nat.card_congr (Equiv.ofBijective f hf)]
    simp

private theorem attained_counts (N : Nat) (full : Bool) :
    Nat.card (residualSet (relation N full) (2 * N + 1)) = N ∧
    Nat.card (image (relation N full) (2 * N + 1, 1)) = 2 * N*(N + if full then 0 else 1) ∧
    ∀ E ∈ residualSet (relation N full) (2 * N + 1),
      Nat.card (currentFiber (relation N full) (2 * N + 1) E) = 2*(N + if full then 0 else 1) ∧
      ∀ b, Nat.card (fixedBitFiber (relation N full) (2 * N + 1) E b) = N + if full then 0 else 1 := by
  refine ⟨?_,?_,?_⟩
  · rw [current_residuals,Nat.card_range_of_injective (singleton_injective N)]
    simp
  · rw [actual_image,Nat.card_range_of_injective (fine_injective N full),
      Nat.card_prod,Nat.card_prod,spare_card]
    simp; ring
  · intro E hE
    rw [current_residuals] at hE
    obtain ⟨s,rfl⟩ := hE
    constructor
    · rw [current_fiber_range,Nat.card_range_of_injective,Nat.card_prod,spare_card]
      · simp
      · intro t u he
        exact congrArg Prod.snd (fine_injective N full he)
    · intro b
      rw [fixed_fiber_range,Nat.card_range_of_injective,spare_card]
      intro t u he
      exact congrArg (fun p : Point N full => p.2.2) (fine_injective N full he)

def Bounds (C : Set (List Bool)) (k : Nat) (q : Nat) : Prop :=
  (∀ E ∈ residualSet C k, Nat.card (currentFiber C k E) ≤ 2 * q ∧
    ∀ b, Nat.card (fixedBitFiber C k E b) ≤ q) ∧
  Nat.card (image C (k, 1)) ≤ 2 * Nat.card (residualSet C k) * q

def Attains (N : Nat) (full : Bool) : Prop :=
  let C := relation N full
  C.Nonempty ∧ (∀ w ∈ C, w.length = 3 * N + 1) ∧
  1 ≤ 2 * N + 1 ∧ 2 * N + 1 ≤ 3 * N + 1 ∧
  (full = true → FullBranching C (2 * N + 1)) ∧
  Nat.card (residualSet C (2 * N + 1)) = N ∧
  Nat.card (image C (2 * N + 1, 1)) = 2 * N*(N + if full then 0 else 1) ∧
  ∀ E ∈ residualSet C (2 * N + 1),
    Nat.card (currentFiber C (2 * N + 1) E) = 2*(N + if full then 0 else 1) ∧
    ∀ b, Nat.card (fixedBitFiber C (2 * N + 1) E b) = N + if full then 0 else 1

private theorem attainment (N : Nat) (hN : 1 ≤ N) (full : Bool) : Attains N full := by
  let s : Fin N := ⟨0,by omega⟩
  let p : Point N full := (s,false,⟨some s,by simp⟩)
  refine ⟨⟨code p,p,rfl⟩,?_,by omega,by omega,?_,attained_counts N full⟩
  · rintro w ⟨q,rfl⟩; exact code_length q
  · intro h; subst full; exact full_branching N

/-- Sharp binary one-symbol recut bounds on one actual relation, and simultaneous
attainment at every positive forward width in both branching regimes. -/
theorem sharp_binary_one_recut :
    (∀ (n : Nat) (C : Set (List Bool)), (∀ w ∈ C, w.length = n) → C.Nonempty →
      ∀ k : Nat, 1 ≤ k → k ≤ n →
      (residualSet C k).Finite ∧ 0 < Nat.card (residualSet C k) ∧
      (∀ z ∈ image C (k, 1), recut z ∈ residualSet C k) ∧
      Bounds C k (Nat.card (residualSet C k)+1) ∧
      (FullBranching C k → Bounds C k (Nat.card (residualSet C k)))) ∧
    (∀ N : Nat, 1 ≤ N → Attains N false ∧ Attains N true) := by
  constructor
  · intro n C hl hc k hk hkn
    have hfin := residual_finite C k
    letI := hfin.fintype
    have hn : 0 < Nat.card (residualSet C k) := by
      apply Nat.card_pos_iff.mpr
      exact ⟨(residual_nonempty n C hl hc k hkn).to_subtype,inferInstance⟩
    refine ⟨hfin,hn,fun z hz => (image_data n C hl hc k hk hkn hz).2.2,?_,?_⟩
    · have hempty : (∅ : Set (List Bool)) ∉ residualSet C k := by
        intro he; exact (residual_not_empty he).ne_empty rfl
      have hB := hfin.insert (∅ : Set (List Bool))
      letI := hB.fintype
      have hcard : Nat.card (insert (∅ : Set (List Bool)) (residualSet C k) : Set (Set (List Bool))) =
          Nat.card (residualSet C k)+1 := by
        rw [Nat.card_eq_fintype_card,Nat.card_eq_fintype_card,Set.card_insert _ hempty]
      have hbound := bounds_with n C hl hc k hk hkn _ hB (by
        intro S hS b
        exact (derivative_member hk hS b).elim (fun he => Or.inl he) (fun he => Or.inr he))
      rw [hcard] at hbound
      exact ⟨fun E _ => hbound.1 E,hbound.2⟩
    · intro hb
      have hbound := bounds_with n C hl hc k hk hkn _ hfin (by
        intro S hS b; exact derivative_full hk hb hS b)
      exact ⟨fun E _ => hbound.1 E,hbound.2⟩
  · intro N hN; exact ⟨attainment N hN false,attainment N hN true⟩

end D5.S3.ObserverMemory.SharpBinaryOneRecut
