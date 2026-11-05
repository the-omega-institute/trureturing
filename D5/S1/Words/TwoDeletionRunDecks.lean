/- GID: D5/S1/Words/TwoDeletionRunDecks
   generality: G
   mirror-B: D5/B/S1/Words/TwoDeletionRunDecks
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Exact binary run counts and entropy comparisons for two deletions. -/

/-
admission_basis: escape-witness
Module escape_witness: twoRunBlocks_linear.
Escape audit unfinished: https://github.com/the-omega-institute/trureturing/issues/19498.
Frozen dependency identifiers refer to declarations at the pinned base:
F1: D5/S1/Words/AssociatedMersenne/RunTupleBijection.splitData_positive; statement_id: sha256:5355f8c314d297cb883cdcfef81c4b1dc2947535c741326cb84ddb5ecdb601fa.
F2: D5/S1/Words/AssociatedMersenne/RunTupleBijection.splitData; statement_id: sha256:6e3cc323324665c81638b2ff35725d45de98161ca95937f62867e81732fec0f0.
F3: D5/S1/Words/AssociatedMersenne/RunTupleBijection.blockLengths; statement_id: sha256:e3f12e42fd17d7c9355dfc30f184ef2df14db948a5b37cb78dc1839a924c35d2.
F4: D5/S1/Words/AssociatedMersenne/RunTupleBijection.splitData_reconstruct; statement_id: sha256:b8e79b941f58db417f6353fe33118db83888c3ae649cb374665cbe6dbc922482.
F5: D5/S1/Words/AssociatedMersenne/RunTupleBijection.splitData_alternating; statement_id: sha256:432fa419951886376b3b92b39b0f0543ec8c283dcccd6552931cef4cbe3b6588.
adjacentWeights: proof_shape: bind-only (definition); frozen: none; escape_witness: none; consumer: adjacentBlocks_weights.
pairWeights: proof_shape: bind-only (definition); frozen: none; escape_witness: none; consumer: D5.S3.Entropy.TwoDeletionRunEntropyBounds.pair_phi_formula.
count_as_sum_indicator: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: collisionBlocks_realize.
prefixBlocks: proof_shape: bind-only (definition); frozen: none; escape_witness: none; consumer: adjacentBlocks_compatible.
adjacent_singleton_shift: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: adjacentBlocks_compatible.
deletionDeck: proof_shape: bind-only (definition); frozen: none; escape_witness: none; consumer: two_deletion_sum_replicate.
deletionDeck_zero: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: two_deletion_sum_replicate.
deletionDeck_nil: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: oneRunBlocks_linear.
deletionDeck_cons: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: two_deletion_sum_replicate.
runWord: proof_shape: bind-only (definition); frozen: none; escape_witness: none; consumer: runWord_data.
sameRunWeights: proof_shape: bind-only (definition); frozen: none; escape_witness: none; consumer: collisionWeights.
nonadjacentWeights: proof_shape: bind-only (definition); frozen: none; escape_witness: none; consumer: collisionWeights.
componentWeightsAux: proof_shape: bind-only (definition); frozen: none; escape_witness: none; consumer: mergeWeightedAux_weights.
blockLengths_positive: proof_shape: bind-only; frozen: F1,F2,F3; escape_witness: none; consumer: D5.S3.Entropy.SinghviMaxInputEntropy.exists_positive_run_profile.
realizeBlocks: proof_shape: bind-only (definition); frozen: none; escape_witness: none; consumer: mergeWeightedAux_realize.
mergeWeightedAux: proof_shape: bind-only (definition); frozen: none; escape_witness: none; consumer: componentBlocks.
MergeCompatible: proof_shape: bind-only (definition); frozen: none; escape_witness: none; consumer: adjacentBlocks_compatible.
oneRunBlocks: proof_shape: bind-only (definition); frozen: none; escape_witness: none; consumer: nonadjBlocks.
realizeBlocks_count: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: collisionBlocks_realize.
edgeLabel: proof_shape: bind-only (definition); frozen: none; escape_witness: none; consumer: adjacentBlocks_compatible.
adjacentWeights_length: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: componentBlocks_realize.
sameBlocks: proof_shape: bind-only (definition); frozen: none; escape_witness: none; consumer: collisionBlocks.
deletionDeck_one_replicate: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: one_deletion_sum_replicate.
componentWeights: proof_shape: bind-only (definition); frozen: none; escape_witness: none; consumer: collisionWeights.
runWord_length: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: D5.S3.Entropy.SinghviMaxInputEntropy.exists_positive_run_profile.
runWord_data: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: runWord_blockLengths.
MergeCompatible_weight_irrel: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: mergeWeightedAux_realize.
MergeCompatible_map: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: adjacentBlocks_compatible.
mergeWeightedAux_weights: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: componentBlocks_weights.
one_deletion_sum_replicate: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: two_deletion_sum_replicate.
twoRunBlocks: proof_shape: bind-only (definition); frozen: none; escape_witness: none; consumer: twoRunBlocks_decomposition.
oneRunBlocks_weights: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: nonadjBlocks_weights.
adjacentBlocks: proof_shape: bind-only (definition); frozen: none; escape_witness: none; consumer: adjacentBlocks_compatible.
nonadjBlocks: proof_shape: bind-only (definition); frozen: none; escape_witness: none; consumer: collisionBlocks.
sameBlocks_weights: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: D5.S3.Entropy.TwoDeletionChannelEntropy.collisionBlocks_phi.
deletionDeck_eq_sublistsLen: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: twoDeletionDeck_eq_deletionDeck.
collisionWeights: proof_shape: bind-only (definition); frozen: none; escape_witness: none; consumer: D5.S3.Entropy.TwoDeletionRunEntropyBounds.run_fine_insertion_bound.
runWord_blockLengths: proof_shape: bind-only; frozen: F3,F4,F5,F2; escape_witness: none; consumer: D5.S3.Entropy.SinghviMaxInputEntropy.exists_positive_run_profile.
mergeWeightedAux_realize: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: componentBlocks_realize.
two_deletion_sum_replicate: proof_shape: content; frozen: none; escape_witness: D5.S1.Words.TwoDeletionRunDecks.two_deletion_sum_replicate; consumer: twoRunBlocks_linear.
oneRunBlocks_linear: proof_shape: content; frozen: none; escape_witness: D5.S1.Words.TwoDeletionRunDecks.oneRunBlocks_linear; consumer: twoRunBlocks_linear.
componentBlocks: proof_shape: bind-only (definition); frozen: none; escape_witness: none; consumer: collisionBlocks.
adjacentBlocks_weights: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: componentBlocks_weights.
adjacentBlocks_compatible: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: componentBlocks_realize.
twoRunBlocks_decomposition: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: collisionBlocks_realize.
nonadjBlocks_weights: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: D5.S3.Entropy.TwoDeletionChannelEntropy.collisionBlocks_phi.
twoDeletionDeck_eq_deletionDeck: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: D5.S3.Entropy.TwoDeletionChannelEntropy.actual_run_insertion_lower.
twoRunBlocks_linear: proof_shape: content; frozen: none; escape_witness: twoRunBlocks_linear; consumer: collisionBlocks_realize.
componentBlocks_realize: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: collisionBlocks_realize.
componentBlocks_weights: proof_shape: bind-only; frozen: none; escape_witness: none; consumer: D5.S3.Entropy.TwoDeletionChannelEntropy.collisionBlocks_phi.
collisionBlocks: proof_shape: bind-only (definition); frozen: none; escape_witness: none; consumer: collisionBlocks_realize.
collisionBlocks_realize: proof_shape: content; frozen: none; escape_witness: D5.S1.Words.TwoDeletionRunDecks.twoRunBlocks_linear; consumer: D5.S3.Entropy.TwoDeletionChannelEntropy.actual_run_insertion_lower.
-/

import D5.S1.Words.AssociatedMersenne.RunTupleBijection
import Mathlib.Tactic.Ring

set_option Elab.async false
set_option maxHeartbeats 1200000
set_option maxRecDepth 4096

namespace D5.S1.Words.TwoDeletionRunDecks

open D5.S1.Words.AssociatedMersenne.RunTupleBijection
open D5.S1.Words.AssociatedMersenne.RunTupleBijection (splitData splitData_reconstruct splitData_alternating splitData_positive)

def adjacentWeights : List ℕ → List ℕ
  | a :: b :: rs => a*b :: adjacentWeights (b::rs)
  | _ => []

def pairWeights : List ℕ → List ℕ
  | [] => []
  | a :: rs => rs.map (fun b => a*b) ++ pairWeights rs

private lemma count_as_sum_indicator {α : Type*} [DecidableEq α] [BEq α] [LawfulBEq α] (l : List α) (x : α) :
    l.count x=(l.map (fun y => if y=x then 1 else 0)).sum := by
  simpa only [List.flatMap_singleton', List.map_map, Function.comp_def,
      List.count_singleton, beq_iff_eq] using
      (List.count_flatMap (x := x) (l := l) (f := fun y => [y]))

def prefixBlocks (pre : List Bool) (bs : List (List Bool × ℕ)) : List (List Bool × ℕ) :=
  bs.map (fun p => (pre++p.1,p.2))

private lemma adjacent_singleton_shift (b : Bool) (a c : ℕ) (ha : 1 ≤ a) (hc : 1 ≤ c) :
    List.replicate (a-1) b++List.replicate c b=
      List.replicate a b++List.replicate (c-1) b := by
  rw [←List.replicate_add,←List.replicate_add]
  congr 1
  omega

def deletionDeck {α : Type*} (k : ℕ) (w : List α) : List (List α) :=
  if k ≤ w.length then w.sublistsLen (w.length-k) else []

private lemma deletionDeck_zero {α : Type*} (w : List α) : deletionDeck 0 w = [w] := by
  simp [deletionDeck]

private lemma deletionDeck_nil {α : Type*} (k : ℕ) : deletionDeck (k+1) ([] : List α) = [] := by
  simp [deletionDeck]

private lemma deletionDeck_cons {α : Type*} (k : ℕ) (a : α) (w : List α) :
    deletionDeck (k+1) (a::w) = deletionDeck k w ++ (deletionDeck (k+1) w).map (List.cons a) := by
  by_cases hk : k ≤ w.length
  · by_cases hs : k+1 ≤ w.length
    · have hcons : k+1 ≤ (a::w).length := by exact Nat.succ_le_succ hk
      have he : w.length+1-(k+1)=(w.length-(k+1))+1 := by exact Nat.sub_add_comm hs
      have he' : w.length-k=(w.length-(k+1))+1 := by omega
      simp only [deletionDeck,if_pos hk,if_pos hs,if_pos hcons,List.length_cons,he,he',List.sublistsLen_succ_cons]
      simp [show k+1 ≤ w.length+1 by omega]
    · have he : k=w.length := by exact Nat.le_antisymm hk (Nat.le_of_not_lt hs)
      subst k
      simp [deletionDeck]
  · have hs : ¬k+1 ≤ w.length := by omega
    have hc : ¬k+1 ≤ (a::w).length := by simp; omega
    simp [deletionDeck,hk,hs,hc]

def runWord : Bool → List ℕ → List Bool
  | _, [] => []
  | b, r :: rs => List.replicate r b ++ runWord (!b) rs



def sameRunWeights (rs : List ℕ) : List ℕ :=
  (rs.filter fun r => 2 ≤ r).map (fun r => r.choose 2)



def nonadjacentWeights : List ℕ → List ℕ
  | [] => []
  | a :: rs => (rs.drop 1).map (fun b => a*b) ++ nonadjacentWeights rs



def componentWeightsAux (acc prev : ℕ) : List ℕ → List ℕ
  | [] => [acc]
  | r :: rs => if prev = 1 then componentWeightsAux (acc + prev*r) r rs
      else acc :: componentWeightsAux (prev*r) r rs




lemma blockLengths_positive (w : List Bool) : ∀ r ∈ blockLengths w, 0 < r := by
  intro r hr
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp (show r ∈ (splitData w).map Prod.snd by simpa [splitData,blockLengths,List.map_map] using hr)
  exact splitData_positive w p hp

def realizeBlocks {α : Type*} (bs : List (α × ℕ)) : List α :=
  bs.flatMap (fun p => List.replicate p.2 p.1)

def mergeWeightedAux {α : Type*} (p : α × ℕ) (prev : ℕ) :
    List ℕ → List (α × ℕ) → List (α × ℕ)
  | r::rs,q::qs => if prev=1 then mergeWeightedAux (p.1,p.2+q.2) r rs qs
      else p::mergeWeightedAux q r rs qs
  | _,_ => [p]

private def MergeCompatible {α : Type*} (p : α × ℕ) (prev : ℕ) : List ℕ → List (α × ℕ) → Prop
  | r::rs,q::qs => (prev=1 → p.1=q.1) ∧ MergeCompatible q r rs qs
  | _,_ => True

def oneRunBlocks : Bool → List ℕ → List (List Bool × ℕ)
  | _,[] => []
  | b,r::rs =>
    (List.replicate (r-1) b++runWord (!b) rs,r)::
      ((oneRunBlocks (!b) rs).map (fun p => (List.replicate r b++p.1,p.2)))

private lemma realizeBlocks_count {α : Type*} [DecidableEq α] [BEq α] [LawfulBEq α] (bs : List (α × ℕ)) (x : α) :
    (realizeBlocks bs).count x=(bs.map (fun p => p.2*(if p.1=x then 1 else 0))).sum := by
  unfold realizeBlocks
  rw [List.count_flatMap]
  apply congrArg List.sum
  apply List.map_congr_left
  intro p _
  by_cases hx : p.1=x <;> simp [Function.comp_def,List.count_replicate,hx]

def edgeLabel (b : Bool) (a c : ℕ) (rs : List ℕ) : List Bool :=
  List.replicate (a-1) b++List.replicate (c-1) (!b)++runWord b rs

private lemma adjacentWeights_length (rs : List ℕ) : (adjacentWeights rs).length=rs.length-1 := by
  induction rs with
  | nil => rfl
  | cons a rs ih =>
    cases rs with
    | nil => rfl
    | cons c rs => simpa [adjacentWeights] using congrArg Nat.succ ih

def sameBlocks : Bool → List ℕ → List (List Bool × ℕ)
  | _,[] => []
  | b,a::rs => (List.replicate (a-2) b++runWord (!b) rs,a.choose 2)::
      prefixBlocks (List.replicate a b) (sameBlocks (!b) rs)

private lemma deletionDeck_one_replicate {α : Type*} (b : α) (r : ℕ) (w : List α) :
    deletionDeck 1 (List.replicate r b++w)=
      List.replicate r (List.replicate (r-1) b++w)++
        (deletionDeck 1 w).map (fun x => List.replicate r b++x) := by
  induction r with
  | zero => simp [deletionDeck_zero,deletionDeck_nil,deletionDeck_cons]
  | succ r ih =>
    rw [List.replicate_succ,List.cons_append]
    simp only [deletionDeck_zero,deletionDeck_nil,deletionDeck_cons,List.singleton_append]
    rw [ih]
    cases r <;> simp [List.replicate_succ,List.cons_append,Function.comp_def,
      List.map_append,List.map_replicate,List.map_map,List.append_assoc]

def componentWeights : List ℕ → List ℕ
  | a :: b :: rs => componentWeightsAux (a*b) b rs
  | _ => []

lemma runWord_length (b : Bool) (rs : List ℕ) : (runWord b rs).length = rs.sum := by
  induction rs generalizing b with
  | nil => simp [runWord]
  | cons r rs ih => simp [runWord,ih]

private lemma runWord_data (ds : List (Bool × ℕ))
    (hc : (ds.map Prod.fst).IsChain (· ≠ ·)) :
    runWord (ds.headD (false,0)).1 (ds.map Prod.snd) =
      (ds.map (fun p => List.replicate p.2 p.1)).flatten := by
  induction ds with
  | nil => simp [runWord]
  | cons a ds ih =>
    cases ds with
    | nil => simp [runWord]
    | cons b ds =>
      have hpair : a.1 ≠ b.1 ∧ ((b::ds).map Prod.fst).IsChain (· ≠ ·) := by
        simpa only [List.map_cons,List.isChain_cons_cons] using hc
      have hne : a.1 ≠ b.1 := hpair.1
      have htail : ((b::ds).map Prod.fst).IsChain (· ≠ ·) := hpair.2
      have hb : (!a.1) = b.1 := by
        cases ha : a.1 <;> cases hb : b.1 <;> simp_all
      have hi := ih htail
      simpa only [List.headD_cons,List.map_cons,runWord,List.flatten_cons,hb] using
        congrArg (fun w => List.replicate a.2 a.1 ++ w) hi

private lemma MergeCompatible_weight_irrel {α : Type*} (p : α × ℕ) (n prev : ℕ)
    (rs : List ℕ) (es : List (α × ℕ)) :
    MergeCompatible (p.1,n) prev rs es ↔ MergeCompatible p prev rs es := by
  cases rs <;> cases es <;> rfl

private lemma MergeCompatible_map {α β : Type*} (F : α → β) (p : α × ℕ) (prev : ℕ)
    (rs : List ℕ) (es : List (α × ℕ)) (h : MergeCompatible p prev rs es) :
    MergeCompatible (F p.1,p.2) prev rs (es.map (fun q => (F q.1,q.2))) := by
  induction rs generalizing p prev es with
  | nil => trivial
  | cons r rs ih =>
    cases es with
    | nil => trivial
    | cons q qs =>
      exact ⟨fun hp => congrArg F (h.1 hp),ih q r qs h.2⟩

private lemma mergeWeightedAux_weights {α : Type*} (p : α × ℕ) (prev : ℕ)
    (rs : List ℕ) (es : List (α × ℕ))
    (hw : es.map Prod.snd=adjacentWeights (prev::rs)) :
    (mergeWeightedAux p prev rs es).map Prod.snd=componentWeightsAux p.2 prev rs := by
  induction rs generalizing p prev es with
  | nil => simp [mergeWeightedAux,componentWeightsAux]
  | cons r rs ih =>
    cases es with
    | nil => simp [adjacentWeights] at hw
    | cons q es =>
      have hh : q.2=prev*r ∧ es.map Prod.snd=adjacentWeights (r::rs) := by
        simpa only [List.map_cons,adjacentWeights,List.cons.injEq] using hw
      have hhead := hh.1
      have htail := hh.2
      by_cases hp : prev=1
      · simp only [mergeWeightedAux,componentWeightsAux,if_pos hp]
        rw [ih _ r es htail,hhead]
      · simp only [mergeWeightedAux,componentWeightsAux,if_neg hp,List.map_cons]
        rw [ih q r es htail,hhead]

private lemma one_deletion_sum_replicate {α : Type*} (b : α) (r : ℕ) (w : List α) (F : List α → ℕ) :
    ((deletionDeck 1 (List.replicate r b++w)).map F).sum=
      r*F (List.replicate (r-1) b++w)+
        ((deletionDeck 1 w).map (fun x => F (List.replicate r b++x))).sum := by
  rw [deletionDeck_one_replicate]
  simp [List.map_append,List.map_replicate,List.map_map,Function.comp_def]

private def twoRunBlocks : Bool → List ℕ → List (List Bool × ℕ)
  | _,[] => []
  | b,r::rs =>
    (List.replicate (r-2) b++runWord (!b) rs,r.choose 2)::
      (((oneRunBlocks (!b) rs).map (fun p => (List.replicate (r-1) b++p.1,r*p.2)))++
      ((twoRunBlocks (!b) rs).map (fun p => (List.replicate r b++p.1,p.2))))

private lemma oneRunBlocks_weights (b : Bool) (rs : List ℕ) :
    (oneRunBlocks b rs).map Prod.snd=rs := by
  induction rs generalizing b with
  | nil => rfl
  | cons r rs ih => simp [oneRunBlocks,List.map_map,Function.comp_def,ih]

def adjacentBlocks : Bool → List ℕ → List (List Bool × ℕ)
  | b,a::c::rs => (edgeLabel b a c rs,a*c)::
      prefixBlocks (List.replicate a b) (adjacentBlocks (!b) (c::rs))
  | _,_ => []

def nonadjBlocks : Bool → List ℕ → List (List Bool × ℕ)
  | b,a::c::rs =>
    ((oneRunBlocks b rs).map (fun p =>
      (List.replicate (a-1) b++List.replicate c (!b)++p.1,a*p.2)))++
      prefixBlocks (List.replicate a b) (nonadjBlocks (!b) (c::rs))
  | _,_ => []

lemma sameBlocks_weights (b : Bool) (rs : List ℕ) :
    (sameBlocks b rs).map Prod.snd=rs.map (fun a => a.choose 2) := by
  induction rs generalizing b with
  | nil => rfl
  | cons a rs ih => simp [sameBlocks,prefixBlocks,List.map_map,Function.comp_def,ih]

private lemma deletionDeck_eq_sublistsLen {α : Type*} (w : List α) (k : ℕ) (hk : k ≤ w.length) :
    deletionDeck k w=w.sublistsLen (w.length-k) := by
  simp [deletionDeck, hk]

def collisionWeights (rs : List ℕ) : List ℕ :=
  sameRunWeights rs ++ nonadjacentWeights rs ++ componentWeights rs



lemma runWord_blockLengths (w : List Bool) :
    runWord (w.headD false) (blockLengths w) = w := by
  have hc := splitData_alternating w
  have h := runWord_data (splitData w) hc
  have hr := splitData_reconstruct w
  have hlen : (splitData w).map Prod.snd = blockLengths w := by
    simp [splitData,blockLengths,List.map_map]
  rw [hlen,hr] at h
  by_cases hw : w=[]
  · simp [hw,blockLengths,runWord]
  have he : ((splitData w).headD (false,0)).1 = w.headD false := by
    let bs := w.splitBy (· == ·)
    have hb : bs ≠ [] := List.splitBy_ne_nil.mpr hw
    have hn : bs.head hb ≠ [] := List.ne_nil_of_mem_splitBy (List.head_mem hb)
    have hfirst := List.head_head_splitBy (· == ·) hw
    change (bs.head hb).head hn = w.head hw at hfirst
    change ((bs.map (fun b => (b.headD false,b.length))).headD (false,0)).1 = w.headD false
    rw [show (false,0) = (fun b : List Bool => (b.headD false,b.length)) [] from rfl,
      List.headD_map]
    change (bs.headD []).headD false = w.headD false
    simpa only [List.headD_eq_head?_getD,List.head?_eq_some_head hb,
      Option.getD_some,List.head?_eq_some_head hn,List.head?_eq_some_head hw] using hfirst
  simpa only [he] using h

private lemma mergeWeightedAux_realize {α : Type*} (p : α × ℕ) (prev : ℕ)
    (rs : List ℕ) (es : List (α × ℕ)) (hlen : es.length=rs.length)
    (hc : MergeCompatible p prev rs es) :
    realizeBlocks (mergeWeightedAux p prev rs es)=realizeBlocks (p::es) := by
  induction rs generalizing p prev es with
  | nil =>
    have he : es=[] := List.length_eq_zero_iff.mp (by simpa using hlen)
    subst es
    rfl
  | cons r rs ih =>
    cases es with
    | nil => simp at hlen
    | cons q es =>
      have ht : es.length=rs.length := by exact Nat.add_right_cancel hlen
      by_cases hp : prev=1
      · have hw : p.1=q.1 := hc.1 hp
        have htail : MergeCompatible (p.1,p.2+q.2) r rs es := by
          rw [hw]
          exact (MergeCompatible_weight_irrel q (p.2+q.2) r rs es).mpr hc.2
        rw [mergeWeightedAux,if_pos hp,ih _ _ _ ht htail]
        simp only [realizeBlocks,List.flatMap_cons]
        rw [List.replicate_add,hw,List.append_assoc]
      · rw [mergeWeightedAux,if_neg hp]
        simp only [realizeBlocks,List.flatMap_cons]
        rw [show (mergeWeightedAux q r rs es).flatMap (fun p => List.replicate p.2 p.1)=
          (q::es).flatMap (fun p => List.replicate p.2 p.1) from ih q r es ht hc.2]
        rfl

private lemma two_deletion_sum_replicate {α : Type*} (b : α) (r : ℕ) (w : List α) (F : List α → ℕ) :
    ((deletionDeck 2 (List.replicate r b++w)).map F).sum=
      r.choose 2*F (List.replicate (r-2) b++w)+
        r*((deletionDeck 1 w).map (fun x => F (List.replicate (r-1) b++x))).sum+
        ((deletionDeck 2 w).map (fun x => F (List.replicate r b++x))).sum := by
  induction r generalizing F with
  | zero => simp
  | succ r ih =>
    cases r with
    | zero => simp [List.replicate_succ,deletionDeck_zero,deletionDeck_nil,deletionDeck_cons,List.map_append,List.map_map,Function.comp_def]
    | succ r =>
      cases r with
      | zero =>
        simp [List.replicate_succ,deletionDeck_zero,deletionDeck_nil,deletionDeck_cons,List.map_append,List.map_map,Nat.choose_succ_succ,Function.comp_def]
        omega
      | succ r =>
        rw [List.replicate_succ,List.cons_append,deletionDeck_cons]
        simp only [List.map_append,List.sum_append,List.map_map,Function.comp_def]
        have ho := one_deletion_sum_replicate b (r+2) w F
        have ht := ih (fun x => F (b::x))
        simp only [List.replicate_succ,List.cons_append,Nat.add_sub_cancel,Function.comp_def] at ho ht
        have hc : (r+3).choose 2=(r+2).choose 2+(r+2) := by
          rw [Nat.choose_succ_succ]
          simp
          omega
        simp only [show r+1+1+1-2=r+1 by omega, show r+1+1+1-1=r+2 by omega, hc,Function.comp_def]
        simp only [List.replicate_succ,List.cons_append] at ho ht ⊢
        rw [ho,ht]
        simp only [show r+2-1=r+1 by omega,show r+1+1-2=r by omega,List.replicate_succ,List.cons_append]
        ring

private lemma oneRunBlocks_linear (b : Bool) (rs : List ℕ) (F : List Bool → ℕ) :
    ((deletionDeck 1 (runWord b rs)).map F).sum=
      ((oneRunBlocks b rs).map (fun p => p.2*F p.1)).sum := by
  induction rs generalizing b F with
  | nil => simp [runWord,deletionDeck_zero,deletionDeck_nil,deletionDeck_cons,oneRunBlocks]
  | cons r rs ih =>
    rw [runWord,one_deletion_sum_replicate,ih]
    simp [oneRunBlocks,List.map_map,Function.comp_def]

def componentBlocks : Bool → List ℕ → List (List Bool × ℕ)
  | b,a::c::rs => mergeWeightedAux (edgeLabel b a c rs,a*c) c rs
      (prefixBlocks (List.replicate a b) (adjacentBlocks (!b) (c::rs)))
  | _,_ => []

private lemma adjacentBlocks_weights (b : Bool) (rs : List ℕ) :
    (adjacentBlocks b rs).map Prod.snd=adjacentWeights rs := by
  induction rs generalizing b with
  | nil => rfl
  | cons a rs ih =>
    cases rs with
    | nil => rfl
    | cons c rs => simp [adjacentBlocks,adjacentWeights,prefixBlocks,List.map_map,Function.comp_def,ih]

private lemma adjacentBlocks_compatible (b : Bool) (a c : ℕ) (rs : List ℕ)
    (ha : 0<a) (hc : 0<c) (hp : ∀ r∈rs,0<r) :
    MergeCompatible (edgeLabel b a c rs,a*c) c rs
      (prefixBlocks (List.replicate a b) (adjacentBlocks (!b) (c::rs))) := by
  induction rs generalizing b a c with
  | nil => trivial
  | cons r rs ih =>
    have hr := hp r (by simp)
    have ht : ∀ t∈rs,0<t := fun t h => hp t (by simp [h])
    constructor
    · intro he
      subst c
      simp only [edgeLabel,runWord,prefixBlocks,adjacentBlocks,List.map_cons,List.append_nil,
        Nat.sub_self,List.replicate_zero,List.nil_append,List.replicate_one,Bool.not_not]
      simpa only [List.append_assoc] using congrArg (fun w => w++runWord (!b) rs)
        (adjacent_singleton_shift b a r (by omega) (by omega))
    · have hi := ih (!b) c r hc hr ht
      have hm := MergeCompatible_map (fun w => List.replicate a b++w)
        (edgeLabel (!b) c r rs,c*r) r rs
        (prefixBlocks (List.replicate c (!b)) (adjacentBlocks (!(!b)) (r::rs))) hi
      simpa only [adjacentBlocks,prefixBlocks,List.map_cons,List.map_map,Function.comp_def,
        Bool.not_not,List.append_assoc] using hm

private lemma twoRunBlocks_decomposition (b : Bool) (rs : List ℕ) (F : List Bool → ℕ) :
    ((twoRunBlocks b rs).map (fun p => p.2*F p.1)).sum=
      ((sameBlocks b rs).map (fun p => p.2*F p.1)).sum+
      ((nonadjBlocks b rs).map (fun p => p.2*F p.1)).sum+
      ((adjacentBlocks b rs).map (fun p => p.2*F p.1)).sum := by
  induction rs generalizing b F with
  | nil => simp [twoRunBlocks,sameBlocks,nonadjBlocks,adjacentBlocks]
  | cons a rs ih =>
    cases rs with
    | nil => simp [twoRunBlocks,sameBlocks,nonadjBlocks,adjacentBlocks,oneRunBlocks,prefixBlocks]
    | cons c rs =>
      have hi := ih (!b) (fun w => F (List.replicate a b++w))
      simp only [twoRunBlocks,sameBlocks,nonadjBlocks,adjacentBlocks,oneRunBlocks,prefixBlocks,
        List.map_cons,List.sum_cons,List.map_append,List.sum_append,List.map_map,
        Function.comp_def,Bool.not_not,List.append_assoc,edgeLabel] at hi ⊢
      omega

lemma nonadjBlocks_weights (b : Bool) (rs : List ℕ) :
    (nonadjBlocks b rs).map Prod.snd=nonadjacentWeights rs := by
  induction rs generalizing b with
  | nil => rfl
  | cons a rs ih =>
    cases rs with
    | nil => rfl
    | cons c rs =>
      have hw := congrArg (List.map (fun r => a*r)) (oneRunBlocks_weights b rs)
      simp only [List.map_map,Function.comp_def] at hw
      simp only [nonadjBlocks,nonadjacentWeights,List.drop_succ_cons,List.drop_zero,
        List.map_append,prefixBlocks,List.map_map,Function.comp_def]
      rw [hw,ih]
      rfl

lemma twoDeletionDeck_eq_deletionDeck (w : List Bool) (hw : 2 ≤ w.length) :
    (w.sublistsLen (w.length - 2))=deletionDeck 2 w := by
  exact (deletionDeck_eq_sublistsLen w 2 hw).symm

private lemma twoRunBlocks_linear (b : Bool) (rs : List ℕ) (F : List Bool → ℕ) :
    ((deletionDeck 2 (runWord b rs)).map F).sum=
      ((twoRunBlocks b rs).map (fun p => p.2*F p.1)).sum := by
  induction rs generalizing b F with
  | nil => simp [runWord,deletionDeck_zero,deletionDeck_nil,deletionDeck_cons,twoRunBlocks]
  | cons r rs ih =>
    rw [runWord,two_deletion_sum_replicate,oneRunBlocks_linear,ih]
    simp only [twoRunBlocks,List.map_cons,List.sum_cons,List.map_append,List.sum_append,List.map_map]
    simp only [Function.comp_def]
    rw [←List.sum_map_mul_left]
    have he : ((oneRunBlocks (!b) rs).map (fun p => r*(p.2*F (List.replicate (r-1) b++p.1)))).sum=
        ((oneRunBlocks (!b) rs).map (fun p => (r*p.2)*F (List.replicate (r-1) b++p.1))).sum := by
      congr 1
      apply List.map_congr_left
      intro p _
      ring
    rw [he]
    omega

private lemma componentBlocks_realize (b : Bool) (rs : List ℕ) (hp : ∀ r∈rs,0<r) :
    realizeBlocks (componentBlocks b rs)=realizeBlocks (adjacentBlocks b rs) := by
  cases rs with
  | nil => rfl
  | cons a rs =>
    cases rs with
    | nil => rfl
    | cons c rs =>
      have ha := hp a (by simp)
      have hc := hp c (by simp)
      have ht : ∀ r∈rs,0<r := fun r h => hp r (by simp [h])
      apply mergeWeightedAux_realize
      · have h := congrArg List.length (adjacentBlocks_weights (!b) (c::rs))
        simpa only [prefixBlocks,List.length_map,adjacentWeights_length,List.length_cons,Nat.add_sub_cancel] using h
      · exact adjacentBlocks_compatible b a c rs ha hc ht

lemma componentBlocks_weights (b : Bool) (rs : List ℕ) :
    (componentBlocks b rs).map Prod.snd=componentWeights rs := by
  cases rs with
  | nil => rfl
  | cons a rs =>
    cases rs with
    | nil => rfl
    | cons c rs =>
      apply mergeWeightedAux_weights
      simpa only [prefixBlocks,List.map_map,Function.comp_def] using adjacentBlocks_weights (!b) (c::rs)

def collisionBlocks (b : Bool) (rs : List ℕ) : List (List Bool × ℕ) :=
  sameBlocks b rs++nonadjBlocks b rs++componentBlocks b rs

lemma collisionBlocks_realize (b : Bool) (rs : List ℕ) (hp : ∀ r∈rs,0<r) :
    (realizeBlocks (collisionBlocks b rs)).Perm (deletionDeck 2 (runWord b rs)) := by
  apply List.perm_iff_count.mpr
  intro x
  have hc := congrArg (fun l : List (List Bool) => l.count x) (componentBlocks_realize b rs hp)
  rw [realizeBlocks_count,realizeBlocks_count] at hc
  rw [realizeBlocks_count,count_as_sum_indicator,twoRunBlocks_linear,twoRunBlocks_decomposition b rs (fun w => if w=x then 1 else 0)]
  simp only [collisionBlocks,List.map_append,List.sum_append]
  rw [hc]

end D5.S1.Words.TwoDeletionRunDecks
