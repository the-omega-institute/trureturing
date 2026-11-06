/- GID: D5/S3/Geometry/FiniteProtectedDualWord
   generality: G
   mirror-B: none (new universal P02 source)
   mirror-E: none (source-only implementation)
   anchors: [D5/S3/Geometry/OriginalLabelTwoSum/Raw,
             D5/S3/Geometry/FiniteAlexanderDualCollapse]
   utility: «protected» dual-word native sequence
   digest: Ordered raw face partitions produce «protected» native collapses on
           the unchanged ground, including ghosts, VOID and UNIT. -/
import D5.S3.Geometry.OriginalLabelTwoSum.Raw
import D5.S3.Geometry.FiniteAlexanderDualCollapse

/-! SOURCE_ONLY_UNCOMPILED. Raw membership is membership of the existing
LowerSet Family, never AugmentedFace. Only projection discards empty faces.
The only free-pair/sequence authorities are the imported native owners.
Critical symbols (including the empty face) and «protected» pairs are skipped.
No properness condition is imposed on a skipped pair. -/
noncomputable section
open Set Finset
namespace D5.S3.Geometry.FiniteProtectedDualWord
open OriginalLabelTwoSum
open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse
open FiniteConeCollapse
open FiniteAlexanderDualCollapse (simplex)

variable {V : Type*} [Fintype V] [DecidableEq V]

inductive Symbol (V : Type*) where
  | pair (L : Finset V) (v : V)
  | critical (S : Finset V)
  deriving DecidableEq

namespace Symbol

def faces : Symbol V → Finset (Finset V)
  | .pair L v => {L, insert v L}
  | .critical S => {S}

def isCritical : Symbol V → Prop
  | .pair _ _ => False
  | .critical _ => True

@[simp] theorem pair_faces (L : Finset V) (v : V) :
    (Symbol.pair L v).faces = {L, insert v L} := rfl

@[simp] theorem critical_faces (S : Finset V) :
    (Symbol.critical S).faces = {S} := rfl

end Symbol

def emittedOne (H : Finset (Finset V)) : Symbol V → Finset (Finset V)
  | .pair L v => if L ∈ H then ∅ else {L, insert v L}
  | .critical _ => ∅

def emittedFaces (H : Finset (Finset V)) : List (Symbol V) → Finset (Finset V)
  | [] => ∅
  | σ :: xs => emittedOne H σ ∪ emittedFaces H xs

/-- The existing finite dual table, equipped with its derived LowerSet proof.
The table tests raw K, so VOID and UNIT give different answers. -/
def rawDual (W : Finset V) (K : Family V) : Family V := by
  classical
  refine { carrier := {s | s ∈ (FiniteAlexanderDualCollapse.dualTable W
    (W.powerset.filter (fun T => T ∈ K)))}, lower' := ?_ }
  ·
    intro s t hts hs
    have hm : ∀ q : Finset V,
        q ∈ FiniteAlexanderDualCollapse.dualTable W
          (W.powerset.filter (fun T => T ∈ K)) ↔
          q ⊆ W ∧ W \ q ∉ K := by
      intro q
      simp only [FiniteAlexanderDualCollapse.dualTable, Finset.mem_filter,
        Finset.mem_powerset]
      simp only [Finset.sdiff_subset, true_and]
    obtain ⟨hsW, hsK⟩ := (hm s).mp hs
    exact (hm t).mpr ⟨hts.trans hsW, fun ht => hsK
      (K.lower (Finset.sdiff_subset_sdiff_right W hts) ht)⟩

private theorem mem_rawDual (W : Finset V) (K : Family V) (s : Finset V) :
    s ∈ rawDual W K ↔ s ⊆ W ∧ W \ s ∉ K := by
  classical
  change s ∈ FiniteAlexanderDualCollapse.dualTable W
    (W.powerset.filter (fun T => T ∈ K)) ↔ _
  simp only [FiniteAlexanderDualCollapse.dualTable, Finset.mem_filter,
    Finset.mem_powerset]
  simp only [Finset.sdiff_subset, true_and]

/-- This formula is used only at actual initial segments in `Contract.current`.
It says that a nonempty face survives iff its primal complement is outside K
or has not been emitted. No downward closure of an arbitrary subword is claimed. -/
def RawFaces (W : Finset V) (K : Family V)
    (R : Finset (Finset V)) (s : Finset V) : Prop :=
  s.Nonempty ∧ s ⊆ W ∧ (W \ s ∉ K ∨ W \ s ∉ R)

/-- Raw exact endpoint. Upwardness is within K; the proof does not adjoin empty
membership to K and does not require W to occur in K. -/
def rawEndpoint (W : Finset V) (K : Family V) (H : Finset (Finset V))
    (hUp : ∀ {T U}, T ∈ H → U ∈ K → T ⊆ U → U ∈ H) : Family V where
  carrier := {s | s ⊆ W ∧ (W \ s ∉ K ∨ W \ s ∈ H)}
  lower' := by
    classical
    rintro s t hts ⟨hsW, hs⟩
    refine ⟨hts.trans hsW, ?_⟩
    have hc : W \ s ⊆ W \ t := Finset.sdiff_subset_sdiff_right W hts
    rcases hs with hs | hs
    · exact Or.inl (fun ht => hs (K.lower hc ht))
    · by_cases ht : W \ t ∈ K
      · exact Or.inr (hUp hs ht hc)
      · exact Or.inl ht

/-- Projection happens only after the raw endpoint has been constructed. -/
def protectedEndpoint (W : Finset V) (K : Family V) (H : Finset (Finset V))
    (hUp : ∀ {T U}, T ∈ H → U ∈ K → T ⊆ U → U ∈ H) :
    PreAbstractSimplicialComplex V := project (rawEndpoint W K H hUp)

/-- Ordered, disjoint, exhaustive raw face data. Pairwise disjointness is over
OCCURRENCES in the list, and therefore excludes repeated symbols as well.
The indexed covers field uses the actual List.get API. -/
structure Word (W : Finset V) (K : Family V) where
  word : List (Symbol V)
  supported : OriginalLabelTwoSum.Supported W K
  pair_data : ∀ L v, Symbol.pair L v ∈ word →
    L ∈ K ∧ insert v L ∈ K ∧ v ∉ L
  critical_data : ∀ S, Symbol.critical S ∈ word → S ∈ K
  partition : word.Pairwise (fun σ τ => Disjoint σ.faces τ.faces)
  covers : ∀ s, s ∈ K ↔ ∃ i : Fin word.length, s ∈ (word.get i).faces
  pair_dependency : ∀ («prefix» suffix : List (Symbol V)) L v,
    word = «prefix» ++ Symbol.pair L v :: suffix →
    ∀ T, T ⊂ insert v L → T ≠ L → ∃ σ ∈ «prefix», T ∈ σ.faces
  critical_dependency : ∀ («prefix» suffix : List (Symbol V)) S,
    word = «prefix» ++ Symbol.critical S :: suffix →
    ∀ T, T ⊂ S → ∃ σ ∈ «prefix», T ∈ σ.faces

/-- Protection adds no native output hypothesis. Whole-symbol protection for
pairs is the equivalence below; singleton critical symbols need no duplicate
whole-symbol premise. Properness is conditional on the pair being emitted. -/
structure Contract (W : Finset V) (K : Family V) extends Word W K where
  «protected» : Finset (Finset V)
  protected_subset : ∀ T ∈ «protected», T ∈ K
  protected_upward : ∀ {T U}, T ∈ «protected» → U ∈ K → T ⊆ U → U ∈ «protected»
  protected_pair : ∀ L v, Symbol.pair L v ∈ word →
    (L ∈ «protected» ↔ insert v L ∈ «protected»)
  critical_protected : ∀ S, Symbol.critical S ∈ word → S ∈ «protected»
  emitted_proper : ∀ L v, Symbol.pair L v ∈ word → L ∉ «protected» → insert v L ⊂ W

private theorem split_mem {α : Type*} {x : α} {xs : List α} (hx : x ∈ xs) :
    ∃ left right, xs = left ++ x :: right := by
  revert hx
  induction xs with
  | nil => intro hx; simp at hx
  | cons y ys ih =>
      intro hx
      rcases List.mem_cons.mp hx with he | hx
      · subst y
        exact ⟨[], ys, rfl⟩
      · obtain ⟨left, right, h⟩ := ih hx
        exact ⟨y :: left, right, by simp only [h, List.cons_append]⟩

private theorem prefix_subset {α : Type*} {word «prefix» suffix : List α}
    (h : word = «prefix» ++ suffix) {σ : α} (hσ : σ ∈ «prefix») : σ ∈ word := by
  rw [h]
  exact List.mem_append.mpr (Or.inl hσ)

private theorem suffix_subset {α : Type*} {word «prefix» suffix : List α}
    (h : word = «prefix» ++ suffix) {σ : α} (hσ : σ ∈ suffix) : σ ∈ word := by
  rw [h]
  exact List.mem_append.mpr (Or.inr hσ)

private theorem separated {«prefix» suffix : List (Symbol V)}
    (h : («prefix» ++ suffix).Pairwise (fun σ τ => Disjoint σ.faces τ.faces))
    {σ τ : Symbol V} (hσ : σ ∈ «prefix») (hτ : τ ∈ suffix) :
    Disjoint σ.faces τ.faces := by
  revert h hσ
  induction «prefix» with
  | nil => intro h hσ; simp at hσ
  | cons a xs ih =>
      intro h hσ
      rw [List.cons_append, List.pairwise_cons] at h
      rcases List.mem_cons.mp hσ with he | hσ
      · subst σ
        exact h.1 τ (List.mem_append.mpr (Or.inr hτ))
      · exact ih h.2 hσ

private theorem owner_unique {xs : List (Symbol V)}
    (h : xs.Pairwise (fun σ τ => Disjoint σ.faces τ.faces))
    {σ τ : Symbol V} {T : Finset V} (hσ : σ ∈ xs) (hτ : τ ∈ xs)
    (hTσ : T ∈ σ.faces) (hTτ : T ∈ τ.faces) : σ = τ := by
  revert h hσ hτ
  induction xs with
  | nil => intro h hσ hτ; simp at hσ
  | cons a xs ih =>
      intro h hσ hτ
      rw [List.pairwise_cons] at h
      rcases List.mem_cons.mp hσ with he | hσ
      · subst σ
        rcases List.mem_cons.mp hτ with he | hτ
        · exact he.symm
        · exact (Finset.disjoint_left.mp (h.1 τ hτ) hTσ hTτ).elim
      · rcases List.mem_cons.mp hτ with he | hτ
        · subst τ
          exact (Finset.disjoint_left.mp (h.1 σ hσ) hTτ hTσ).elim
        · exact ih h.2 hσ hτ

private theorem mem_emitted (H : Finset (Finset V)) (xs : List (Symbol V))
    (T : Finset V) : T ∈ emittedFaces H xs ↔ ∃ σ ∈ xs, T ∈ emittedOne H σ := by
  induction xs with
  | nil => simp [emittedFaces]
  | cons σ xs ih =>
      simp only [emittedFaces, Finset.mem_union, ih, List.mem_cons]
      constructor
      · rintro (h | ⟨τ, hτ, hT⟩)
        · exact ⟨σ, Or.inl rfl, h⟩
        · exact ⟨τ, Or.inr hτ, hT⟩
      · rintro ⟨τ, rfl | hτ, hT⟩
        · exact Or.inl hT
        · exact Or.inr ⟨τ, hτ, hT⟩

private theorem emittedOne_subset (H : Finset (Finset V)) (σ : Symbol V) :
    emittedOne H σ ⊆ σ.faces := by
  cases σ with
  | critical S => simp [emittedOne]
  | pair L v =>
      by_cases h : L ∈ H <;> simp [emittedOne, Symbol.faces, h]

private theorem emitted_append (H : Finset (Finset V)) (xs ys : List (Symbol V)) :
    emittedFaces H (xs ++ ys) = emittedFaces H xs ∪ emittedFaces H ys := by
  induction xs with
  | nil => simp [emittedFaces]
  | cons σ xs ih => simp only [List.cons_append, emittedFaces, ih, Finset.union_assoc]

private theorem emitted_critical_append (H : Finset (Finset V))
    (xs : List (Symbol V)) (S : Finset V) :
    emittedFaces H (xs ++ [Symbol.critical S]) = emittedFaces H xs := by
  simp only [emitted_append, emittedFaces, emittedOne, Finset.union_empty]

private theorem emitted_protected_append (H : Finset (Finset V))
    (xs : List (Symbol V)) (L : Finset V) (v : V) (hL : L ∈ H) :
    emittedFaces H (xs ++ [Symbol.pair L v]) = emittedFaces H xs := by
  simp only [emitted_append, emittedFaces, emittedOne, if_pos hL, Finset.union_empty]

private theorem emitted_pair_append (H : Finset (Finset V))
    (xs : List (Symbol V)) (L : Finset V) (v : V) (hL : L ∉ H) :
    emittedFaces H (xs ++ [Symbol.pair L v]) = emittedFaces H xs ∪ {L, insert v L} := by
  simp only [emitted_append, emittedFaces, emittedOne, if_neg hL, Finset.union_empty]

private theorem complement_injective {W a b : Finset V} (ha : a ⊆ W) (hb : b ⊆ W)
    (h : W \ a = W \ b) : a = b := by
  have hc := congrArg (fun q : Finset V => W \ q) h
  simpa only [Finset.sdiff_sdiff_eq_self ha, Finset.sdiff_sdiff_eq_self hb] using hc

private theorem complement_upper {W L : Finset V} {v : V}
    (hU : insert v L ⊆ W) (hv : v ∉ L) :
    insert v (W \ insert v L) = W \ L := by
  have hvW : v ∈ W := hU (Finset.mem_insert_self v L)
  ext x
  by_cases hx : x = v
  · subst x
    simp [hvW, hv]
  · simp [Finset.mem_sdiff, hx]

namespace Contract
variable {W : Finset V} {K : Family V} (d : Contract W K)

private theorem face_valid {σ : Symbol V} (hσ : σ ∈ d.word)
    {T : Finset V} (hT : T ∈ σ.faces) : T ∈ K := by
  cases σ with
  | critical S =>
      have : T = S := by simpa [Symbol.faces] using hT
      subst T
      exact d.critical_data S hσ
  | pair L v =>
      have hd := d.pair_data L v hσ
      rcases (show T = L ∨ T = insert v L by simpa [Symbol.faces] using hT) with rfl | rfl
      · exact hd.1
      · exact hd.2.1

private theorem emitted_valid («prefix» : List (Symbol V))
    (hp : ∀ σ ∈ «prefix», σ ∈ d.word) {r : Finset V}
    (hr : r ∈ emittedFaces d.«protected» «prefix») : r ∈ K ∧ r ∉ d.«protected» := by
  obtain ⟨σ, hσ, hr⟩ := (mem_emitted _ _ _).mp hr
  have hσword := hp σ hσ
  refine ⟨d.face_valid hσword (emittedOne_subset _ _ hr), ?_⟩
  cases σ with
  | critical S => simp [emittedOne] at hr
  | pair L v =>
      by_cases hL : L ∈ d.«protected»
      · simp [emittedOne, hL] at hr
      · have hf : r = L ∨ r = insert v L := by simpa [emittedOne, hL] using hr
        rcases hf with rfl | rfl
        · exact hL
        · exact fun hU => hL ((d.protected_pair L v hσword).mpr hU)

private theorem face_emitted («prefix» : List (Symbol V))
    (hp : ∀ σ ∈ «prefix», σ ∈ d.word) {σ : Symbol V} (hσ : σ ∈ «prefix»)
    {T : Finset V} (hT : T ∈ σ.faces) (hn : T ∉ d.«protected») :
    T ∈ emittedFaces d.«protected» «prefix» := by
  apply (mem_emitted _ _ _).mpr
  refine ⟨σ, hσ, ?_⟩
  cases σ with
  | critical S =>
      have he : T = S := by simpa [Symbol.faces] using hT
      subst T
      exact (hn (d.critical_protected S (hp _ hσ))).elim
  | pair L v =>
      have hL : L ∉ d.«protected» := by
        intro hL
        rcases (show T = L ∨ T = insert v L by simpa [Symbol.faces] using hT) with rfl | rfl
        · exact hn hL
        · exact hn ((d.protected_pair L v (hp _ hσ)).mp hL)
      simpa only [emittedOne, if_neg hL, Symbol.faces] using hT

/-- This is the order-sensitive argument. Split the witnessed emitted symbol
INSIDE «prefix», and apply its dependency at that very occurrence in the full word. -/
private theorem emitted_downward («prefix» suffix : List (Symbol V))
    (hword : d.word = «prefix» ++ suffix) {r T : Finset V}
    (hr : r ∈ emittedFaces d.«protected» «prefix») (hTr : T ⊆ r) :
    T ∈ emittedFaces d.«protected» «prefix» := by
  have hp : ∀ σ ∈ «prefix», σ ∈ d.word := fun _ h => prefix_subset hword h
  have hv := d.emitted_valid «prefix» hp hr
  have hTn : T ∉ d.«protected» := fun h => hv.2 (d.protected_upward h hv.1 hTr)
  obtain ⟨σ, hσ, hrσ⟩ := (mem_emitted _ _ _).mp hr
  cases σ with
  | critical S => simp [emittedOne] at hrσ
  | pair L v =>
      have hface : r ∈ (Symbol.pair L v).faces := emittedOne_subset _ _ hrσ
      have hTU : T ⊆ insert v L := by
        rcases (show r = L ∨ r = insert v L by simpa [Symbol.faces] using hface) with rfl | rfl
        · exact hTr.trans (Finset.subset_insert v r)
        · exact hTr
      by_cases hTUeq : T = insert v L
      · exact d.face_emitted «prefix» hp hσ (by simp [hTUeq, Symbol.faces]) hTn
      by_cases hTLeq : T = L
      · exact d.face_emitted «prefix» hp hσ (by simp [hTLeq, Symbol.faces]) hTn
      obtain ⟨left, right, hprefix⟩ := split_mem hσ
      have hsplit : d.word = left ++ Symbol.pair L v :: (right ++ suffix) := by
        rw [hword, hprefix]
        simp only [List.append_assoc, List.cons_append]
      obtain ⟨τ, hτ, hTτ⟩ := d.pair_dependency left (right ++ suffix) L v hsplit T
        (Finset.ssubset_iff_subset_ne.mpr ⟨hTU, hTUeq⟩) hTLeq
      have hτprefix : τ ∈ «prefix» := by
        rw [hprefix]
        exact List.mem_append.mpr (Or.inl hτ)
      exact d.face_emitted «prefix» hp hτprefix hTτ hTn

private theorem current_downward («prefix» suffix : List (Symbol V))
    (hword : d.word = «prefix» ++ suffix) {s t : Finset V}
    (hs : RawFaces W K (emittedFaces d.«protected» «prefix») s)
    (hts : t ⊆ s) (ht : t.Nonempty) :
    RawFaces W K (emittedFaces d.«protected» «prefix») t := by
  refine ⟨ht, hts.trans hs.2.1, ?_⟩
  by_cases hr : W \ t ∈ emittedFaces d.«protected» «prefix»
  · have hc := Finset.sdiff_subset_sdiff_right W hts
    have he := d.emitted_downward «prefix» suffix hword hr hc
    have hv := d.emitted_valid «prefix» (fun _ h => prefix_subset hword h) hr
    have hK : W \ s ∈ K := K.lower hc hv.1
    exact (hs.2.2.elim (fun h => h hK) (fun h => h he)).elim
  · exact Or.inr hr

/-- Current carries the actual ordered decomposition, not a membership-only
subword certificate. Its downward-closure field is proved from dependencies. -/
def current («prefix» suffix : List (Symbol V))
    (hword : d.word = «prefix» ++ suffix) : PreAbstractSimplicialComplex V where
  faces := RawFaces W K (emittedFaces d.«protected» «prefix»)
  isRelLowerSet_faces := by
    intro s hs
    exact ⟨hs.1, fun t hts ht => d.current_downward «prefix» suffix hword hs hts ht⟩

private theorem current_mem («prefix» suffix : List (Symbol V))
    (hword : d.word = «prefix» ++ suffix) (s : Finset V) :
    s ∈ d.current «prefix» suffix hword ↔
      s.Nonempty ∧ s ⊆ W ∧ W \ s ∉ emittedFaces d.«protected» «prefix» := by
  change RawFaces W K (emittedFaces d.«protected» «prefix») s ↔ _
  constructor
  · rintro ⟨hs, hsW, hn | hn⟩
    · exact ⟨hs, hsW, fun h => hn
        (d.emitted_valid «prefix» (fun _ h => prefix_subset hword h) h).1⟩
    · exact ⟨hs, hsW, hn⟩
  · rintro ⟨hs, hsW, hn⟩
    exact ⟨hs, hsW, Or.inr hn⟩

private theorem current_emitted_eq (p q p' q' : List (Symbol V))
    (h : d.word = p ++ q) (h' : d.word = p' ++ q')
    (he : emittedFaces d.«protected» p = emittedFaces d.«protected» p') :
    d.current p q h = d.current p' q' h' := by
  apply SetLike.coe_injective
  ext s
  change RawFaces W K (emittedFaces d.«protected» p) s ↔
    RawFaces W K (emittedFaces d.«protected» p') s
  rw [he]

/-- A suffix face is present only when its complement is nonempty. In particular
this lemma deliberately excludes a critical S=W. -/
private theorem current_complement_mem («prefix» suffix : List (Symbol V))
    (hword : d.word = «prefix» ++ suffix) {σ : Symbol V} (hσ : σ ∈ suffix)
    {a : Finset V} (ha : a ∈ σ.faces) (hap : a ⊂ W) :
    W \ a ∈ d.current «prefix» suffix hword := by
  have hn : a ∉ emittedFaces d.«protected» «prefix» := by
    intro hr
    obtain ⟨τ, hτ, haτ⟩ := (mem_emitted _ _ _).mp hr
    have hd := separated (hword ▸ d.partition) hτ hσ
    exact Finset.disjoint_left.mp hd (emittedOne_subset _ _ haτ) ha
  apply (d.current_mem «prefix» suffix hword _).mpr
  refine ⟨?_, Finset.sdiff_subset, ?_⟩
  · rw [Finset.sdiff_nonempty]
    intro h
    exact hap.ne (Finset.Subset.antisymm hap.subset h)
  · simpa only [Finset.sdiff_sdiff_eq_self hap.subset] using hn

private theorem current_free («prefix» suffix : List (Symbol V)) L v
    (hword : d.word = «prefix» ++ Symbol.pair L v :: suffix) (hL : L ∉ d.«protected»)
    (s : Finset V) (hs : s ∈ d.current «prefix» (Symbol.pair L v :: suffix) hword)
    (hls : W \ insert v L ⊂ s) : s = W \ L := by
  have hpair : Symbol.pair L v ∈ d.word := suffix_subset hword (by simp)
  have hd := d.pair_data L v hpair
  have hs' := (d.current_mem _ _ hword s).mp hs
  have hcU : W \ s ⊆ insert v L := by
    intro x hx
    by_contra hn
    exact (Finset.mem_sdiff.mp hx).2 (hls.subset
      (Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hx).1, hn⟩))
  have hcUne : W \ s ≠ insert v L := by
    intro he
    have hh := congrArg (fun q : Finset V => W \ q) he
    have hsEq : s = W \ insert v L := by
      simpa only [Finset.sdiff_sdiff_eq_self hs'.2.1] using hh
    exact hls.ne hsEq.symm
  by_cases hcL : W \ s = L
  · have hh := congrArg (fun q : Finset V => W \ q) hcL
    simpa only [Finset.sdiff_sdiff_eq_self hs'.2.1] using hh
  have hcnot : W \ s ∉ d.«protected» := by
    intro h
    have hU := d.protected_upward h hd.2.1 hcU
    exact hL ((d.protected_pair L v hpair).mpr hU)
  obtain ⟨σ, hσ, hcσ⟩ := d.pair_dependency «prefix» suffix L v hword (W \ s)
    (Finset.ssubset_iff_subset_ne.mpr ⟨hcU, hcUne⟩) hcL
  have he := d.face_emitted «prefix» (fun _ h => prefix_subset hword h) hσ hcσ hcnot
  exact (hs'.2.2 he).elim

/-- Actual native pair: lower W\\U, unchanged apex v, upper W\\L. -/
def nativePair («prefix» suffix : List (Symbol V)) (L : Finset V) (v : V)
    (hword : d.word = «prefix» ++ Symbol.pair L v :: suffix) (hL : L ∉ d.«protected») :
    CollapsePair V := by
  have hpair : Symbol.pair L v ∈ d.word := suffix_subset hword (by simp)
  have hd := d.pair_data L v hpair
  have hproper := d.emitted_proper L v hpair hL
  have hu := complement_upper hproper.subset hd.2.2
  refine {
    ambient := d.current «prefix» (Symbol.pair L v :: suffix) hword
    lower := W \ insert v L
    apex := v
    lower_nonempty := ?_
    apex_notMem := ?_
    upper_mem := ?_
    free := ?_ }
  · rw [Finset.sdiff_nonempty]
    intro h
    exact hproper.ne (Finset.Subset.antisymm hproper.subset h)
  · simp only [Finset.mem_sdiff, Finset.mem_insert_self, not_true_eq_false, and_false,
      not_false_eq_true]
  · rw [hu]
    exact d.current_complement_mem «prefix» (Symbol.pair L v :: suffix) hword
      (σ := Symbol.pair L v) (a := L)
      (by simp) (by simp [Symbol.faces])
      (lt_of_le_of_lt (Finset.subset_insert v L) hproper)
  · intro s hs hls
    rw [hu]
    exact d.current_free «prefix» suffix L v hword hL s hs hls

private theorem nativePair_retained («prefix» suffix : List (Symbol V)) L v
    (hword : d.word = «prefix» ++ Symbol.pair L v :: suffix) (hL : L ∉ d.«protected»)
    (hnext : d.word = («prefix» ++ [Symbol.pair L v]) ++ suffix) :
    (d.nativePair «prefix» suffix L v hword hL).retained =
      d.current («prefix» ++ [Symbol.pair L v]) suffix hnext := by
  have hpair : Symbol.pair L v ∈ d.word := suffix_subset hword (by simp)
  have hd := d.pair_data L v hpair
  have hUW := d.supported _ hd.2.1
  have hLW := d.supported _ hd.1
  have hu := complement_upper hUW hd.2.2
  apply SetLike.coe_injective
  ext s
  change s ∈ (d.nativePair «prefix» suffix L v hword hL).retained ↔
    s ∈ d.current («prefix» ++ [Symbol.pair L v]) suffix hnext
  rw [(d.nativePair «prefix» suffix L v hword hL).mem_retained_iff]
  change (s ∈ d.current «prefix» (Symbol.pair L v :: suffix) hword ∧
    s ≠ W \ insert v L ∧ s ≠ insert v (W \ insert v L)) ↔ _
  rw [hu, d.current_mem, d.current_mem, emitted_pair_append _ _ _ _ hL]
  constructor
  · rintro ⟨⟨hs, hsW, hn⟩, hl, hupp⟩
    refine ⟨hs, hsW, ?_⟩
    intro hr
    rcases Finset.mem_union.mp hr with hr | hr
    · exact hn hr
    · rcases (show W \ s = L ∨ W \ s = insert v L by simpa using hr) with he | he
      · apply hupp
        have hh := congrArg (fun q : Finset V => W \ q) he
        simpa only [Finset.sdiff_sdiff_eq_self hsW] using hh
      · apply hl
        have hh := congrArg (fun q : Finset V => W \ q) he
        simpa only [Finset.sdiff_sdiff_eq_self hsW] using hh
  · rintro ⟨hs, hsW, hn⟩
    refine ⟨⟨hs, hsW, fun hr => hn (Finset.mem_union.mpr (Or.inl hr))⟩, ?_, ?_⟩
    · intro he
      apply hn
      apply Finset.mem_union.mpr
      right
      rw [he, Finset.sdiff_sdiff_eq_self hUW]
      simp
    · intro he
      apply hn
      apply Finset.mem_union.mpr
      right
      rw [he, Finset.sdiff_sdiff_eq_self hLW]
      simp

/-- The exact nonempty endpoint is the finite raw dual union the nonempty
complements of H. Both complement involutions use explicit support witnesses. -/
theorem protectedEndpoint_mem (s : Finset V) :
    s ∈ protectedEndpoint W K d.«protected» d.protected_upward ↔
      s ∈ project (rawDual W K) ∨
        (s.Nonempty ∧ ∃ T ∈ d.«protected», s = W \ T) := by
  change (s.Nonempty ∧ s ⊆ W ∧ (W \ s ∉ K ∨ W \ s ∈ d.«protected»)) ↔ _
  constructor
  · rintro ⟨hs, hsW, hn | hh⟩
    · exact Or.inl ⟨hs, (mem_rawDual W K s).mpr ⟨hsW, hn⟩⟩
    · exact Or.inr ⟨hs, W \ s, hh, (Finset.sdiff_sdiff_eq_self hsW).symm⟩
  · rintro (⟨hs, hd⟩ | ⟨hs, T, hT, rfl⟩)
    · obtain ⟨hsW, hn⟩ := (mem_rawDual W K s).mp hd
      exact ⟨hs, hsW, Or.inl hn⟩
    · have hTW := d.supported T (d.protected_subset T hT)
      exact ⟨hs, Finset.sdiff_subset,
        Or.inr (by simpa only [Finset.sdiff_sdiff_eq_self hTW] using hT)⟩

private theorem emitted_terminal {T : Finset V} (hT : T ∈ K) :
    T ∈ emittedFaces d.«protected» d.word ↔ T ∉ d.«protected» := by
  constructor
  · exact fun h => (d.emitted_valid d.word (fun _ h => h) h).2
  · intro hn
    obtain ⟨i, hi⟩ := (d.covers T).mp hT
    have hm : d.word.get i ∈ d.word := List.mem_iff_get.mpr ⟨i, rfl⟩
    exact d.face_emitted d.word (fun _ h => h) hm hi hn

private theorem current_terminal («prefix» : List (Symbol V))
    (hword : d.word = «prefix» ++ []) :
    d.current «prefix» [] hword = protectedEndpoint W K d.«protected» d.protected_upward := by
  classical
  have hp : «prefix» = d.word := by simpa only [List.append_nil] using hword.symm
  apply SetLike.coe_injective
  ext s
  change s ∈ d.current «prefix» [] hword ↔
    s ∈ protectedEndpoint W K d.«protected» d.protected_upward
  rw [d.current_mem]
  change (s.Nonempty ∧ s ⊆ W ∧ W \ s ∉ emittedFaces d.«protected» «prefix») ↔
    (s.Nonempty ∧ s ⊆ W ∧ (W \ s ∉ K ∨ W \ s ∈ d.«protected»))
  rw [hp]
  constructor
  · rintro ⟨hs, hsW, hn⟩
    refine ⟨hs, hsW, ?_⟩
    by_cases hc : W \ s ∈ K
    · right
      by_contra hh
      exact hn ((d.emitted_terminal hc).mpr hh)
    · exact Or.inl hc
  · intro hs
    have hsEndpoint : s ∈ protectedEndpoint W K d.«protected» d.protected_upward := hs
    rcases (d.protectedEndpoint_mem s).mp hsEndpoint with hd | ⟨hsn, T, hT, heq⟩
    · obtain ⟨hsn, hd⟩ := hd
      obtain ⟨hsW, hn⟩ := (mem_rawDual W K s).mp hd
      exact ⟨hsn, hsW, fun he => hn
        (d.emitted_valid d.word (fun _ h => h) he).1⟩
    · have hTW := d.supported T (d.protected_subset T hT)
      have hsW : s ⊆ W := by rw [heq]; exact Finset.sdiff_subset
      refine ⟨hsn, hsW, ?_⟩
      intro he
      have hv := d.emitted_valid d.word (fun _ h => h) he
      have hc : W \ T = W \ (W \ s) :=
        heq.symm.trans (Finset.sdiff_sdiff_eq_self hsW).symm
      have hTc : T = W \ s := complement_injective hTW Finset.sdiff_subset hc
      exact hv.2 (hTc ▸ hT)

private def suffixSequence : (suffix «prefix» : List (Symbol V)) →
    (hword : d.word = «prefix» ++ suffix) →
    Sequence (d.current «prefix» suffix hword)
      (protectedEndpoint W K d.«protected» d.protected_upward)
  | [], «prefix», hword =>
      (Sequence.refl _).cast rfl (d.current_terminal «prefix» hword)
  | Symbol.critical S :: tail, «prefix», hword => by
      have hnext : d.word = («prefix» ++ [Symbol.critical S]) ++ tail := by
        simpa only [List.append_assoc, List.cons_append, List.nil_append] using hword
      have T := suffixSequence tail («prefix» ++ [Symbol.critical S]) hnext
      have he := d.current_emitted_eq «prefix» (Symbol.critical S :: tail)
        («prefix» ++ [Symbol.critical S]) tail hword hnext
        (emitted_critical_append d.«protected» «prefix» S).symm
      exact T.cast he.symm rfl
  | Symbol.pair L v :: tail, «prefix», hword => by
      have hnext : d.word = («prefix» ++ [Symbol.pair L v]) ++ tail := by
        simpa only [List.append_assoc, List.cons_append, List.nil_append] using hword
      have T := suffixSequence tail («prefix» ++ [Symbol.pair L v]) hnext
      by_cases hL : L ∈ d.«protected»
      · have he := d.current_emitted_eq «prefix» (Symbol.pair L v :: tail)
          («prefix» ++ [Symbol.pair L v]) tail hword hnext
          (emitted_protected_append d.«protected» «prefix» L v hL).symm
        exact T.cast he.symm rfl
      · exact Sequence.step (d.nativePair «prefix» tail L v hword hL)
          (T.cast (d.nativePair_retained «prefix» tail L v hword hL hnext).symm rfl)

/-- Universal corrected P02. No critical nonemptiness, nonvoid assumption,
no-ghost assumption, or properness of «protected» uppers occurs in this telescope. -/
def protectedDualWordSequence :
    Sequence (simplex W) (protectedEndpoint W K d.«protected» d.protected_upward) := by
  have hword : d.word = [] ++ d.word := rfl
  have S := d.suffixSequence d.word [] hword
  have hstart : d.current [] d.word hword = simplex W := by
    apply SetLike.coe_injective
    ext s
    change s ∈ d.current [] d.word hword ↔ s ∈ simplex W
    rw [d.current_mem]
    change (s.Nonempty ∧ s ⊆ W ∧ W \ s ∉ (∅ : Finset (Finset V))) ↔
      (s.Nonempty ∧ s ⊆ W)
    simp only [Finset.notMem_empty, not_false_eq_true, and_true]
  exact S.cast hstart rfl

end Contract

/-- Finite raw collection of critical faces. Empty criticals are retained. -/
def criticalFaces : List (Symbol V) → Finset (Finset V)
  | [] => ∅
  | Symbol.pair _ _ :: xs => criticalFaces xs
  | Symbol.critical S :: xs => insert S (criticalFaces xs)

private theorem mem_criticalFaces (xs : List (Symbol V)) (S : Finset V) :
    S ∈ criticalFaces xs ↔ Symbol.critical S ∈ xs := by
  induction xs with
  | nil => simp [criticalFaces]
  | cons σ xs ih =>
      cases σ <;> simp [criticalFaces, ih]

namespace Word
variable {W : Finset V} {K : Family V} (d : Word W K)

/-- A substantive H=empty consumer: the no-critical condition constructs the
all-critical protection obligation, rather than being an unused extra premise. -/
def noCritical_unprotected
    (hcrit : ∀ σ ∈ d.word, ¬ σ.isCritical)
    (hproper : ∀ L v, Symbol.pair L v ∈ d.word → insert v L ⊂ W) :
    Sequence (simplex W) (project (rawDual W K)) := by
  let c : Contract W K := {
    toWord := d
    «protected» := ∅
    protected_subset := by simp
    protected_upward := by intro T U h; exact (Finset.notMem_empty T h).elim
    protected_pair := by intro L v h; simp
    critical_protected := by
      intro S hS
      exact (hcrit _ hS (by trivial)).elim
    emitted_proper := by intro L v h _; exact hproper L v h }
  have he : protectedEndpoint W K c.«protected» c.protected_upward = project (rawDual W K) := by
    apply SetLike.coe_injective
    ext s
    change s ∈ protectedEndpoint W K c.«protected» c.protected_upward ↔
      s ∈ project (rawDual W K)
    simpa only [c, Finset.notMem_empty, false_and, exists_false, and_false, or_false]
      using c.protectedEndpoint_mem s
  exact c.protectedDualWordSequence.cast rfl he

/-- Maximal critical faces make their own protection upward in K. Disjoint
partition ownership shows no pair face belongs to this protection, so whole
symbols are «protected». All emitted-pair properness remains explicit. -/
def maximalCritical_protected
    (hmax : ∀ S, Symbol.critical S ∈ d.word → ∀ T ∈ K, S ⊆ T → T = S)
    (hproper : ∀ L v, Symbol.pair L v ∈ d.word → insert v L ⊂ W) :
    Sequence (simplex W)
      (protectedEndpoint W K (criticalFaces d.word) (by
        intro S T hS hT hST
        have hc := (mem_criticalFaces d.word S).mp hS
        rw [hmax S hc T hT hST]
        exact hS)) := by
  have hUp : ∀ {S T}, S ∈ criticalFaces d.word → T ∈ K → S ⊆ T →
      T ∈ criticalFaces d.word := by
    intro S T hS hT hST
    have hc := (mem_criticalFaces d.word S).mp hS
    rw [hmax S hc T hT hST]
    exact hS
  have hpairNone : ∀ L v, Symbol.pair L v ∈ d.word →
      L ∉ criticalFaces d.word ∧ insert v L ∉ criticalFaces d.word := by
    intro L v hp
    constructor
    · intro hL
      have hc := (mem_criticalFaces d.word L).mp hL
      have he := owner_unique d.partition hp hc
        (show L ∈ (Symbol.pair L v).faces by simp [Symbol.faces])
        (show L ∈ (Symbol.critical L).faces by simp [Symbol.faces])
      cases he
    · intro hU
      have hc := (mem_criticalFaces d.word (insert v L)).mp hU
      have he := owner_unique d.partition hp hc
        (show insert v L ∈ (Symbol.pair L v).faces by simp [Symbol.faces])
        (show insert v L ∈ (Symbol.critical (insert v L)).faces by simp [Symbol.faces])
      cases he
  let c : Contract W K := {
    toWord := d
    «protected» := criticalFaces d.word
    protected_subset := by
      intro T hT
      exact d.critical_data T ((mem_criticalFaces d.word T).mp hT)
    protected_upward := hUp
    protected_pair := by
      intro L v hp
      have hn := hpairNone L v hp
      exact ⟨fun h => (hn.1 h).elim, fun h => (hn.2 h).elim⟩
    critical_protected := by
      intro S hS
      exact (mem_criticalFaces d.word S).mpr hS
    emitted_proper := by intro L v hp _; exact hproper L v hp }
  exact c.protectedDualWordSequence

end Word
end D5.S3.Geometry.FiniteProtectedDualWord
