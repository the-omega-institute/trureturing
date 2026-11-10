/- GID: D5/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain
   generality: G
   mirror-B: D5/B/S3/Geometry/OriginalLabelTwoSum/PhysicalClosedChain
   mirror-E: none(waiver:original-label-physical-closed-chain)
   anchors: [mathlib/module/Mathlib.Combinatorics.SimpleGraph.Acyclic]
   utility: none
   digest: Literal finite K4/W4 closed chains in one ambient consume actual graph histories, exact critical and ground formulas, and both native sequences. -/
import D5.S3.Geometry.OriginalLabelTwoSum.PhysicalHistory

/-! SOURCE_ONLY_UNCOMPILED. Ordinary route: released T09, with T03/T04/T05/T08.
The number n counts attachments of W4, not the rim width of a variable wheel.
All prefixes use Fin(3+4*n+ghosts). The public construction takes ONLY n, ghosts,
and a prefix length bound. No graph, fresh supply, invariant, certificate, root,
collapse, list formula, or desired endpoint is an external input.

Source index (j,i) means the original mathematical label r(j+1,i+1).
Thus block j has values 3+4*j,...,6+4*j; its local G3 label zero is the
interface, and its local labels 1,2,3,4 are those four values. The literal
sum carrier, total label map, physical chord indices, actual unique paths,
raw root and native Sequence/Certificate authorities are imported unchanged.
No claim about Lean/native/Reg/official acceptance is made here. -/
noncomputable section
open Set Finset SimpleGraph
open scoped unitInterval ContinuousMap
namespace D5.S3.Geometry.OriginalLabelTwoSum.PhysicalClosedChain
open FiniteElementaryCollapse FiniteRelativeSimplicialCollapse FiniteSimplicialJoin

abbrev Ambient (n ghosts : Nat) : Type := PhysicalHistory.Ambient n ghosts

def p (n ghosts : Nat) : Ambient n ghosts := ⟨0,by omega⟩
def u (n ghosts : Nat) : Ambient n ghosts := ⟨1,by omega⟩
def v (n ghosts : Nat) : Ambient n ghosts := ⟨2,by omega⟩

/-- Zero-based block/offset, with an explicit finite bound, never an infinite
fresh supply in a finite type. Offset 0 is mathematical r(j+1,1). -/
def r (n ghosts j : Nat) (hj : j < n) (i : Fin 4) : Ambient n ghosts :=
  ⟨3+4*j+i.val,by have := i.isLt; omega⟩

/-- e1=u and e_(j+2)=r(j+1,1) in the one-based mathematical convention. -/
def interface (n ghosts k : Nat) (hk : k ≤ n) : Ambient n ghosts :=
  if h : k = 0 then u n ghosts else r n ghosts (k-1) (by omega) 0

/-- Exactly the union of offsets 2,3 in all blocks j<k. The equivalent
explicit union is proved below; the filter makes all prefix bounds literal. -/
def S (n ghosts k : Nat) : Finset (Ambient n ghosts) :=
  Finset.univ.filter (fun x => 3 ≤ x.val ∧ x.val < 3+4*k ∧
    ((x.val-3)%4 = 2 ∨ (x.val-3)%4 = 3))

def first (n ghosts k : Nat) (hk : k ≤ n) : Finset (Ambient n ghosts) :=
  insert (interface n ghosts k hk) (S n ghosts k)

def second (n ghosts k : Nat) : Finset (Ambient n ghosts) :=
  insert (v n ghosts) (S n ghosts k)

/-- The block coordinates that are never selected for physical deletion. -/
def tail (n ghosts k : Nat) : Finset (Ambient n ghosts) :=
  Finset.univ.filter (fun x => 3 ≤ x.val ∧ x.val < 3+4*k ∧ (x.val-3)%4 ≠ 0)

def retained (n ghosts k : Nat) (hk : k ≤ n) : Finset (Ambient n ghosts) :=
  {p n ghosts,v n ghosts,interface n ghosts k hk} ∪ tail n ghosts k

private def seedLabels (n ghosts : Nat) : K4.SeedLabel ↪ Ambient n ghosts where
  toFun i := ⟨i.val,by have := i.isLt; omega⟩
  inj' := by intro a b h; exact Fin.ext (congrArg Fin.val h)

private theorem interface_succ (n ghosts k : Nat) (hk : k+1 ≤ n) :
    interface n ghosts (k+1) hk = r n ghosts k (by omega) 0 := by
  simp [interface]

private theorem interface_bound (n ghosts k : Nat) (hk : k ≤ n) :
    (interface n ghosts k hk).val < 3+4*k := by
  by_cases h : k = 0
  · subst k; simp [interface,u]
  · simp only [interface,dif_neg h,r]
    omega

private theorem p_ne_interface (n ghosts k : Nat) (hk : k ≤ n) :
    p n ghosts ≠ interface n ghosts k hk := by
  intro h
  have hv := congrArg Fin.val h
  by_cases h0 : k = 0
  · simp [interface,h0,p,u] at hv
  · simp only [interface,dif_neg h0,p,r] at hv
    omega

private theorem interface_not_S (n ghosts k : Nat) (hk : k ≤ n) :
    interface n ghosts k hk ∉ S n ghosts k := by
  intro h
  have hval : 3 ≤ (interface n ghosts k hk).val ∧
      (interface n ghosts k hk).val < 3+4*k ∧
      (((interface n ghosts k hk).val-3)%4 = 2 ∨
        ((interface n ghosts k hk).val-3)%4 = 3) := by simpa [S] using h
  by_cases h0 : k = 0
  · simp [interface,h0,u] at hval
  · simp only [interface,dif_neg h0,r] at hval
    omega

private theorem interface_not_second (n ghosts k : Nat) (hk : k ≤ n) :
    interface n ghosts k hk ∉ second n ghosts k := by
  have hne : interface n ghosts k hk ≠ v n ghosts := by
    intro he
    have hv := congrArg Fin.val he
    by_cases h0 : k = 0
    · simp [interface,h0,u,v] at hv
    · simp only [interface,dif_neg h0,r,v] at hv
      omega
  simp only [second,Finset.mem_insert,not_or]
  exact ⟨hne,interface_not_S n ghosts k hk⟩

private theorem S_zero (n ghosts : Nat) : S n ghosts 0 = ∅ := by
  ext x
  simp only [S,Finset.mem_filter,Finset.mem_univ,true_and,Finset.not_mem_empty] <;> omega

/-- An explicit union of the ORIGINAL r(j+1,3),r(j+1,4) values. -/
theorem S_union (n ghosts k : Nat) (hk : k ≤ n) :
    S n ghosts k = (Finset.range k).attach.biUnion (fun j =>
      {r n ghosts j.1 (by have := Finset.mem_range.mp j.2; omega) 2,
       r n ghosts j.1 (by have := Finset.mem_range.mp j.2; omega) 3}) := by
  ext x
  simp only [S,Finset.mem_filter,Finset.mem_univ,true_and,
    Finset.mem_biUnion,Finset.mem_attach,true_and,Finset.mem_insert,Finset.mem_singleton]
  constructor
  · intro hx
    let j := (x.val-3)/4
    have hj : j < k := by dsimp [j]; omega
    refine ⟨⟨j,Finset.mem_range.mpr hj⟩,?_⟩
    rcases hx.2.2 with h2 | h3
    · left; apply Fin.ext; dsimp [r,j]; omega
    · right; apply Fin.ext; dsimp [r,j]; omega
  · rintro ⟨j,hx | hx⟩ <;> subst x <;>
      have hj := Finset.mem_range.mp j.2 <;> dsimp [r] <;> omega

/-- The retained block tail is the explicit union of offsets 1,2,3. -/
theorem tail_union (n ghosts k : Nat) (hk : k ≤ n) :
    tail n ghosts k = (Finset.range k).attach.biUnion (fun j =>
      {r n ghosts j.1 (by have := Finset.mem_range.mp j.2; omega) 1,
       r n ghosts j.1 (by have := Finset.mem_range.mp j.2; omega) 2,
       r n ghosts j.1 (by have := Finset.mem_range.mp j.2; omega) 3}) := by
  ext x
  simp only [tail,Finset.mem_filter,Finset.mem_univ,true_and,
    Finset.mem_biUnion,Finset.mem_attach,true_and,Finset.mem_insert,Finset.mem_singleton]
  constructor
  · intro hx
    let j := (x.val-3)/4
    have hj : j < k := by dsimp [j]; omega
    refine ⟨⟨j,Finset.mem_range.mpr hj⟩,?_⟩
    have hm : (x.val-3)%4 = 1 ∨ (x.val-3)%4 = 2 ∨ (x.val-3)%4 = 3 := by omega
    rcases hm with h1 | h2 | h3
    · left; apply Fin.ext; dsimp [r,j]; omega
    · right; left; apply Fin.ext; dsimp [r,j]; omega
    · right; right; apply Fin.ext; dsimp [r,j]; omega
  · rintro ⟨j,hx | hx | hx⟩ <;> subst x <;>
      have hj := Finset.mem_range.mp j.2 <;> dsimp [r] <;> omega

private theorem S_succ (n ghosts k : Nat) (hk : k < n) :
    S n ghosts (k+1) = S n ghosts k ∪ {r n ghosts k hk 2,r n ghosts k hk 3} := by
  ext x
  simp only [S,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_union,
    Finset.mem_insert,Finset.mem_singleton,Fin.ext_iff,r]
  omega

private theorem critical_recurrence (n ghosts k : Nat) (hk : k < n) :
    wheelCell (interface n ghosts k (by omega)) (r n ghosts k hk 0)
        (r n ghosts k hk 2) (r n ghosts k hk 3) (first n ghosts k (by omega)) =
      first n ghosts (k+1) (by omega) ∧
    wheelCell (interface n ghosts k (by omega)) (r n ghosts k hk 0)
        (r n ghosts k hk 2) (r n ghosts k hk 3) (second n ghosts k) =
      second n ghosts (k+1) := by
  constructor
  · simp only [first,wheelCell,Finset.mem_insert_self,if_pos,
      Finset.erase_insert (interface_not_S n ghosts k (by omega)),S_succ n ghosts k hk,
      interface_succ]
    ext x
    simp only [Finset.mem_insert,Finset.mem_union,Finset.mem_singleton]
    tauto
  · simp only [wheelCell,if_neg (interface_not_second n ghosts k (by omega)),
      second,S_succ n ghosts k hk]
    ext x
    simp only [Finset.mem_insert,Finset.mem_union,Finset.mem_singleton]
    tauto

private def orientedEdge {A : Type} {n ghosts : Nat}
    (g : GraphData A (Ambient n ghosts)) (e : Ambient n ghosts) :
    {ab : A × A // g.edge e = s(ab.1,ab.2)} := by
  have hex : ∃ a b : A, g.edge e = s(a,b) := by
    have all : ∀ d : Sym2 A, ∃ a b : A, d = s(a,b) := by
      apply Sym2.ind
      intro a b
      exact ⟨a,b,rfl⟩
    exact all (g.edge e)
  let a := Classical.choose hex
  let hb := Classical.choose_spec hex
  exact ⟨(a,Classical.choose hb),Classical.choose_spec hb⟩

/-- Internal constructor consumes proved prefix facts; build below supplies
them inductively. Its choice orients an actual total graph edge only. -/
private def nextInput {A : Type} {n ghosts k : Nat}
    (g : GraphData A (Ambient n ghosts)) (hk : k < n)
    (bound : ∀ x ∈ g.ground, x.val < 3+4*k)
    (he : interface n ghosts k (by omega) ∈ g.ground) : PhysicalHistory.Input g :=
  let ab := orientedEdge g (interface n ghosts k (by omega))
  PhysicalHistory.blockInput g hk bound (interface n ghosts k (by omega)) he
    ab.1.1 ab.1.2 ab.2

private theorem next_value {A : Type} {n ghosts k : Nat}
    (g : GraphData A (Ambient n ghosts)) (hk : k < n)
    (bound : ∀ x ∈ g.ground, x.val < 3+4*k)
    (he : interface n ghosts k (by omega) ∈ g.ground)
    (i : Wheel.Label) (hi : i ≠ 0) :
    ((nextInput g hk bound he).labels i).val = 3+4*k+(i.val-1) := by
  change (if i = 0 then interface n ghosts k (by omega)
    else (⟨3+4*k+(i.val-1),by have := i.isLt; omega⟩ : Ambient n ghosts)).val = _
  rw [if_neg hi]

/-- Literal bounded recursion. Its only stored proof facts are the prefix
bound and retention needed to form the next actual G3 Input. All requested
critical/root/ground/count/list/native conclusions are proved AFTER construction. -/
def build (n ghosts : Nat) : (k : Nat) → (hk : k ≤ n) →
    Σ A : Type, Σ g : GraphData A (Ambient n ghosts),
      {h : PhysicalHistory.History k A g //
        (∀ x ∈ g.ground, x.val < 3+4*k) ∧ interface n ghosts k hk ∈ g.ground}
  | 0, hk => ⟨Fin 4,PhysicalHistory.seedGraph (seedLabels n ghosts),
      PhysicalHistory.History.seed (seedLabels n ghosts),by
        constructor
        · intro x hx
          obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
          exact i.isLt
        · exact Finset.mem_image.mpr ⟨1,Finset.mem_univ _,rfl⟩⟩
  | k+1, hk =>
    let old := build n ghosts k (by omega)
    let g := old.2.1
    let i := nextInput g (by omega : k < n) old.2.2.2.1 old.2.2.2.2
    ⟨(PhysicalHistory.step g i).Carrier,(PhysicalHistory.step g i).data,
      PhysicalHistory.History.attach old.2.2.1 i,by
        constructor
        · intro x hx
          rcases Finset.mem_union.mp hx with hold | hnew
          · have hb := old.2.2.2.1 x (Finset.mem_of_mem_erase hold)
            omega
          · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hnew
            have ha0 : a ≠ (0 : Wheel.Label) := by
              intro h; subst a; exact (by decide : (0 : Wheel.Label) ∉ Wheel.Y) ha
            have hv := next_value g (by omega) old.2.2.2.1 old.2.2.2.2 a ha0
            have := a.isLt
            change (i.labels a).val < _
            change (i.labels a).val = _ at hv
            omega
        · rw [interface_succ]
          apply Finset.mem_union_right
          exact Finset.mem_image.mpr ⟨1,by decide,rfl⟩⟩

abbrev carrier (n ghosts k : Nat) (hk : k ≤ n) : Type := (build n ghosts k hk).1

abbrev graph (n ghosts k : Nat) (hk : k ≤ n) :
    GraphData (carrier n ghosts k hk) (Ambient n ghosts) := (build n ghosts k hk).2.1

abbrev history (n ghosts k : Nat) (hk : k ≤ n) :
    PhysicalHistory.History k (carrier n ghosts k hk) (graph n ghosts k hk) :=
  (build n ghosts k hk).2.2.1

/-- The actual Input used by build, with the same finite ambient at both ends. -/
abbrev input (n ghosts k : Nat) (hk : k < n) :
    PhysicalHistory.Input (graph n ghosts k (by omega)) :=
  nextInput (graph n ghosts k (by omega)) hk
    (build n ghosts k (by omega)).2.2.2.1 (build n ghosts k (by omega)).2.2.2.2

theorem history_succ (n ghosts k : Nat) (hk : k+1 ≤ n) :
    history n ghosts (k+1) hk = PhysicalHistory.History.attach
      (history n ghosts k (by omega)) (input n ghosts k (by omega)) := rfl

/-- Explicit local G3 zero/1-based to global zero-based label translation. -/
theorem input_labels (n ghosts k : Nat) (hk : k < n) :
    (input n ghosts k hk).e = interface n ghosts k (by omega) ∧
    (input n ghosts k hk).labels 0 = interface n ghosts k (by omega) ∧
    (input n ghosts k hk).labels 1 = r n ghosts k hk 0 ∧
    (input n ghosts k hk).labels 2 = r n ghosts k hk 1 ∧
    (input n ghosts k hk).labels 3 = r n ghosts k hk 2 ∧
    (input n ghosts k hk).labels 4 = r n ghosts k hk 3 :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- Retention and current-ground freshness are OUTPUTS of the recursion. -/
theorem input_valid (n ghosts k : Nat) (hk : k < n) :
    interface n ghosts k (by omega) ∈ (graph n ghosts k (by omega)).ground ∧
    Disjoint (graph n ghosts k (by omega)).ground
      (Wheel.Y.image (input n ghosts k hk).labels) ∧
    (graph n ghosts k (by omega)).edge (interface n ghosts k (by omega)) =
      s((input n ghosts k hk).a,(input n ghosts k hk).b) :=
  ⟨(input n ghosts k hk).retained,(input n ghosts k hk).fresh,
    (input n ghosts k hk).edge⟩

theorem prefix_bound (n ghosts k : Nat) (hk : k ≤ n) :
    ∀ x ∈ (graph n ghosts k hk).ground, x.val < 3+4*k :=
  (build n ghosts k hk).2.2.2.1

/-- Future blocks are fresh from proved bounds, including blocks beyond the
very next attachment. This is not an input premise of build. -/
theorem future_blocks_fresh (n ghosts k j : Nat) (hk : k ≤ n)
    (hkj : k ≤ j) (hj : j < n) (a : Fin 4) :
    r n ghosts j hj a ∉ (graph n ghosts k hk).ground := by
  intro h
  have hb := prefix_bound n ghosts k hk _ h
  change 3+4*j+a.val < 3+4*k at hb
  omega

/-- Literal K4 raw root in this common finite ambient. -/
theorem seed_root (n ghosts : Nat) :
    (graph n ghosts 0 (by omega)).rows.root =
      delta {p n ghosts} ⊔ delta {u n ghosts} ⊔ delta {v n ghosts} :=
  PhysicalHistory.seed_root (seedLabels n ghosts)

private theorem input_Y (n ghosts k : Nat) (hk : k < n) :
    Wheel.Y.image (input n ghosts k hk).labels =
      {r n ghosts k hk 0,r n ghosts k hk 1,r n ghosts k hk 2,r n ghosts k hk 3} := by
  simp only [Wheel.Y,Finset.image_insert,Finset.image_singleton,
    (input_labels n ghosts k hk).2.2.1,(input_labels n ghosts k hk).2.2.2.1,
    (input_labels n ghosts k hk).2.2.2.2.1,(input_labels n ghosts k hk).2.2.2.2.2]

/-- Derived literal erase/union recurrence of the actual retained graph ground. -/
theorem ground_recurrence (n ghosts k : Nat) (hk : k < n) :
    (graph n ghosts (k+1) (by omega)).ground =
      (graph n ghosts k (by omega)).ground.erase (interface n ghosts k (by omega)) ∪
        {r n ghosts k hk 0,r n ghosts k hk 1,r n ghosts k hk 2,r n ghosts k hk 3} := by
  change (graph n ghosts k (by omega)).ground.erase _ ∪
    Wheel.Y.image (input n ghosts k hk).labels = _
  rw [input_Y]

/-- Total values of all other coordinates are mapped through the actual
left embedding, even when a coordinate has been physically deleted or inactive.
Only membership in the new four-spoke block selects the right total value. -/
theorem total_label_recurrence (n ghosts k : Nat) (hk : k < n)
    (x : Ambient n ghosts) (hx : x ∉ Wheel.Y.image (input n ghosts k hk).labels) :
    (graph n ghosts (k+1) (by omega)).edge x =
      Sym2.map (PhysicalHistory.step (graph n ghosts k (by omega))
        (input n ghosts k hk)).qL ((graph n ghosts k (by omega)).edge x) := by
  change (if x ∈ Wheel.Y.image (input n ghosts k hk).labels then _ else _) = _
  exact if_neg hx

private theorem retained_recurrence (n ghosts k : Nat) (hk : k < n) :
    (retained n ghosts k (by omega)).erase (interface n ghosts k (by omega)) ∪
        {r n ghosts k hk 0,r n ghosts k hk 1,r n ghosts k hk 2,r n ghosts k hk 3} =
      retained n ghosts (k+1) (by omega) := by
  have hp := p_ne_interface n ghosts k (by omega)
  have heT : interface n ghosts k (by omega) ∉ tail n ghosts k := by
    intro h
    have hh : 3 ≤ (interface n ghosts k (by omega)).val ∧
        (interface n ghosts k (by omega)).val < 3+4*k ∧
        ((interface n ghosts k (by omega)).val-3)%4 ≠ 0 := by simpa [tail] using h
    by_cases h0 : k = 0
    · simp [interface,h0,u] at hh
    · simp only [interface,dif_neg h0,r] at hh
      omega
  have hev : v n ghosts ≠ interface n ghosts k (by omega) := by
    intro h
    exact interface_not_second n ghosts k (by omega)
      (Finset.mem_insert.mpr (Or.inl h.symm))
  ext x
  simp only [retained,Finset.mem_union,Finset.mem_erase,Finset.mem_insert,
    Finset.mem_singleton,tail,Finset.mem_filter,Finset.mem_univ,true_and,interface_succ]
  have hxI := interface_bound n ghosts k (by omega)
  have hnT : x = interface n ghosts k (by omega) →
      ¬ (3 ≤ x.val ∧ x.val < 3+4*k ∧ (x.val-3)%4 ≠ 0) := by
    rintro rfl; simpa [tail] using heT
  have hpI : x = p n ghosts → x ≠ interface n ghosts k (by omega) := by
    rintro rfl; exact hp
  have hvI : x = v n ghosts → x ≠ interface n ghosts k (by omega) := by
    rintro rfl; exact hev
  simp only [Fin.ext_iff,p,v,r] at *
  omega

/-- Exact original-label ground, including k=0. Deleted interfaces are not
retained, but their coordinates remain in Ambient n ghosts. -/
theorem ground_formula (n ghosts k : Nat) (hk : k ≤ n) :
    (graph n ghosts k hk).ground = retained n ghosts k hk := by
  induction k with
  | zero =>
    change Finset.univ.image (seedLabels n ghosts) = retained n ghosts 0 hk
    have hu : (Finset.univ : Finset K4.SeedLabel) = {0,1,2} := by decide
    rw [hu]
    ext x
    simp only [Finset.mem_image,Finset.mem_insert,Finset.mem_singleton,retained,
      Finset.mem_union,tail,Finset.mem_filter,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨i,hi,rfl⟩
      rcases hi with rfl | rfl | rfl <;> simp [seedLabels,p,v,interface,u]
    · intro hx
      rcases hx with (hx | hx | hx) | hx
      · exact ⟨0,Or.inl rfl,hx.symm⟩
      · exact ⟨2,Or.inr (Or.inr rfl),hx.symm⟩
      · exact ⟨1,Or.inr (Or.inl rfl),hx.symm⟩
      · omega
  | succ k ih =>
    rw [ground_recurrence n ghosts k (by omega),ih (by omega)]
    exact retained_recurrence n ghosts k (by omega)

/-- This is the disjoint union asserted by the closed-chain formula. -/
theorem ground_disjoint (n ghosts k : Nat) (hk : k ≤ n) :
    Disjoint ({p n ghosts,v n ghosts,interface n ghosts k hk} : Finset (Ambient n ghosts))
      (tail n ghosts k) := by
  apply Finset.disjoint_left.mpr
  intro x hx ht
  have hh : 3 ≤ x.val ∧ x.val < 3+4*k ∧ (x.val-3)%4 ≠ 0 := by simpa [tail] using ht
  simp only [Finset.mem_insert,Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl
  · simp [p] at hh
  · simp [v] at hh
  · by_cases h0 : k = 0
    · simp [interface,h0,u] at hh
    · simp only [interface,dif_neg h0,r] at hh
      omega

/-- All earlier first spokes are physically absent from retained ground. -/
theorem earlier_interfaces_deleted (n ghosts k j : Nat) (hk : k ≤ n)
    (hj : j+1 < k) : r n ghosts j (by omega) 0 ∉ (graph n ghosts k hk).ground := by
  rw [ground_formula]
  intro h
  simp only [retained,Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at h
  have hv : (r n ghosts j (by omega) 0).val = 3+4*j := rfl
  rcases h with (h | h | h) | h
  · have := congrArg Fin.val h; simp only [r,p] at this; omega
  · have := congrArg Fin.val h; simp only [r,v] at this; omega
  · have := congrArg Fin.val h
    have h0 : k ≠ 0 := by omega
    simp only [r,interface,dif_neg h0] at this
    omega
  · have hh : 3 ≤ (r n ghosts j (by omega) 0).val ∧
        (r n ghosts j (by omega) 0).val < 3+4*k ∧
        ((r n ghosts j (by omega) 0).val-3)%4 ≠ 0 := by simpa [tail] using h
    rw [hv] at hh
    omega

/-- No inactive future block or ambient ghost can occur in retained ground
or in any raw root face. This retains the actual total ambient type. -/
theorem inactive (n ghosts k : Nat) (hk : k ≤ n) (x : Ambient n ghosts)
    (hx : 3+4*k ≤ x.val) :
    x ∉ (graph n ghosts k hk).ground ∧
    ∀ s ∈ (graph n ghosts k hk).rows.root, x ∉ s := by
  have hn : x ∉ (graph n ghosts k hk).ground := by
    intro h; have := prefix_bound n ghosts k hk x h; omega
  exact ⟨hn,fun s hs hxs => hn ((graph n ghosts k hk).rows.root_supported s hs hxs)⟩

/-- Exact equality of ACTUAL certificate critical faces, including the seed. -/
theorem critical_formula (n ghosts k : Nat) (hk : k ≤ n) :
    (PhysicalHistory.certificate (history n ghosts k hk)).critical =
      {first n ghosts k hk,second n ghosts k} := by
  induction k with
  | zero =>
    change (K4.seed.critical.image (fun t => t.image (seedLabels n ghosts))) = _
    simp [K4.seed,first,second,S_zero,interface,seedLabels,u,v]
  | succ k ih =>
    change (PhysicalCertificate.certificate (graph n ghosts k (by omega))
      (input n ghosts k (by omega)).e (input n ghosts k (by omega)).retained
      (input n ghosts k (by omega)).a (input n ghosts k (by omega)).b
      (input n ghosts k (by omega)).edge (input n ghosts k (by omega)).labels
      (input n ghosts k (by omega)).zero (input n ghosts k (by omega)).fresh
      (PhysicalHistory.certificate (history n ghosts k (by omega)))).critical = _
    rw [PhysicalCertificate.certificate_critical,ih (by omega)]
    simp only [Finset.image_insert,Finset.image_singleton,
      (input_labels n ghosts k (by omega)).1,
      (input_labels n ghosts k (by omega)).2.2.1,
      (input_labels n ghosts k (by omega)).2.2.2.2.1,
      (input_labels n ghosts k (by omega)).2.2.2.2.2,
      (critical_recurrence n ghosts k (by omega)).1,
      (critical_recurrence n ghosts k (by omega)).2]

/-- The positive-stage formula in the original one-based mathematical names:
S_(k+1) union {r(k+1,1)} and S_(k+1) union {v}. -/
theorem closed_critical (n ghosts k : Nat) (hk : k < n) :
    (PhysicalHistory.certificate (history n ghosts (k+1) (by omega))).critical =
      {S n ghosts (k+1) ∪ {r n ghosts k hk 0},S n ghosts (k+1) ∪ {v n ghosts}} := by
  rw [critical_formula]
  simp only [first,second,interface_succ,Finset.union_singleton]

/-- The corresponding explicit retained ground; tail_union expands the last
term to the disjoint union of ORIGINAL r(j+1,2),r(j+1,3),r(j+1,4). -/
theorem closed_ground (n ghosts k : Nat) (hk : k < n) :
    (graph n ghosts (k+1) (by omega)).ground =
      {p n ghosts,v n ghosts,r n ghosts k hk 0} ∪ tail n ghosts (k+1) ∧
    Disjoint ({p n ghosts,v n ghosts,r n ghosts k hk 0} : Finset (Ambient n ghosts))
      (tail n ghosts (k+1)) := by
  constructor
  · rw [ground_formula]
    simp only [retained,interface_succ]
  · simpa only [interface_succ] using ground_disjoint n ghosts (k+1) (by omega)

/-- Actual root/core/cell support, transferred to the exact retained formula. -/
theorem original_support (n ghosts k : Nat) (hk : k ≤ n) :
    Supported (retained n ghosts k hk) (graph n ghosts k hk).rows.root ∧
    Supported (retained n ghosts k hk) (PhysicalHistory.certificate (history n ghosts k hk)).core ∧
    ∀ s ∈ ({first n ghosts k hk,second n ghosts k} : Finset (Finset (Ambient n ghosts))),
      s ⊆ retained n ghosts k hk := by
  have hr := (graph n ghosts k hk).rows.root_supported
  have hc := (PhysicalHistory.certificate (history n ghosts k hk)).core_supported
  have hs := (PhysicalHistory.certificate (history n ghosts k hk)).critical_supported
  rw [ground_formula] at hr hc hs
  rw [critical_formula] at hs
  exact ⟨hr,hc,hs⟩

/-- Source identity of the actual computed native endpoint: each step uses
certificate_away_from_core, since its selected retained label differs from p. -/
theorem vertex_formula (n ghosts k : Nat) (hk : k ≤ n) :
    (PhysicalHistory.certificate (history n ghosts k hk)).vertex = p n ghosts := by
  induction k with
  | zero => rfl
  | succ k ih =>
    let i := input n ghosts k (by omega)
    change (PhysicalCertificate.certificate (graph n ghosts k (by omega)) i.e i.retained
      i.a i.b i.edge i.labels i.zero i.fresh
      (PhysicalHistory.certificate (history n ghosts k (by omega)))).vertex = _
    have haway : (PhysicalHistory.certificate (history n ghosts k (by omega))).vertex ≠ i.e := by
      rw [ih (by omega)]
      exact p_ne_interface n ghosts k (by omega)
    exact (PhysicalCertificate.certificate_away_from_core
      (graph n ghosts k (by omega)) i.e i.retained i.a i.b i.edge i.labels i.zero
      i.fresh (PhysicalHistory.certificate (history n ghosts k (by omega))) haway).trans
        (ih (by omega))

/-- The two literal critical faces are distinct and each has size 2k+1. -/
theorem critical_sizes (n ghosts k : Nat) (hk : k ≤ n) :
    first n ghosts k hk ≠ second n ghosts k ∧
    (first n ghosts k hk).card = 2*k+1 ∧ (second n ghosts k).card = 2*k+1 := by
  have hne : first n ghosts k hk ≠ second n ghosts k := by
    intro h
    have hi : interface n ghosts k hk ∈ first n ghosts k hk := Finset.mem_insert_self _ _
    rw [h] at hi
    exact interface_not_second n ghosts k hk hi
  have hs := (PhysicalHistory.statistics (history n ghosts k hk)).2
  rw [critical_formula] at hs
  exact ⟨hne,hs _ (by simp),hs _ (by simp)⟩

/-- Full proper RAW boundaries, absent literal faces and antichain, in the
actual core. The empty face is included in each proper boundary. -/
theorem critical_boundaries (n ghosts k : Nat) (hk : k ≤ n)
    (s : Finset (Ambient n ghosts))
    (hs : s = first n ghosts k hk ∨ s = second n ghosts k) :
    s.Nonempty ∧ s ∉ (PhysicalHistory.certificate (history n ghosts k hk)).core ∧
    (∀ t, t ⊂ s → t ∈ (PhysicalHistory.certificate (history n ghosts k hk)).core) ∧
    delta s ⊓ (PhysicalHistory.certificate (history n ghosts k hk)).core =
      (⟨{t | t ⊂ s},by intro a b hab hbs; exact lt_of_le_of_lt hab hbs⟩ : Family (Ambient n ghosts)) ∧
    ∀ t ∈ ({first n ghosts k hk,second n ghosts k} : Finset (Finset (Ambient n ghosts))),
      s ⊆ t → s = t := by
  have hm : s ∈ (PhysicalHistory.certificate (history n ghosts k hk)).critical := by
    rw [critical_formula]; simpa only [Finset.mem_insert,Finset.mem_singleton] using hs
  have hb := PhysicalHistory.boundaries (history n ghosts k hk) hm
  refine ⟨hb.1,hb.2.1,?_,hb.2.2.1,?_⟩
  · exact (PhysicalHistory.certificate (history n ghosts k hk)).cells.boundary s hm
  · intro t ht hst
    exact hb.2.2.2 t (by rwa [critical_formula]) hst

/-- p is an actual retained tree label AND an actual vertex of the computed core. -/
theorem apex_retained (n ghosts k : Nat) (hk : k ≤ n) :
    p n ghosts ∈ (graph n ghosts k hk).ground ∧
    ({p n ghosts} : Finset (Ambient n ghosts)) ∈
      (PhysicalHistory.certificate (history n ghosts k hk)).core := by
  have hv := PhysicalHistory.survives (history n ghosts k hk)
  have hc := (PhysicalHistory.certificate (history n ghosts k hk)).vertex_mem
  rw [vertex_formula] at hv hc
  exact ⟨hv,hc⟩

/-- Counts are transferred through THIS constructed History, for every prefix,
including k=0, n=0 and ghosts=0. No unrelated existence theorem is used. -/
theorem counts (n ghosts k : Nat) (hk : k ≤ n) :
    Nat.card (Ambient n ghosts) = 3+4*n+ghosts ∧
    Nat.card (carrier n ghosts k hk) = 4+3*k ∧
    (graph n ghosts k hk).ground.card = 3+3*k ∧
    Nat.card {d : Sym2 (carrier n ghosts k hk) // d ∈ (graph n ghosts k hk).tree.edgeSet} = 3+3*k ∧
    Nat.card {d : Sym2 (carrier n ghosts k hk) // d ∈ (graph n ghosts k hk).graph.edgeSet} = 6+6*k := by
  refine ⟨?_,PhysicalHistory.vertex_card (history n ghosts k hk),
    PhysicalHistory.ground_card (history n ghosts k hk),
    PhysicalHistory.tree_edge_card (history n ghosts k hk),
    PhysicalHistory.graph_edge_card (history n ghosts k hk)⟩
  rw [Nat.card_eq_fintype_card,Fintype.card_fin]

/-- Physical chord-index correspondence, identity on inherited indices and on
the underlying right 23/34/41 indices. Other duplicate indices are preserved. -/
def chord_equiv (n ghosts k : Nat) (hk : k < n) :
    (graph n ghosts (k+1) (by omega)).chords ≃
      (graph n ghosts k (by omega)).chords ⊕ {d : Fin 4 // d ≠ 0} :=
  PhysicalCertificate.attachment_chords (graph n ghosts k (by omega))
    (input n ghosts k hk).e (input n ghosts k hk).retained
    (input n ghosts k hk).a (input n ghosts k hk).b (input n ghosts k hk).edge
    (input n ghosts k hk).labels (input n ghosts k hk).zero (input n ghosts k hk).fresh

/-- Inherited indices are literally preserved; this is not a quotient of
indices with coincident rows or physical chord endpoints. -/
theorem chord_equiv_left (n ghosts k : Nat) (hk : k < n)
    (c : (graph n ghosts k (by omega)).chords) :
    chord_equiv n ghosts k hk (.inl c) = .inl c := rfl

/-- On right physical survivors the underlying original index is unchanged. -/
theorem chord_equiv_right (n ghosts k : Nat) (hk : k < n)
    (d : (Wheel.ambientGraph (input n ghosts k hk).labels).PhysicalSurvivor (0 : Fin 4)) :
    chord_equiv n ghosts k hk (.inr d) =
      .inr ⟨d.1,fun he => d.2 (congrArg (Wheel.ambientGraph (input n ghosts k hk).labels).kappa he)⟩ := rfl

/-- EVERY actual inherited unique-path row is conditionally replaced, and
exactly the three original physical right indices are appended. -/
theorem path_rows (n ghosts k : Nat) (hk : k < n) :
    (∀ c : (graph n ghosts k (by omega)).chords,
      (graph n ghosts (k+1) (by omega)).rows.row
        ((chord_equiv n ghosts k hk).symm (.inl c)) =
      substitute (interface n ghosts k (by omega))
        {r n ghosts k hk 0,r n ghosts k hk 1} ((graph n ghosts k (by omega)).rows.row c)) ∧
    (∀ d : {d : Fin 4 // d ≠ 0},
      (graph n ghosts (k+1) (by omega)).rows.row
        ((chord_equiv n ghosts k hk).symm (.inr d)) =
      ![{r n ghosts k hk 0,r n ghosts k hk 1},
        {r n ghosts k hk 1,r n ghosts k hk 2},
        {r n ghosts k hk 2,r n ghosts k hk 3},
        {r n ghosts k hk 3,r n ghosts k hk 0}] d.1) := by
  let g := graph n ghosts k (by omega)
  let i := input n ghosts k hk
  have h := PhysicalHistory.step_rows g i
  constructor
  · intro c
    change (PhysicalHistory.step g i).data.rows.row (.inl c) = _
    rw [h.1 c]
    have hr : Wheel.R.image i.labels = {r n ghosts k hk 0,r n ghosts k hk 1} := by
      simp only [Wheel.R,Finset.image_insert,Finset.image_singleton]
      rfl
    rw [hr]
  · intro d
    let d' : (Wheel.ambientGraph i.labels).PhysicalSurvivor (0 : Fin 4) :=
      ⟨d.1,fun he => d.2 (Wheel.ambient_uniqueInterface i.labels d.1 he)⟩
    change (PhysicalHistory.step g i).data.rows.row (.inr d') = _
    rw [h.2 d']
    have hv : ∀ j : Fin 4,
        (![{(1 : Wheel.Label),2},{2,3},{3,4},{4,1}] j).image i.labels =
          ![{r n ghosts k hk 0,r n ghosts k hk 1},
            {r n ghosts k hk 1,r n ghosts k hk 2},
            {r n ghosts k hk 2,r n ghosts k hk 3},
            {r n ghosts k hk 3,r n ghosts k hk 0}] j := by
      intro j
      fin_cases j <;> simp only [Finset.image_insert,Finset.image_singleton] <;> rfl
    exact hv d.1

/-- The literal actual graph raw root is identified BEFORE nonempty projection. -/
theorem raw_root_step (n ghosts k : Nat) (hk : k < n) :
    (graph n ghosts (k+1) (by omega)).rows.root =
      parentOf ((graph n ghosts k (by omega)).ground.erase (interface n ghosts k (by omega)))
        {r n ghosts k hk 0,r n ghosts k hk 1,r n ghosts k hk 2,r n ghosts k hk 3}
        {r n ghosts k hk 2,r n ghosts k hk 3} (interface n ghosts k (by omega))
        (renameFamily (input n ghosts k hk).labels Wheel.E)
        (graph n ghosts k (by omega)).rows.root := by
  let g := graph n ghosts k (by omega)
  let i := input n ghosts k hk
  have h := PhysicalCertificate.attachment_root g i.e i.retained i.a i.b i.edge
    i.labels i.zero i.fresh
  have hz : Wheel.Z.image i.labels = {r n ghosts k hk 2,r n ghosts k hk 3} := by
    simp only [Wheel.Z,Finset.image_insert,Finset.image_singleton]; rfl
  simpa only [input_Y n ghosts k hk,hz] using h

/-- Exact existing RowHistory and its EVERY-index correspondence on this chain. -/
theorem row_handoff (n ghosts k : Nat) (hk : k ≤ n) :
    (graph n ghosts k hk).ground = (PhysicalHistory.handoff (history n ghosts k hk)).1.ground ∧
    (∀ c : (graph n ghosts k hk).chords,
      (graph n ghosts k hk).rows.row c =
        (PhysicalHistory.handoff (history n ghosts k hk)).1.row
          ((PhysicalHistory.handoff (history n ghosts k hk)).2.2.index c)) ∧
    (graph n ghosts k hk).rows.root = (PhysicalHistory.handoff (history n ghosts k hk)).1.root :=
  ⟨(PhysicalHistory.handoff (history n ghosts k hk)).2.2.ground,
    (PhysicalHistory.handoff (history n ghosts k hk)).2.2.row,
    PhysicalHistory.root_handoff (history n ghosts k hk)⟩

/-- Independent closed-chain main enumeration from the empty K4 main list,
using the real chosen Gamma and the local filling schedules of the L1 owner. -/
def mainSchedule (n ghosts : Nat) : (k : Nat) → (hk : k ≤ n) →
    List (Finset (Ambient n ghosts) × Finset (Ambient n ghosts))
  | 0, _ => []
  | k+1, hk => WheelSupplier.oneStepMainFrom (interface n ghosts k (by omega))
      (input n ghosts k (by omega)).labels {first n ghosts k (by omega),second n ghosts k}
      (mainSchedule n ghosts k (by omega))

/-- Independent separate enumeration: collars, old-core replay, terminal.
The terminal uses the proved ground and persistent p, on Cout ALONE. -/
def separateSchedule (n ghosts : Nat) : (k : Nat) → (hk : k ≤ n) →
    List (Finset (Ambient n ghosts) × Finset (Ambient n ghosts))
  | 0, _ => []
  | k+1, hk => WheelSupplier.oneStepSeparateFrom
      ((retained n ghosts k (by omega)).erase (interface n ghosts k (by omega)))
      (interface n ghosts k (by omega)) (input n ghosts k (by omega)).labels
      {first n ghosts k (by omega),second n ghosts k} (p n ghosts)
      (separateSchedule n ghosts k (by omega))

private theorem main_schedule_handoff (n ghosts k : Nat) (hk : k ≤ n) :
    rowHistoryMainSchedule (PhysicalHistory.handoff (history n ghosts k hk)).2.1 =
      mainSchedule n ghosts k hk := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change WheelSupplier.oneStepMainFrom (interface n ghosts k (by omega))
      (input n ghosts k (by omega)).labels
      (rowHistoryCriticalSchedule (PhysicalHistory.handoff (history n ghosts k (by omega))).2.1)
      (rowHistoryMainSchedule (PhysicalHistory.handoff (history n ghosts k (by omega))).2.1) = _
    rw [← (PhysicalHistory.schedule_data (history n ghosts k (by omega))).1,
      critical_formula,ih (by omega)]
    rfl

private theorem separate_schedule_handoff (n ghosts k : Nat) (hk : k ≤ n) :
    rowHistorySeparateSchedule (PhysicalHistory.handoff (history n ghosts k hk)).2.1 =
      separateSchedule n ghosts k hk := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change WheelSupplier.oneStepSeparateFrom
      ((PhysicalHistory.handoff (history n ghosts k (by omega))).1.ground.erase
        (interface n ghosts k (by omega)))
      (interface n ghosts k (by omega)) (input n ghosts k (by omega)).labels
      (rowHistoryCriticalSchedule (PhysicalHistory.handoff (history n ghosts k (by omega))).2.1)
      (rowHistoryVertexSchedule (PhysicalHistory.handoff (history n ghosts k (by omega))).2.1)
      (rowHistorySeparateSchedule (PhysicalHistory.handoff (history n ghosts k (by omega))).2.1) = _
    rw [← (PhysicalHistory.handoff (history n ghosts k (by omega))).2.2.ground,
      ground_formula,← (PhysicalHistory.schedule_data (history n ghosts k (by omega))).1,
      critical_formula,← (PhysicalHistory.schedule_data (history n ghosts k (by omega))).2,
      vertex_formula,ih (by omega)]
    rfl

private theorem endpoint_formula (n ghosts k : Nat) (hk : k ≤ n) :
    endpoint (PhysicalHistory.certificate (history n ghosts k hk)).core
      (PhysicalHistory.certificate (history n ghosts k hk)).critical =
      (PhysicalHistory.certificate (history n ghosts k hk)).core ⊔
        delta (first n ghosts k hk) ⊔ delta (second n ghosts k) := by
  rw [critical_formula]
  apply SetLike.ext
  intro s
  change (s ∈ (PhysicalHistory.certificate (history n ghosts k hk)).core ∨
    ∃ a ∈ ({first n ghosts k hk,second n ghosts k} : Finset (Finset (Ambient n ghosts))), s ⊆ a) ↔ _
  simp only [Finset.mem_insert,Finset.mem_singleton,LowerSet.mem_sup_iff,delta,LowerSet.mem_mk]
  aesop

/-- ACTUAL native main list, with only an equality cast to its proved literal
two-simplex endpoint. The raw attachment is unchanged. -/
def main (n ghosts k : Nat) (hk : k ≤ n) :
    Sequence (project (graph n ghosts k hk).rows.root)
      (project ((PhysicalHistory.certificate (history n ghosts k hk)).core ⊔
        delta (first n ghosts k hk) ⊔ delta (second n ghosts k))) :=
  (PhysicalHistory.certificate (history n ghosts k hk)).main.cast rfl
    (congrArg project (endpoint_formula n ghosts k hk))

/-- ACTUAL native separate list, whose source is the core alone. -/
def separate (n ghosts k : Nat) (hk : k ≤ n) :
    Sequence (project (PhysicalHistory.certificate (history n ghosts k hk)).core)
      (project (delta {p n ghosts})) :=
  (PhysicalHistory.certificate (history n ghosts k hk)).separate.cast rfl
    (by rw [vertex_formula])

/-- Exact independent list equations, via G3 main_order/separate_order and
the explicit closed-chain data recursions, with equality casts preserving order. -/
theorem list_equations (n ghosts k : Nat) (hk : k ≤ n) :
    orderedPairs (main n ghosts k hk) = mainSchedule n ghosts k hk ∧
    orderedPairs (separate n ghosts k hk) = separateSchedule n ghosts k hk := by
  constructor
  · rw [main,orderedPairs_cast]
    exact (PhysicalHistory.main_order (history n ghosts k hk)).trans
      (main_schedule_handoff n ghosts k hk)
  · rw [separate,orderedPairs_cast]
    exact (PhysicalHistory.separate_order (history n ghosts k hk)).trans
      (separate_schedule_handoff n ghosts k hk)

/-- The two lists are real ordinary collapses in their evolving ambients,
and every emitted pair retains its literal full final endpoint. -/
theorem current_pairs (n ghosts k : Nat) (hk : k ≤ n) :
    (∀ P ∈ (main n ghosts k hk).pairs, P.lower.Nonempty ∧
      (∀ s ∈ P.ambient, P.lower ⊆ s → s = P.lower ∨ s = P.upper) ∧
      project ((PhysicalHistory.certificate (history n ghosts k hk)).core ⊔
        delta (first n ghosts k hk) ⊔ delta (second n ghosts k)) ≤ P.retained) ∧
    (∀ P ∈ (separate n ghosts k hk).pairs, P.lower.Nonempty ∧
      (∀ s ∈ P.ambient, P.lower ⊆ s → s = P.lower ∨ s = P.upper) ∧
      project (delta {p n ghosts}) ≤ P.retained) := by
  have hc (P : CollapsePair (Ambient n ghosts)) :
      ∀ s ∈ P.ambient, P.lower ⊆ s → s = P.lower ∨ s = P.upper := by
    intro s hs hsub
    by_cases he : s = P.lower
    · exact Or.inl he
    · exact Or.inr (P.free s hs (Finset.ssubset_iff_subset_ne.mpr ⟨hsub,Ne.symm he⟩))
  exact ⟨fun P hP => ⟨P.lower_nonempty,hc P,(main n ghosts k hk).final_le_each_retained hP⟩,
    fun P hP => ⟨P.lower_nonempty,hc P,(separate n ghosts k hk).final_le_each_retained hP⟩⟩

/-- Original-label coordinate fixedness and actual inclusion/retraction
equations for BOTH constructed sequences. Coordinates include deleted labels
and ghosts, and the separate domain is always the core alone. -/
theorem native_geometry (n ghosts k : Nat) (hk : k ≤ n) :
    (∀ (t : unitInterval) (x : Space (project (graph n ghosts k hk).rows.root)),
      x.val ∈ realization (project ((PhysicalHistory.certificate (history n ghosts k hk)).core ⊔
        delta (first n ghosts k hk) ⊔ delta (second n ghosts k))) →
      ∀ a : Ambient n ghosts, ((main n ghosts k hk).collapseHomotopy (t,x)).val a = x.val a) ∧
    (∀ (t : unitInterval) (x : Space (project (PhysicalHistory.certificate (history n ghosts k hk)).core)),
      x.val ∈ realization (project (delta {p n ghosts})) →
      ∀ a : Ambient n ghosts, ((separate n ghosts k hk).collapseHomotopy (t,x)).val a = x.val a) ∧
    (∀ y : Space (project ((PhysicalHistory.certificate (history n ghosts k hk)).core ⊔
        delta (first n ghosts k hk) ⊔ delta (second n ghosts k))),
      (main n ghosts k hk).sequenceRetraction ((main n ghosts k hk).inclusion y) = y) ∧
    (∀ z : Space (project (delta {p n ghosts})),
      (separate n ghosts k hk).sequenceRetraction ((separate n ghosts k hk).inclusion z) = z) := by
  refine ⟨?_,?_,?_,?_⟩
  · intro t x hx a
    exact congrArg (fun y : Space (project (graph n ghosts k hk).rows.root) => y.val a)
      ((main n ghosts k hk).collapseHomotopy_fixed t x hx)
  · intro t x hx a
    exact congrArg (fun y : Space (project (PhysicalHistory.certificate (history n ghosts k hk)).core) => y.val a)
      ((separate n ghosts k hk).collapseHomotopy_fixed t x hx)
  · exact fun y => (main n ghosts k hk).sequenceRetraction_inclusion y
  · exact fun z => (separate n ghosts k hk).sequenceRetraction_inclusion z

end D5.S3.Geometry.OriginalLabelTwoSum.PhysicalClosedChain
