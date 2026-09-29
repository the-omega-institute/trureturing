/- GID: D5/S3/Quantum/Algebra/DegeneracyGraphDeterminant
   generality: G
   mirror-B: D5/B/S3/Quantum/Algebra/DegeneracyGraphDeterminant
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Literal degeneracy-graph columns support the fiber-Newton pruning recurrence. -/

import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Vandermonde
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fintype.Sort
import Mathlib.Algebra.Polynomial.BigOperators

set_option autoImplicit false

noncomputable section

open scoped BigOperators

namespace D5.S3.Quantum.Algebra.DegeneracyGraphDeterminant

/-- A finite ordered layered tree, including the virtual root at level zero.
The ancestor maps are the coherent iterates of the adjacent parent maps. -/
structure SourceTree (L : ℕ) where
  V : Fin (L + 1) → Type
  fintypeV : ∀ i, Fintype (V i)
  linearOrderV : ∀ i, LinearOrder (V i)
  rootSubsingleton : Subsingleton (V 0)
  rootNonempty : Nonempty (V 0)
  ancestor : ∀ {i j : Fin (L + 1)}, i ≤ j → V j → V i
  ancestor_self : ∀ (i) (v : V i), ancestor (le_refl i) v = v
  ancestor_trans : ∀ {i j k} (hij : i ≤ j) (hjk : j ≤ k) (v : V k),
    ancestor hij (ancestor hjk v) = ancestor (hij.trans hjk) v
  ancestor_surjective : ∀ {i j} (hij : i ≤ j), Function.Surjective (ancestor hij)
  label : (i : Fin L) → V i.succ → ℂ
  sibling_injective : ∀ (i : Fin L) (u v : V i.succ),
    ancestor Fin.castSucc_lt_succ.le u = ancestor Fin.castSucc_lt_succ.le v →
    label i u = label i v → u = v

attribute [instance] SourceTree.fintypeV SourceTree.linearOrderV SourceTree.rootSubsingleton
  SourceTree.rootNonempty

/-- The adjacent parent map. -/
def SourceTree.parent {L : ℕ} (T : SourceTree L) (i : Fin L) :
    T.V i.succ → T.V i.castSucc :=
  T.ancestor Fin.castSucc_lt_succ.le

/-- The source positive-composition view (`p₁,c₂,...`): at every adjacent
level it records the actual ordered parent-fiber sizes. -/
def sourcePositiveComposition {L : ℕ} (T : SourceTree L) (i : Fin L)
    (p : T.V i.castSucc) : ℕ :=
  Fintype.card {w : T.V i.succ // T.parent i w = p}

/-- Recursive source survival: a vertex at level `i` survives when it has at least
`threshold i` distinct surviving children.  Bottom vertices survive unconditionally. -/
inductive Survives {L : ℕ} (T : SourceTree L) (threshold : Fin L → ℕ) :
    (i : Fin (L + 1)) → T.V i → Prop
  | bottom (v : T.V (Fin.last L)) : Survives T threshold (Fin.last L) v
  | step (i : Fin L) (v : T.V i.castSucc) (children : Finset (T.V i.succ))
      (hparent : ∀ w ∈ children, T.parent i w = v)
      (hcard : threshold i ≤ children.card)
      (hchildren : ∀ w ∈ children, Survives T threshold i.succ w) :
      Survives T threshold i.castSucc v

/-- The literal finite source survival set at a level. -/
def survivalSet {L : ℕ} (T : SourceTree L) (threshold : Fin L → ℕ)
    (i : Fin (L + 1)) : Finset (T.V i) := by
  classical
  exact Finset.univ.filter (Survives T threshold i)

noncomputable def survivingChildren {L : ℕ} (T : SourceTree L)
    (threshold : Fin L → ℕ) (i : Fin L) (v : T.V i.castSucc) :
    Finset (T.V i.succ) := by
  classical
  exact Finset.univ.filter fun w =>
    T.parent i w = v ∧ Survives T threshold i.succ w

theorem survives_step_iff {L : ℕ} (T : SourceTree L) (threshold : Fin L → ℕ)
    (i : Fin L) (v : T.V i.castSucc) :
    Survives T threshold i.castSucc v ↔
      threshold i ≤ (survivingChildren T threshold i v).card := by
  classical
  constructor
  · intro h
    refine Survives.rec (motive := fun j w _ =>
      ∀ (k : Fin L) (hjk : j = k.castSucc),
        threshold k ≤ (survivingChildren T threshold k (hjk ▸ w)).card)
      ?_ ?_ h i rfl
    · intro w k hk
      have hval := congrArg Fin.val hk
      simp only [Fin.val_last, Fin.val_castSucc] at hval
      omega
    · intro j w children hparent hcard hchildren ih k hjk
      have hjk' : j = k := by
        apply Fin.ext
        exact congrArg (fun x : Fin (L + 1) => x.val) hjk
      subst k
      have hjk : hjk = rfl := Subsingleton.elim _ _
      subst hjk
      exact hcard.trans (Finset.card_le_card (by
        intro x hx
        simpa [survivingChildren] using And.intro (hparent x hx) (hchildren x hx)))
  · intro h
    let children := survivingChildren T threshold i v
    exact Survives.step i v children
      (by
        intro w hw
        exact (show T.parent i w = v ∧ Survives T threshold i.succ w from by
          simpa [children, survivingChildren] using hw).1)
      h
      (by
        intro w hw
        exact (show T.parent i w = v ∧ Survives T threshold i.succ w from by
          simpa [children, survivingChildren] using hw).2)

/-- The finite source exponent box. -/
def Exponents {L : ℕ} (T : SourceTree L) :=
  ∀ i : Fin L, Fin (Fintype.card (T.V i.succ))

def sourceThreshold {L : ℕ} (T : SourceTree L) (m : Exponents T) : Fin L → ℕ :=
  fun i => (m i).val + 1

/-- The source set `S^[1]_[m₂+1,...,m_L+1]`. -/
def sourceS {n : ℕ} (T : SourceTree (n + 1)) (m : Exponents T) :
    Finset (T.V ⟨1, by omega⟩) :=
  survivalSet T (sourceThreshold T m) (Fin.succ 0)

/-- Literal source columns: exponent vectors satisfying the source bound on the first exponent. -/
def Columns {n : ℕ} (T : SourceTree (n + 1)) :=
  {m : Exponents T // (m 0).val < (sourceS T m).card}

/-- Evaluation along the actual ancestor path from a bottom vertex. -/
def RawM {n : ℕ} (T : SourceTree (n + 1)) :
    Matrix (T.V (Fin.last (n + 1))) (Columns T) ℂ :=
  fun b m => ∏ i : Fin (n + 1),
    T.label i (T.ancestor (Fin.le_last i.succ) b) ^ (m.1 i).val

abbrev Bottom {n : ℕ} (T : SourceTree (n + 1)) :=
  T.V (Fin.last (n + 1))

abbrev Penultimate {n : ℕ} (T : SourceTree (n + 1)) :=
  T.V (Fin.last n).castSucc

/-- The actual bottom siblings over a penultimate vertex. -/
abbrev bottomFiber {n : ℕ} (T : SourceTree (n + 1)) (p : Penultimate T) :=
  {b : Bottom T // T.parent (Fin.last n) b = p}

/-- Penultimate vertices whose bottom fiber contains the Newton degree `r`. -/
abbrev occupiedPenultimate {n : ℕ} (T : SourceTree (n + 1)) (r : ℕ) :=
  {p : Penultimate T // r < Fintype.card (bottomFiber T p)}

/-- Vertices retained at a level by the occupied penultimate vertices. -/
def retainedVertex {n : ℕ} (T : SourceTree (n + 1)) (r : ℕ)
    (i : Fin (n + 1)) :=
  {v : T.V i.castSucc // ∃ p : occupiedPenultimate T r,
    T.ancestor (show i.castSucc ≤ (Fin.last n).castSucc from Fin.le_last i) p.1 = v}

noncomputable instance {n : ℕ} (T : SourceTree (n + 1)) (r : ℕ)
    (i : Fin (n + 1)) : Fintype (retainedVertex T r i) := by
  letI : Finite (retainedVertex T r i) :=
    Finite.of_injective Subtype.val Subtype.val_injective
  exact Fintype.ofFinite _

def reachesOccupied {n : ℕ} (T : SourceTree (n + 1)) (r : ℕ)
    (i : Fin (n + 2)) (v : T.V i) : Prop :=
  i = Fin.last (n + 1) ∨ ∃ h : i ≤ (Fin.last n).castSucc,
    ∃ p : occupiedPenultimate T r, T.ancestor h p.1 = v

theorem survives_reachesOccupied {n : ℕ} (T : SourceTree (n + 1))
    (threshold : Fin (n + 1) → ℕ) (r : ℕ)
    (hpositive : ∀ i, 0 < threshold i)
    (hlast : threshold (Fin.last n) = r + 1)
    {i : Fin (n + 2)} {v : T.V i} (h : Survives T threshold i v) :
    reachesOccupied T r i v := by
  classical
  induction h with
  | bottom w => exact Or.inl rfl
  | step j w children hparent hcard hchildren ih =>
      right
      by_cases hj : j = Fin.last n
      · subst j
        let f : children → bottomFiber T w := fun c => ⟨c.1, hparent c.1 c.2⟩
        have hf : Function.Injective f := by
          intro a b hab
          have hab' : (f a).val = (f b).val :=
            congrArg (fun z : bottomFiber T w => z.val) hab
          exact Subtype.ext hab'
        have hchildrenCard : children.card ≤ Fintype.card (bottomFiber T w) := by
          rw [← Fintype.card_coe]
          exact Fintype.card_le_of_injective f hf
        have hoccupied : r < Fintype.card (bottomFiber T w) := by
          rw [hlast] at hcard
          omega
        refine ⟨le_rfl, ⟨w, hoccupied⟩, ?_⟩
        exact T.ancestor_self _ w
      · have hchildrenPos : 0 < children.card := (hpositive j).trans_le hcard
        obtain ⟨c, hc⟩ := Finset.card_pos.mp hchildrenPos
        rcases ih c hc with hbottom | ⟨hbelow, p, hp⟩
        · have hval := congrArg Fin.val hbottom
          simp only [Fin.val_succ, Fin.val_last] at hval
          have hjval : j.val = n := by omega
          have : j = Fin.last n := Fin.ext hjval
          exact (hj this).elim
        · have hedge : j.castSucc ≤ j.succ := Fin.castSucc_lt_succ.le
          have hout : j.castSucc ≤ (Fin.last n).castSucc := hedge.trans hbelow
          refine ⟨hout, p, ?_⟩
          calc
            T.ancestor hout p.1 = T.ancestor hedge (T.ancestor hbelow p.1) :=
              (T.ancestor_trans hedge hbelow p.1).symm
            _ = T.parent j c := by rw [hp]; rfl
            _ = w := hparent c hc

theorem survives_descendant {L : ℕ} (T : SourceTree L)
    (threshold : Fin L → ℕ) (hpositive : ∀ i, 0 < threshold i)
    {i j : Fin (L + 1)} (hij : i ≤ j) {v : T.V i}
    (hv : Survives T threshold i v) :
    ∃ w : T.V j, T.ancestor hij w = v ∧ Survives T threshold j w := by
  have aux : ∀ d : ℕ, ∀ (i j : Fin (L + 1)),
      j.val = i.val + d → ∀ (hij : i ≤ j) (v : T.V i),
        Survives T threshold i v →
          ∃ w : T.V j, T.ancestor hij w = v ∧ Survives T threshold j w := by
    intro d
    induction d with
    | zero =>
        intro i j hval hij v hv
        have hij' : i = j := Fin.ext (by omega)
        subst j
        exact ⟨v, T.ancestor_self _ v, hv⟩
    | succ d ih =>
        intro i j hval hij v hv
        have hiL : i.val < L := by omega
        let q : Fin L := ⟨i.val, hiL⟩
        have hq : Survives T threshold q.castSucc v := by
          simpa [q] using hv
        have hcard := (survives_step_iff T threshold q v).mp hq
        have hnonempty :
            (survivingChildren T threshold q v).Nonempty :=
          Finset.card_pos.mp ((hpositive q).trans_le hcard)
        obtain ⟨w, hw⟩ := hnonempty
        have hw' : T.parent q w = v ∧ Survives T threshold q.succ w := by
          simpa [survivingChildren] using hw
        let k : Fin (L + 1) := ⟨i.val + 1, by omega⟩
        have hik : i ≤ k := by
          change i.val ≤ i.val + 1
          omega
        have hkj : k ≤ j := by
          change i.val + 1 ≤ j.val
          omega
        obtain ⟨z, hzanc, hzsurv⟩ := ih k j (by simp [k]; omega) hkj w hw'.2
        refine ⟨z, ?_, hzsurv⟩
        calc
          T.ancestor hij z = T.ancestor hik (T.ancestor hkj z) :=
            (T.ancestor_trans hik hkj z).symm
          _ = T.ancestor hik w := by rw [hzanc]
          _ = v := by
            change T.parent q w = v
            exact hw'.1
  obtain ⟨w, hw, hwsurv⟩ := aux (j.val - i.val) i j (by omega) hij v hv
  exact ⟨w, hw, hwsurv⟩

/-- Append the occupied bottom threshold to the thresholds on a pruned tree. -/
def appendThreshold {n : ℕ} (threshold : Fin n → ℕ) (r : ℕ) :
    Fin (n + 1) → ℕ :=
  Fin.lastCases (r + 1) threshold

private theorem retained_penultimate_survives {n : ℕ} (T : SourceTree (n + 1))
    (threshold : Fin n → ℕ) (r : ℕ) (v : retainedVertex T r (Fin.last n)) :
    Survives T (appendThreshold threshold r) (Fin.last n).castSucc v.1 := by
  classical
  rw [survives_step_iff]
  simp only [appendThreshold, Fin.lastCases_last]
  obtain ⟨p, hp⟩ := v.2
  have hpv : p.1 = v.1 := by
    simpa only [T.ancestor_self] using hp
  have hvoccupied : r < Fintype.card (bottomFiber T v.1) := by
    rw [← hpv]
    exact p.2
  have hchildren :
      (survivingChildren T (appendThreshold threshold r) (Fin.last n) v.1).card =
        Fintype.card (bottomFiber T v.1) := by
    rw [Fintype.card_subtype]
    apply congrArg Finset.card
    ext b
    simp only [survivingChildren, bottomFiber, Finset.mem_filter, Finset.mem_univ,
      true_and, and_iff_left_iff_imp]
    intro _
    exact Survives.bottom b
  rw [hchildren]
  omega

/-- The source pruning `T_r`: retain exactly the ancestors of penultimate vertices
with at least `r+1` bottom children, and then drop the bottom level. -/
def prune {n : ℕ} (T : SourceTree (n + 1)) (r : ℕ)
    (hoccupied : Nonempty (occupiedPenultimate T r)) : SourceTree n := by
  classical
  let anc : ∀ {i j : Fin (n + 1)}, i ≤ j →
      retainedVertex T r j → retainedVertex T r i :=
    fun {i j} hij v => by
      refine ⟨T.ancestor (show i.castSucc ≤ j.castSucc from hij) v.1, ?_⟩
      obtain ⟨p, hp⟩ := v.2
      refine ⟨p, ?_⟩
      rw [← hp]
      exact (T.ancestor_trans _ _ p.1).symm
  refine
    { V := retainedVertex T r
      fintypeV := fun _ => inferInstance
      linearOrderV := fun i => by
        dsimp [retainedVertex]
        infer_instance
      rootSubsingleton := by
        dsimp [retainedVertex]
        infer_instance
      rootNonempty := ?_
      ancestor := anc
      ancestor_self := ?_
      ancestor_trans := ?_
      ancestor_surjective := ?_
      label := fun i v => T.label i.castSucc v.1
      sibling_injective := ?_ }
  · obtain ⟨p⟩ := hoccupied
    exact ⟨⟨T.ancestor (show (0 : Fin (n + 1)).castSucc ≤
      (Fin.last n).castSucc from Fin.le_last 0) p.1, ⟨p, rfl⟩⟩⟩
  · intro i v
    apply Subtype.ext
    exact T.ancestor_self i.castSucc v.1
  · intro i j k hij hjk v
    apply Subtype.ext
    exact T.ancestor_trans (show i.castSucc ≤ j.castSucc from hij)
      (show j.castSucc ≤ k.castSucc from hjk) v.1
  · intro i j hij v
    obtain ⟨p, hp⟩ := v.2
    let w : retainedVertex T r j :=
      ⟨T.ancestor (show j.castSucc ≤ (Fin.last n).castSucc from Fin.le_last j) p.1,
        ⟨p, rfl⟩⟩
    refine ⟨w, ?_⟩
    apply Subtype.ext
    change T.ancestor (show i.castSucc ≤ j.castSucc from hij)
      (T.ancestor (show j.castSucc ≤ (Fin.last n).castSucc from Fin.le_last j) p.1) = v.1
    rw [T.ancestor_trans]
    exact hp
  · intro i u v hparent hlabel
    apply Subtype.ext
    apply T.sibling_injective i.castSucc u.1 v.1
    · exact congrArg Subtype.val hparent
    · exact hlabel

theorem prune_survives_iff {n : ℕ} (T : SourceTree (n + 1))
    (threshold : Fin n → ℕ) (r : ℕ)
    (hoccupied : Nonempty (occupiedPenultimate T r))
    (hpositive : ∀ i, 0 < threshold i)
    (i : Fin (n + 1)) (v : (prune T r hoccupied).V i) :
    Survives (prune T r hoccupied) threshold i v ↔
      Survives T (appendThreshold threshold r) i.castSucc v.1 := by
  classical
  induction i using Fin.reverseInduction with
  | last =>
      constructor
      · intro _
        exact retained_penultimate_survives T threshold r v
      · intro _
        exact Survives.bottom v
  | cast i ih =>
      let leftChildren := survivingChildren (prune T r hoccupied) threshold i v
      let rightChildren := survivingChildren T (appendThreshold threshold r) i.castSucc v.1
      let toRight : leftChildren → rightChildren := fun w => by
        dsimp only [leftChildren, rightChildren] at w ⊢
        have hw : (prune T r hoccupied).parent i w.1 = v ∧
            Survives (prune T r hoccupied) threshold i.succ w.1 := by
          simpa [survivingChildren] using w.2
        refine ⟨w.1.1, ?_⟩
        simp only [survivingChildren, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨?_, (ih w.1).mp hw.2⟩
        exact congrArg Subtype.val hw.1
      let toLeft : rightChildren → leftChildren := fun w => by
        dsimp only [leftChildren, rightChildren] at w ⊢
        have hw : T.parent i.castSucc w.1 = v.1 ∧
            Survives T (appendThreshold threshold r) i.succ.castSucc w.1 := by
          simpa [survivingChildren] using w.2
        have hwretained :
            ∃ p : occupiedPenultimate T r,
              T.ancestor (show i.succ.castSucc ≤ (Fin.last n).castSucc from
                Fin.le_last i.succ) p.1 = w.1 := by
          rcases survives_reachesOccupied T (appendThreshold threshold r) r
              (by
                intro k
                refine Fin.lastCases (by simp [appendThreshold])
                  (fun j => by simpa [appendThreshold] using hpositive j) k)
              (by simp [appendThreshold]) hw.2 with hbottom | ⟨_, p, hp⟩
          · have hval := congrArg Fin.val hbottom
            simp only [Fin.val_castSucc, Fin.val_last] at hval
            omega
          · exact ⟨p, hp⟩
        let w' : (prune T r hoccupied).V i.succ := ⟨w.1, hwretained⟩
        refine ⟨w', ?_⟩
        simp only [survivingChildren, Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨?_, (ih w').mpr hw.2⟩
        apply Subtype.ext
        exact hw.1
      let childEquiv : leftChildren ≃ rightChildren :=
        { toFun := toRight
          invFun := toLeft
          left_inv := by
            intro w
            apply Subtype.ext
            apply Subtype.ext
            dsimp [toLeft, toRight]
          right_inv := by
            intro w
            apply Subtype.ext
            dsimp [toLeft, toRight] }
      have hcard :
          (survivingChildren (prune T r hoccupied) threshold i v).card =
            (survivingChildren T (appendThreshold threshold r) i.castSucc v.1).card := by
        simpa only [Fintype.card_coe] using Fintype.card_congr childEquiv
      rw [survives_step_iff, survives_step_iff]
      simp only [appendThreshold, Fin.lastCases_castSucc]
      rw [hcard]

private theorem column_survival_card_bound {n : ℕ} (T : SourceTree (n + 1))
    (m : Columns T) (i : Fin (n + 1)) :
    (m.1 i).val < (survivalSet T (sourceThreshold T m.1) i.succ).card := by
  classical
  refine Fin.cases m.2 (fun i => ?_) i
  · have hnonempty : (sourceS T m.1).Nonempty := by
      apply Finset.card_pos.mp
      exact (Nat.zero_le (m.1 0).val).trans_lt m.2
    obtain ⟨root, hrootMem⟩ := hnonempty
    have hroot : Survives T (sourceThreshold T m.1) (Fin.succ 0) root := by
      change root ∈ survivalSet T (sourceThreshold T m.1) (Fin.succ 0) at hrootMem
      simp only [survivalSet] at hrootMem
      exact ((@Finset.mem_filter _ (Survives T (sourceThreshold T m.1) (Fin.succ 0))
        (Classical.decPred _) _ _).mp hrootMem).2
    obtain ⟨v, _, hv⟩ := survives_descendant T (sourceThreshold T m.1)
      (fun j => by simp [sourceThreshold]) (j := i.castSucc.succ)
      (by change 1 ≤ i.val + 1; omega) hroot
    have hcard := (survives_step_iff T (sourceThreshold T m.1) i.succ v).mp hv
    have hsubset :
        survivingChildren T (sourceThreshold T m.1) i.succ v ⊆
          survivalSet T (sourceThreshold T m.1) i.succ.succ := by
      intro w hw
      have hw' : T.parent i.succ w = v ∧
          Survives T (sourceThreshold T m.1) i.succ.succ w := by
        simpa [survivingChildren] using hw
      simpa [survivalSet] using hw'.2
    have hle := Finset.card_le_card hsubset
    simp only [sourceThreshold] at hcard
    omega

private theorem column_retained_bound {n : ℕ} (T : SourceTree (n + 1))
    (m : Columns T) (r : ℕ) (hlast : (m.1 (Fin.last n)).val = r)
    (hoccupied : Nonempty (occupiedPenultimate T r))
    (i : Fin n) :
    (m.1 i.castSucc).val < Fintype.card ((prune T r hoccupied).V i.succ) := by
  classical
  let surviving := survivalSet T (sourceThreshold T m.1) i.castSucc.succ
  let toRetained : surviving → (prune T r hoccupied).V i.succ := fun v => by
    refine ⟨v.1, ?_⟩
    have hv : Survives T (sourceThreshold T m.1) i.castSucc.succ v.1 := by
      simpa [surviving, survivalSet] using v.2
    rcases survives_reachesOccupied T (sourceThreshold T m.1) r
        (fun j => by simp [sourceThreshold]) (by simp [sourceThreshold, hlast]) hv with
      hbottom | ⟨_, p, hp⟩
    · have hval := congrArg Fin.val hbottom
      change i.val + 1 = n + 1 at hval
      have hi := i.isLt
      omega
    · exact ⟨p, hp⟩
  have hinjective : Function.Injective toRetained := by
    intro a b hab
    apply Subtype.ext
    exact congrArg (fun z : (prune T r hoccupied).V i.succ => z.1) hab
  have hcard : surviving.card ≤ Fintype.card ((prune T r hoccupied).V i.succ) := by
    rw [← Fintype.card_coe]
    exact Fintype.card_le_of_injective toRetained hinjective
  exact (column_survival_card_bound T m i.castSucc).trans_le hcard

/-- Append the literal last exponent `r` to an exponent vector on `T_r`. -/
noncomputable def liftExponents {n : ℕ} (T : SourceTree (n + 1)) (r : ℕ)
    (hoccupied : Nonempty (occupiedPenultimate T r))
    (m : Exponents (prune T r hoccupied)) : Exponents T :=
  Fin.lastCases ⟨r, by
    obtain ⟨p⟩ := hoccupied
    exact p.2.trans_le (Fintype.card_subtype_le _)⟩ fun i =>
    ⟨(m i).val, (m i).isLt.trans_le (Fintype.card_le_of_injective
      (fun v : (prune T r hoccupied).V i.succ => v.1)
      (fun _ _ h => Subtype.ext h))⟩

/-- Restrict a literal source column with last exponent `r` to the retained levels. -/
noncomputable def restrictExponents {n : ℕ} (T : SourceTree (n + 1))
    (m : Columns T) (r : ℕ) (hlast : (m.1 (Fin.last n)).val = r)
    (hoccupied : Nonempty (occupiedPenultimate T r)) :
    Exponents (prune T r hoccupied) :=
  fun i => ⟨(m.1 i.castSucc).val, column_retained_bound T m r hlast hoccupied i⟩


private theorem sourceS_lift_card {n : ℕ} (T : SourceTree (n + 2))
    (r : ℕ) (hoccupied : Nonempty (occupiedPenultimate T r))
    (m : Exponents (prune T r hoccupied)) :
    (sourceS T (liftExponents T r hoccupied m)).card =
      (sourceS (prune T r hoccupied) m).card := by
  classical
  let one : Fin (n + 2) := Fin.succ 0
  let left := sourceS (prune T r hoccupied) m
  let right := sourceS T (liftExponents T r hoccupied m)
  have hthreshold : sourceThreshold T (liftExponents T r hoccupied m) =
      appendThreshold (sourceThreshold (prune T r hoccupied) m) r := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simp [sourceThreshold, liftExponents, appendThreshold]
    · simp [sourceThreshold, liftExponents, appendThreshold]
  let toRight : left → right := fun v => by
    dsimp only [left, right] at v ⊢
    have hv : Survives (prune T r hoccupied)
        (sourceThreshold (prune T r hoccupied) m) one v.1 := by
      have hvMem := v.2
      change v.1 ∈ survivalSet (prune T r hoccupied)
        (sourceThreshold (prune T r hoccupied) m) one at hvMem
      simp only [survivalSet] at hvMem
      exact ((@Finset.mem_filter _ (Survives (prune T r hoccupied)
        (sourceThreshold (prune T r hoccupied) m) one)
        (Classical.decPred _) _ _).mp hvMem).2
    have hv' := (prune_survives_iff T (sourceThreshold (prune T r hoccupied) m)
      r hoccupied (fun i => by simp [sourceThreshold]) one v.1).mp hv
    refine ⟨v.1.1, ?_⟩
    simp only [sourceS, survivalSet]
    apply (@Finset.mem_filter _ (Survives T
      (sourceThreshold T (liftExponents T r hoccupied m)) (Fin.succ 0))
      (Classical.decPred _) _ _).mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [hthreshold]
    exact hv'
  let toLeft : right → left := fun v => by
    dsimp only [left, right] at v ⊢
    have hv : Survives T (sourceThreshold T (liftExponents T r hoccupied m))
        one.castSucc v.1 := by
      have hvMem := v.2
      change v.1 ∈ survivalSet T
        (sourceThreshold T (liftExponents T r hoccupied m)) one.castSucc at hvMem
      simp only [survivalSet] at hvMem
      exact ((@Finset.mem_filter _ (Survives T
        (sourceThreshold T (liftExponents T r hoccupied m)) one.castSucc)
        (Classical.decPred _) _ _).mp hvMem).2
    have hvAppend : Survives T
        (appendThreshold (sourceThreshold (prune T r hoccupied) m) r)
        one.castSucc v.1 := by
      rw [← hthreshold]
      exact hv
    have hvretained :
        ∃ p : occupiedPenultimate T r,
          T.ancestor (show one.castSucc ≤ (Fin.last (n + 1)).castSucc from
            Fin.le_last one) p.1 = v.1 := by
      rcases survives_reachesOccupied T
          (appendThreshold (sourceThreshold (prune T r hoccupied) m) r) r
          (by
            intro k
            refine Fin.lastCases (by simp [appendThreshold])
              (fun j => by simp [appendThreshold, sourceThreshold]) k)
          (by simp [appendThreshold]) hvAppend with hbottom | ⟨_, p, hp⟩
      · have hval := congrArg Fin.val hbottom
        simp only [Fin.val_castSucc, Fin.val_last] at hval
        omega
      · exact ⟨p, hp⟩
    let v' : (prune T r hoccupied).V one := ⟨v.1, hvretained⟩
    refine ⟨v', ?_⟩
    simp only [sourceS, survivalSet]
    apply (@Finset.mem_filter _ (Survives (prune T r hoccupied)
      (sourceThreshold (prune T r hoccupied) m) (Fin.succ 0))
      (Classical.decPred _) _ _).mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    exact (prune_survives_iff T (sourceThreshold (prune T r hoccupied) m)
      r hoccupied (fun i => by simp [sourceThreshold]) one v').mpr hvAppend
  let e : left ≃ right :=
    { toFun := toRight
      invFun := toLeft
      left_inv := by
        intro v
        apply Subtype.ext
        apply Subtype.ext
        dsimp [toLeft, toRight]
      right_inv := by
        intro v
        apply Subtype.ext
        dsimp [toLeft, toRight] }
  simpa only [Fintype.card_coe] using (Fintype.card_congr e).symm

noncomputable def liftColumn {n : ℕ} (T : SourceTree (n + 2))
    (r : ℕ) (hoccupied : Nonempty (occupiedPenultimate T r))
    (m : Columns (prune T r hoccupied)) : Columns T :=
  ⟨liftExponents T r hoccupied m.1, by
    rw [sourceS_lift_card T r hoccupied m.1]
    change (liftExponents T r hoccupied m.1 (0 : Fin (n + 1)).castSucc).val < _
    simpa only [liftExponents, Fin.lastCases_castSucc] using m.2⟩

noncomputable def restrictColumn {n : ℕ} (T : SourceTree (n + 2))
    (r : ℕ) (hoccupied : Nonempty (occupiedPenultimate T r))
    (m : Columns T) (hlast : (m.1 (Fin.last (n + 1))).val = r) :
    Columns (prune T r hoccupied) :=
  ⟨restrictExponents T m r hlast hoccupied, by
    change (m.1 0).val <
      (sourceS (prune T r hoccupied) (restrictExponents T m r hlast hoccupied)).card
    rw [← sourceS_lift_card T r hoccupied]
    have hlift : liftExponents T r hoccupied
        (restrictExponents T m r hlast hoccupied) = m.1 := by
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · apply Fin.ext
        simpa [liftExponents] using hlast.symm
      · apply Fin.ext
        simp [liftExponents, restrictExponents]
    rw [hlift]
    exact m.2⟩

/-- The literal source columns with last exponent `r` are exactly the literal
columns of the occupied pruning `T_r`. -/
noncomputable def lastExponentSliceEquiv {n : ℕ} (T : SourceTree (n + 2))
    (r : ℕ) (hoccupied : Nonempty (occupiedPenultimate T r)) :
    {m : Columns T // (m.1 (Fin.last (n + 1))).val = r} ≃
      Columns (prune T r hoccupied) where
  toFun m := restrictColumn T r hoccupied m.1 m.2
  invFun m := ⟨liftColumn T r hoccupied m, by simp [liftColumn, liftExponents]⟩
  left_inv := by
    intro m
    apply Subtype.ext
    apply Subtype.ext
    change liftExponents T r hoccupied
      (restrictExponents T m.1 r m.2 hoccupied) = m.1.1
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · apply Fin.ext
      simpa [liftExponents] using m.2.symm
    · apply Fin.ext
      simp [liftExponents, restrictExponents]
  right_inv := by
    intro m
    apply Subtype.ext
    change restrictExponents T (liftColumn T r hoccupied m) r
      (by simp [liftColumn, liftExponents]) hoccupied = m.1
    funext i
    apply Fin.ext
    simp [restrictExponents, liftColumn, liftExponents]

theorem column_last_occupied {n : ℕ} (T : SourceTree (n + 2)) (m : Columns T) :
    Nonempty (occupiedPenultimate T (m.1 (Fin.last (n + 1))).val) := by
  classical
  have hnonempty : (sourceS T m.1).Nonempty := by
    apply Finset.card_pos.mp
    exact (Nat.zero_le (m.1 0).val).trans_lt m.2
  obtain ⟨root, hrootMem⟩ := hnonempty
  have hroot : Survives T (sourceThreshold T m.1) (Fin.succ 0) root := by
    change root ∈ survivalSet T (sourceThreshold T m.1) (Fin.succ 0) at hrootMem
    simp only [survivalSet] at hrootMem
    exact ((@Finset.mem_filter _ (Survives T (sourceThreshold T m.1) (Fin.succ 0))
      (Classical.decPred _) _ _).mp hrootMem).2
  obtain ⟨p, _, hp⟩ := survives_descendant T (sourceThreshold T m.1)
    (fun j => by simp [sourceThreshold]) (j := (Fin.last n).castSucc.succ)
    (by change 1 ≤ n + 1; omega) hroot
  rcases survives_reachesOccupied T (sourceThreshold T m.1)
      (m.1 (Fin.last (n + 1))).val (fun i => by simp [sourceThreshold])
      (by simp [sourceThreshold]) hp with hbottom | ⟨_, q, _⟩
  · have hval := congrArg Fin.val hbottom
    change n + 1 = n + 2 at hval
    omega
  · exact ⟨q⟩

noncomputable def depthOneExponents (T : SourceTree 1)
    (e : Fin (Fintype.card (Bottom T))) : Exponents T :=
  fun i => Fin.cast (by rw [Fin.eq_zero i]; rfl) e

/-- At depth one, literal source columns are precisely the possible monomial degrees. -/
noncomputable def depthOneColumnsEquiv (T : SourceTree 1) :
    Columns T ≃ Fin (Fintype.card (Bottom T)) where
  toFun m := m.1 0
  invFun e :=
    ⟨depthOneExponents T e, by
      change e.val <
        (survivalSet T (sourceThreshold T (depthOneExponents T e)) (Fin.last 1)).card
      have hbottom : survivalSet T (sourceThreshold T (depthOneExponents T e))
          (Fin.last 1) = Finset.univ := by
        ext v
        simp only [survivalSet, Finset.mem_filter, Finset.mem_univ, true_and]
        constructor
        · intro _
          trivial
        · intro _
          exact Survives.bottom v
      rw [hbottom, Finset.card_univ]
      exact e.isLt⟩
  left_inv := by
    intro m
    apply Subtype.ext
    funext i
    have hi : i = 0 := Fin.eq_zero i
    subst i
    rfl
  right_inv := by intro e; rfl

noncomputable def depthOneBottomOrder (T : SourceTree 1) :
    Fin (Fintype.card (Bottom T)) ≃o Bottom T :=
  monoEquivOfFin (Bottom T) rfl

/-- Increasing enumeration of one actual bottom sibling fiber. -/
noncomputable def fiberOrder {n : ℕ} (T : SourceTree (n + 1)) (p : Penultimate T) :
    Fin (Fintype.card (bottomFiber T p)) ≃o bottomFiber T p :=
  monoEquivOfFin (bottomFiber T p) rfl

def bottomParent {n : ℕ} (T : SourceTree (n + 1)) (b : Bottom T) :
    Penultimate T :=
  T.parent (Fin.last n) b

def bottomInFiber {n : ℕ} (T : SourceTree (n + 1)) (b : Bottom T) :
    bottomFiber T (bottomParent T b) :=
  ⟨b, rfl⟩

/-- The increasing position of a bottom vertex inside its actual sibling fiber. -/
noncomputable def fiberRank {n : ℕ} (T : SourceTree (n + 1)) (b : Bottom T) :
    ℕ :=
  (Finset.univ.filter fun c : Bottom T =>
    bottomParent T c = bottomParent T b ∧ c < b).card

/-- The monic Newton polynomial of degree `e` on an actual ordered sibling fiber. -/
noncomputable def fiberNewton {n : ℕ} (T : SourceTree (n + 1))
    (p : Penultimate T) (e : ℕ) : Polynomial ℂ :=
  ∏ j ∈ (Finset.univ.filter fun j : Fin (Fintype.card (bottomFiber T p)) => j.val < e),
    (Polynomial.X - Polynomial.C
      (T.label (Fin.last n) ((fiberOrder T p j).1)))

/-- Block-diagonal evaluation of the monic Newton bases on all actual bottom fibers. -/
noncomputable def NewtonE {n : ℕ} (T : SourceTree (n + 1)) :
    Matrix (Bottom T) (Bottom T) ℂ :=
  fun b c => if _h : bottomParent T b = bottomParent T c then
    (fiberNewton T (bottomParent T c) (fiberRank T c)).eval
      (T.label (Fin.last n) b)
  else 0

noncomputable def fiberValues {n : ℕ} (T : SourceTree (n + 1))
    (p : Penultimate T) : Fin (Fintype.card (bottomFiber T p)) → ℂ :=
  fun i => T.label (Fin.last n) (fiberOrder T p i).1

noncomputable def fiberEvaluation {n : ℕ} (T : SourceTree (n + 1))
    (p : Penultimate T) :
    Matrix (Fin (Fintype.card (bottomFiber T p)))
      (Fin (Fintype.card (bottomFiber T p))) ℂ :=
  fun i j => (fiberNewton T p j.val).eval (fiberValues T p i)

noncomputable def fiberCoefficient {n : ℕ} (T : SourceTree (n + 1))
    (p : Penultimate T) :
    Matrix (Fin (Fintype.card (bottomFiber T p)))
      (Fin (Fintype.card (bottomFiber T p))) ℂ :=
  Matrix.of fun i j => (fiberNewton T p j.val).coeff i.val

theorem fiberRank_order {n : ℕ} (T : SourceTree (n + 1))
    (p : Penultimate T) (i : Fin (Fintype.card (bottomFiber T p))) :
    fiberRank T (fiberOrder T p i).1 = i.val := by
  classical
  unfold fiberRank
  have hs :
      (Finset.univ.filter fun c : Bottom T =>
        bottomParent T c = bottomParent T (fiberOrder T p i).1 ∧
          c < (fiberOrder T p i).1) =
        (Finset.Iio i).image (fun j => (fiberOrder T p j).1) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image,
      Finset.mem_Iio]
    constructor
    · rintro ⟨hcparent, hclt⟩
      have hcparent' : bottomParent T c = p := hcparent.trans (fiberOrder T p i).2
      let c' : bottomFiber T p := ⟨c, hcparent'⟩
      let j := (fiberOrder T p).symm c'
      refine ⟨j, ?_, ?_⟩
      · apply (fiberOrder T p).lt_iff_lt.mp
        dsimp [j]
        rw [(fiberOrder T p).apply_symm_apply]
        exact hclt
      · exact congrArg Subtype.val ((fiberOrder T p).apply_symm_apply c')
    · rintro ⟨j, hji, rfl⟩
      exact ⟨(fiberOrder T p j).2.trans (fiberOrder T p i).2.symm,
        (fiberOrder T p).lt_iff_lt.mpr hji⟩
  rw [hs, Finset.card_image_of_injective]
  · exact Fin.card_Iio i
  · intro a b hab
    apply (fiberOrder T p).injective
    exact Subtype.ext hab

/-- The global Newton evaluation determinant is exactly the product of the
Mathlib-oriented sibling Vandermonde determinants over occupied fibers. -/
theorem det_NewtonE {n : ℕ} (T : SourceTree (n + 1)) :
    (NewtonE T).det = ∏ p ∈ Finset.univ.image (bottomParent T),
      (Matrix.vandermonde (fiberValues T p)).det := by
  classical
  have hdegree (p : Penultimate T)
      (e : Fin (Fintype.card (bottomFiber T p))) :
      (fiberNewton T p e.val).natDegree = e := by
    rw [fiberNewton, Polynomial.natDegree_finsetProd_X_sub_C_eq_card]
    have hs : (Finset.univ.filter fun j : Fin (Fintype.card (bottomFiber T p)) =>
        j.val < e.val) = Finset.Iio e := by
      ext j
      simp
    rw [hs, Fin.card_Iio]
  have hmonic (p : Penultimate T) (e : ℕ) : (fiberNewton T p e).Monic := by
    apply Polynomial.monic_prod_of_monic
    intro j hj
    exact Polynomial.monic_X_sub_C _
  have htri : (NewtonE T).BlockTriangular (bottomParent T) := by
    intro i j hij
    simp [NewtonE, ne_of_gt hij]
  have hblock (p : Penultimate T) :
      Matrix.reindex (fiberOrder T p).toEquiv (fiberOrder T p).toEquiv
        (fiberEvaluation T p) = (NewtonE T).toSquareBlock (bottomParent T) p := by
    rw [Matrix.toSquareBlock_def]
    ext i j
    change fiberEvaluation T p ((fiberOrder T p).symm i) ((fiberOrder T p).symm j) =
      NewtonE T i.1 j.1
    simp only [fiberEvaluation, fiberValues]
    change Polynomial.eval _ _ =
      if _h : bottomParent T i.1 = bottomParent T j.1 then
        (fiberNewton T (bottomParent T j.1) (fiberRank T j.1)).eval
          (T.label (Fin.last n) i.1)
      else 0
    have hpij : bottomParent T i.1 = bottomParent T j.1 := i.2.trans j.2.symm
    simp only [dif_pos hpij]
    have hj : bottomParent T j.1 = p := j.2
    rw [hj]
    have hrank := fiberRank_order T p ((fiberOrder T p).symm j)
    rw [(fiberOrder T p).apply_symm_apply] at hrank
    rw [hrank]
    rw [(fiberOrder T p).apply_symm_apply i]
  rw [htri.det]
  apply Finset.prod_congr rfl
  intro p hp
  rw [← hblock p]
  exact (Matrix.det_reindex_self (fiberOrder T p).toEquiv (fiberEvaluation T p)).trans
    (by
      symm
      exact Matrix.det_eval_matrixOfPolynomials_eq_det_vandermonde
        (fiberValues T p) (fun i => fiberNewton T p i.val) (hdegree p)
          (fun i => hmonic p i.val))

theorem det_NewtonE_ne_zero {n : ℕ} (T : SourceTree (n + 1)) :
    (NewtonE T).det ≠ 0 := by
  classical
  rw [det_NewtonE]
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  apply Matrix.det_vandermonde_ne_zero_iff.mpr
  intro i j hij
  apply (fiberOrder T p).injective
  apply Subtype.ext
  apply T.sibling_injective (Fin.last n)
  · exact (fiberOrder T p i).2.trans (fiberOrder T p j).2.symm
  · exact hij

end D5.S3.Quantum.Algebra.DegeneracyGraphDeterminant
