/- GID: D5/S3/Geometry/Hyperideal/PairedFaceCharts
   generality: G
   mirror-B: D5/B/S3/Geometry/Hyperideal/PairedFaceCharts
   mirror-E: none(waiver:local-quotient-chart)
   anchors: []
   utility: none
   digest: Signed local charts at interior paired-face points and cap intersections in the literal quotient. -/

import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Logic.Relation
import Mathlib.Topology.Constructions
import Mathlib.Tactic
set_option autoImplicit false
set_option relaxedAutoImplicit false
noncomputable section
open Set
namespace D5.S3.Geometry.Hyperideal.PairedFaceCharts
abbrev Coeff := Fin 4 → ℝ
def TruncatedSimplex : Set Coeff :=
  {x | x ∈ stdSimplex ℝ (Fin 4) ∧ ∀ i,x i ≤ (3/4:ℝ)}
abbrev Point := TruncatedSimplex
abbrev Occurrence (T : Type*) := T × Point
structure Pairing (T : Type*) where
  mate : T × Fin 4 → T × Fin 4
  involutive : Function.Involutive mate
  no_fixed : ∀ f,mate f ≠ f
  sigma : T × Fin 4 → Equiv.Perm (Fin 4)
  omitted : ∀ f,sigma f f.2=(mate f).2
  inverse : ∀ f,sigma (mate f)=(sigma f).symm

def permute (e : Equiv.Perm (Fin 4)) (x : Point) : Point :=
  ⟨fun k=>x.val (e.symm k),by
    refine ⟨⟨fun k=>x.property.1.1 _,?_⟩,fun k=>x.property.2 _⟩
    rw [Equiv.sum_comp e.symm,x.property.1.2]⟩
def glue {T : Type*} (P : Pairing T) (a : Occurrence T) (i : Fin 4) : Occurrence T :=
  ((P.mate (a.1,i)).1,permute (P.sigma (a.1,i)) a.2)
def Step {T : Type*} (P : Pairing T) (a b : Occurrence T) : Prop :=
  ∃ i,a.2.val i=0 ∧ b=glue P a i
def SingleZero {T : Type*} (a : Occurrence T) : Prop :=
  ∀ i j,a.2.val i=0 → a.2.val j=0 → i=j

def Collar (i:Fin 4) (δ:ℝ):Set Point:=
  {x|x.val i<δ ∧ (∀ k,k≠i → δ<x.val k) ∧ ∀ k,x.val k<(3/4:ℝ)}
def Patch {T:Type*} (P:Pairing T) (f:T×Fin 4) (δ:ℝ):Set (Occurrence T):=
  ({f.1} ×ˢ Collar f.2 δ) ∪ ({(P.mate f).1} ×ˢ Collar (P.mate f).2 δ)
abbrev RawQuotient {T:Type*} (P:Pairing T):=Quot (Step P)
def qmap {T:Type*} (P:Pairing T):Occurrence T→RawQuotient P := Quot.mk (Step P)

theorem literal_paired_face_bicollar {T:Type*} [TopologicalSpace T] [DiscreteTopology T]
    (P:Pairing T):
    ∀ (a:Occurrence T) (i:Fin 4),a.2.val i=0→
      (∀ j,j≠i→0<a.2.val j)→(∀ j,a.2.val j<(3/4:ℝ))→
      ∃ U:Set (RawQuotient P),IsOpen U ∧ qmap P a∈U ∧
        ∃ B:Set (Fin 3→ℝ),IsOpen B ∧ Nonempty (U ≃ₜ B) := by
  classical
  have chart :
    ∀ (f:T×Fin 4) (δ:ℝ),0<δ →
    IsOpen (qmap P '' Patch P f δ) ∧
    ∃ B:Set (Fin 3→ℝ),IsOpen B ∧ Nonempty ((qmap P '' Patch P f δ) ≃ₜ B) := by
    have openpatch :
        ∀ (f:T×Fin 4) (δ:ℝ),0<δ →
        IsOpen (Patch P f δ) ∧
        (∀ a b:Occurrence T,a∈Patch P f δ → Relation.EqvGen (Step P) a b → b∈Patch P f δ) ∧
        qmap P ⁻¹' (qmap P '' Patch P f δ)=Patch P f δ ∧
        IsOpen (qmap P '' Patch P f δ) := by
      have fibers :
          (∀ a b : Occurrence T,SingleZero a →
            (Relation.EqvGen (Step P) a b ↔ a=b ∨ Step P a b)) ∧
          (∀ a b : Occurrence T,(∀ i,0<a.2.val i) →
            (Quot.mk (Step P) a=Quot.mk (Step P) b ↔ a=b)) ∧
          (∀ a b : Occurrence T,∀ i,a.2.val i=0 →
            (∀ j,j≠i → 0<a.2.val j) →
            glue P a i≠a ∧
            (Quot.mk (Step P) a=Quot.mk (Step P) b ↔
              b=a ∨ b=glue P a i))
          := by
        have hback (a:Occurrence T) (i:Fin 4) :
            glue P (glue P a i) (P.mate (a.1,i)).2=a := by
          have hf : ((glue P a i).1,(P.mate (a.1,i)).2)=P.mate (a.1,i):=rfl
          apply Prod.ext
          · dsimp [glue]
            rw [P.involutive]
          · apply Subtype.ext
            funext k
            change a.2.val ((P.sigma (a.1,i)).symm
              ((P.sigma (P.mate (a.1,i))).symm k))=a.2.val k
            rw [P.inverse]
            simp
        have hzero (a:Occurrence T) (i:Fin 4) (hi:a.2.val i=0):
            (glue P a i).2.val (P.mate (a.1,i)).2=0 := by
          change a.2.val ((P.sigma (a.1,i)).symm (P.mate (a.1,i)).2)=0
          rw [←P.omitted]
          simpa using hi
        have hsingle (a:Occurrence T) (i:Fin 4) (ha:SingleZero a):
            SingleZero (glue P a i) := by
          intro k l hk hl
          change a.2.val ((P.sigma (a.1,i)).symm k)=0 at hk
          change a.2.val ((P.sigma (a.1,i)).symm l)=0 at hl
          exact (P.sigma (a.1,i)).symm.injective (ha _ _ hk hl)
        have hsymm (a b:Occurrence T) (h:Step P a b):Step P b a := by
          obtain ⟨i,hi,rfl⟩:=h
          exact ⟨(P.mate (a.1,i)).2,hzero a i hi,(hback a i).symm⟩
        have hgood (a b:Occurrence T) (h:Step P a b):SingleZero a ↔ SingleZero b := by
          constructor
          · obtain ⟨i,hi,rfl⟩:=h
            exact hsingle a i
          · obtain ⟨i,hi,he⟩:=hsymm a b h
            rw [he]
            exact hsingle b i
        have hreturn (a b c:Occurrence T) (ha:SingleZero a)
            (hab:Step P a b) (hbc:Step P b c):a=c := by
          obtain ⟨i,hi,rfl⟩:=hab
          obtain ⟨j,hj,rfl⟩:=hbc
          have hb:=hsingle a i ha
          have he:j=(P.mate (a.1,i)).2:=hb _ _ hj (hzero a i hi)
          rw [he,hback]
        have closure (a b:Occurrence T) (h:Relation.EqvGen (Step P) a b):
            (SingleZero a ↔ SingleZero b) ∧ (SingleZero a → a=b ∨ Step P a b) := by
          induction h with
          | rel a b h => exact ⟨hgood a b h,fun _=>Or.inr h⟩
          | refl a => exact ⟨Iff.rfl,fun _=>Or.inl rfl⟩
          | symm a b h ih =>
            refine ⟨ih.1.symm,?_⟩
            intro hb
            rcases ih.2 (ih.1.mpr hb) with he | hs
            · exact Or.inl he.symm
            · exact Or.inr (hsymm a b hs)
          | trans a b c hab hbc ihab ihbc =>
            refine ⟨ihab.1.trans ihbc.1,?_⟩
            intro ha
            rcases ihab.2 ha with he | hs
            · subst b
              exact ihbc.2 ha
            · rcases ihbc.2 (ihab.1.mp ha) with he | ht
              · subst c
                exact Or.inr hs
              · exact Or.inl (hreturn a b c ha hs ht)
        have exactFiber (a b:Occurrence T) (ha:SingleZero a):
            Relation.EqvGen (Step P) a b ↔ a=b ∨ Step P a b := by
          constructor
          · exact fun h=>(closure a b h).2 ha
          · rintro (rfl|h)
            · exact Relation.EqvGen.refl _
            · exact Relation.EqvGen.rel _ _ h
        refine ⟨exactFiber,?_,?_⟩
        · intro a b ha
          have hg:SingleZero a:=by
            intro i j hi hj
            exact False.elim ((ha i).ne' hi)
          have hq : (Quot.mk (Step P) a=Quot.mk (Step P) b) ↔
              Relation.EqvGen (Step P) a b:=⟨Quot.eqvGen_exact,Quot.eqvGen_sound⟩
          rw [hq,exactFiber a b hg]
          constructor
          · rintro (he|⟨i,hi,hb⟩)
            · exact he
            · exact False.elim ((ha i).ne' hi)
          · exact Or.inl
        · intro a b i hi hj
          have hg:SingleZero a:=by
            intro k l hk hl
            have hki:k=i:=by
              by_contra h
              exact (hj k h).ne' hk
            have hli:l=i:=by
              by_contra h
              exact (hj l h).ne' hl
            exact hki.trans hli.symm
          refine ⟨?_,?_⟩
          · intro he
            have hz : a.2.val (P.mate (a.1,i)).2=0 := by
              simpa only [he] using hzero a i hi
            have hej : (P.mate (a.1,i)).2=i := hg _ _ hz hi
            apply P.no_fixed (a.1,i)
            have ht : (P.mate (a.1,i)).1=a.1 :=
              congrArg (fun z : Occurrence T=>z.1) he
            exact Prod.ext ht hej
          constructor
          · intro he
            rcases (exactFiber a b hg).mp (Quot.eqvGen_exact he) with he|hs
            · exact Or.inl he.symm
            · obtain ⟨j,hj,hb⟩:=hs
              have heji:j=i:=hg j i hj hi
              exact Or.inr (heji ▸ hb)
          · rintro (rfl|rfl)
            · rfl
            · exact Quot.sound ⟨i,hi,rfl⟩
      have permuteCollar (e:Equiv.Perm (Fin 4)) (x:Point) (i j:Fin 4) (δ:ℝ)
          (he:e i=j) (hx:x∈Collar i δ):permute e x∈Collar j δ := by
        rcases hx with ⟨hxi,hother,hupper⟩
        refine ⟨?_,?_,?_⟩
        · change x.val (e.symm j)<δ
          rw [←he]
          simpa using hxi
        · intro k hk
          change δ<x.val (e.symm k)
          apply hother
          intro hh
          apply hk
          calc
            k=e (e.symm k):=(e.apply_symm_apply k).symm
            _=e i:=congrArg e hh
            _=j:=he
        · intro k
          exact hupper _
      have openCollar (i:Fin 4) (δ:ℝ):IsOpen (Collar i δ) := by
        have hc (k:Fin 4):Continuous (fun x:Point=>x.val k):=
          (continuous_apply k).comp continuous_subtype_val
        have hn:IsOpen {x:Point|∀ k,k≠i → δ<x.val k}:=by
          simp only [setOf_forall]
          apply isOpen_iInter_of_finite
          intro k
          apply isOpen_iInter_of_finite
          intro hk
          exact isOpen_lt continuous_const (hc k)
        have hu:IsOpen {x:Point|∀ k,x.val k<(3/4:ℝ)}:=by
          simp only [setOf_forall]
          exact isOpen_iInter_of_finite fun k=>isOpen_lt (hc k) continuous_const
        exact (isOpen_lt (hc i) continuous_const).inter (hn.inter hu)
      have oneZero (a:Occurrence T) (i:Fin 4) (δ:ℝ) (hδ:0<δ)
          (hx:a.2∈Collar i δ):
          (∀ k,a.2.val k=0 → k=i) ∧ SingleZero a := by
        have hz (k:Fin 4) (hk:a.2.val k=0):k=i:=by
          by_contra hki
          have hp:=hx.2.1 k hki
          rw [hk] at hp
          linarith
        exact ⟨hz,fun k l hk hl=>(hz k hk).trans (hz l hl).symm⟩
      intro f δ hδ
      have hopen:IsOpen (Patch P f δ):=
        ((isOpen_discrete ({f.1}:Set T)).prod (openCollar f.2 δ)).union
          ((isOpen_discrete ({(P.mate f).1}:Set T)).prod (openCollar (P.mate f).2 δ))
      have hg (a:Occurrence T) (ha:a∈Patch P f δ):SingleZero a := by
        change (a.1=f.1 ∧ a.2∈Collar f.2 δ) ∨
          (a.1=(P.mate f).1 ∧ a.2∈Collar (P.mate f).2 δ) at ha
        rcases ha with ⟨ht,hx⟩|⟨ht,hx⟩
        · exact (oneZero a f.2 δ hδ hx).2
        · exact (oneZero a (P.mate f).2 δ hδ hx).2
      have stepStays (a b:Occurrence T) (ha:a∈Patch P f δ) (hab:Step P a b):
          b∈Patch P f δ := by
        change (a.1=f.1 ∧ a.2∈Collar f.2 δ) ∨
          (a.1=(P.mate f).1 ∧ a.2∈Collar (P.mate f).2 δ) at ha
        obtain ⟨k,hk,rfl⟩:=hab
        rcases ha with ⟨ht,hx⟩|⟨ht,hx⟩
        · have heki:k=f.2:=(oneZero a f.2 δ hδ hx).1 k hk
          have hf:(a.1,k)=f:=Prod.ext ht heki
          change (((glue P a k).1=f.1 ∧ (glue P a k).2∈Collar f.2 δ) ∨
            ((glue P a k).1=(P.mate f).1 ∧
              (glue P a k).2∈Collar (P.mate f).2 δ))
          apply Or.inr
          constructor
          · change (P.mate (a.1,k)).1=(P.mate f).1
            rw [hf]
          · change permute (P.sigma (a.1,k)) a.2∈Collar (P.mate f).2 δ
            rw [hf]
            exact permuteCollar (P.sigma f) a.2 f.2 (P.mate f).2 δ (P.omitted f) hx
        · have heki:k=(P.mate f).2:=(oneZero a (P.mate f).2 δ hδ hx).1 k hk
          have hf:(a.1,k)=P.mate f:=Prod.ext ht heki
          change (((glue P a k).1=f.1 ∧ (glue P a k).2∈Collar f.2 δ) ∨
            ((glue P a k).1=(P.mate f).1 ∧
              (glue P a k).2∈Collar (P.mate f).2 δ))
          apply Or.inl
          constructor
          · change (P.mate (a.1,k)).1=f.1
            rw [hf,P.involutive]
          · change permute (P.sigma (a.1,k)) a.2∈Collar f.2 δ
            rw [hf]
            have he:(P.sigma (P.mate f)) (P.mate f).2=f.2:=by
              have h := P.omitted (P.mate f)
              rw [P.involutive f] at h
              exact h
            exact permuteCollar (P.sigma (P.mate f)) a.2 (P.mate f).2 f.2 δ he hx
      have saturated (a b:Occurrence T) (ha:a∈Patch P f δ)
          (hab:Relation.EqvGen (Step P) a b):b∈Patch P f δ := by
        rcases (fibers.1 a b (hg a ha)).mp hab with he|hs
        · simpa only [←he] using ha
        · exact stepStays a b ha hs
      have hpre:qmap P ⁻¹' (qmap P '' Patch P f δ)=Patch P f δ := by
        ext a
        constructor
        · rintro ⟨b,hb,he⟩
          have hab:Relation.EqvGen (Step P) b a:=Quot.eqvGen_exact he
          exact saturated b a hb hab
        · exact fun ha=>⟨a,ha,rfl⟩
      have hquot:Topology.IsQuotientMap (qmap P):=isQuotientMap_quot_mk
      refine ⟨hopen,saturated,hpre,?_⟩
      rw [←hquot.isOpen_preimage,hpre]
      exact hopen
    classical
    intro f δ hδ
    let e : Equiv.Perm (Fin 4) := Equiv.swap 0 f.2
    let σ := P.sigma f
    have he : e 0=f.2 := by simp [e]
    let ep : Equiv.Perm (Fin 4) := e.trans σ
    have hep : ep 0=(P.mate f).2 := by simpa [ep,he] using P.omitted f
    let fold : (Fin 3→ℝ)→Coeff := fun w=>![|w 2|,w 0,w 1,1-|w 2|-w 0-w 1]
    let B : Set (Fin 3→ℝ) := {w | |w 2|<δ ∧ (∀ k:Fin 4,k≠0→δ<fold w k) ∧
      ∀ k:Fin 4,fold w k<(3/4:ℝ)}
    have hfcont : Continuous fold := by
      apply continuous_pi
      intro k
      fin_cases k <;> dsimp [fold] <;> fun_prop
    have hB : IsOpen B := by
      have hc (k:Fin 4):Continuous (fun w:Fin 3→ℝ=>fold w k):=(continuous_apply k).comp hfcont
      change IsOpen ({w:Fin 3→ℝ | |w 2|<δ} ∩
        ({w:Fin 3→ℝ|∀ k:Fin 4,k≠0→δ<fold w k} ∩ {w:Fin 3→ℝ|∀ k:Fin 4,fold w k<(3/4:ℝ)}))
      refine IsOpen.inter (isOpen_lt (by fun_prop) continuous_const) (IsOpen.inter ?_ ?_)
      · simp only [setOf_forall]
        apply isOpen_iInter_of_finite
        intro k
        apply isOpen_iInter_of_finite
        intro hk
        exact isOpen_lt continuous_const (hc k)
      · simp only [setOf_forall]
        exact isOpen_iInter_of_finite fun k=>isOpen_lt (hc k) continuous_const
    have foldValid (w:B):fold w.val∈TruncatedSimplex := by
      refine ⟨⟨?_,?_⟩,?_⟩
      · intro k
        by_cases hk:k=0
        · subst k
          exact abs_nonneg _
        · exact le_of_lt (hδ.trans (w.property.2.1 k hk))
      · simp [fold,Fin.sum_univ_succ]
      · intro k
        exact le_of_lt (w.property.2.2 k)
    let fp : B→Point := fun w=>⟨fold w.val,foldValid w⟩
    have hfp : Continuous fp := hfcont.comp continuous_subtype_val |>.subtype_mk _
    have permCont (g:Equiv.Perm (Fin 4)):Continuous (permute g) := by
      apply Continuous.subtype_mk
      apply continuous_pi
      intro k
      exact (continuous_apply (g.symm k)).comp continuous_subtype_val
    have foldCollar (w:B):fp w∈Collar 0 δ := by
      exact w.property
    have permCollar (g:Equiv.Perm (Fin 4)) (x:Point) (i:Fin 4) (hx:x∈Collar i δ):
        permute g x∈Collar (g i) δ := by
      refine ⟨?_,?_,?_⟩
      · simpa [permute] using hx.1
      · intro k hk
        apply hx.2.1
        intro hh
        apply hk
        exact (g.apply_symm_apply k).symm.trans (congrArg g hh)
      · exact fun k=>hx.2.2 _
    let plus : B→Occurrence T := fun w=>(f.1,permute e (fp w))
    let minus : B→Occurrence T := fun w=>((P.mate f).1,permute ep (fp w))
    have hplus : Continuous plus := continuous_const.prodMk ((permCont e).comp hfp)
    have hminus : Continuous minus := continuous_const.prodMk ((permCont ep).comp hfp)
    have hplusmem (w:B):plus w∈Patch P f δ := by
      apply Or.inl
      exact ⟨rfl,he ▸ permCollar e (fp w) 0 (foldCollar w)⟩
    have hminusmem (w:B):minus w∈Patch P f δ := by
      apply Or.inr
      exact ⟨rfl,hep ▸ permCollar ep (fp w) 0 (foldCollar w)⟩
    have seam (w:B) (hs:w.val 2=0):qmap P (plus w)=qmap P (minus w) := by
      apply Quot.sound
      refine ⟨f.2,?_,?_⟩
      · change fold w.val (e.symm f.2)=0
        rw [←he,e.symm_apply_apply]
        simp [fold,hs]
      · apply Prod.ext
        · rfl
        · apply Subtype.ext
          funext k
          rfl
    let inv : B→RawQuotient P := fun w=>if 0≤w.val 2 then qmap P (plus w) else qmap P (minus w)
    have hinv : Continuous inv := by
      apply Continuous.if_le ((continuous_quot_mk).comp hplus) ((continuous_quot_mk).comp hminus)
        continuous_const ((continuous_apply 2).comp continuous_subtype_val)
      intro w hw
      exact seam w hw.symm
    have hinvmem (w:B):inv w∈qmap P '' Patch P f δ := by
      dsimp [inv]
      split_ifs
      · exact ⟨plus w,hplusmem w,rfl⟩
      · exact ⟨minus w,hminusmem w,rfl⟩
    let up : Set (Occurrence T) := {f.1} ×ˢ Collar f.2 δ
    let down : Set (Occurrence T) := {(P.mate f).1} ×ˢ Collar (P.mate f).2 δ
    have disjoint (a:Occurrence T) (hu:a∈up) (hd:a∈down):False := by
      have hi:f.2≠(P.mate f).2 := by
        intro hh
        apply P.no_fixed f
        exact Prod.ext (hd.1.symm.trans hu.1) hh.symm
      have hlo:=hd.2.2.1 f.2 hi
      have hhi:=hu.2.1
      linarith
    let cp : Occurrence T→(Fin 3→ℝ) := fun a=>![a.2.val (e 1),a.2.val (e 2),a.2.val (e 0)]
    let cm : Occurrence T→(Fin 3→ℝ) := fun a=>![a.2.val (ep 1),a.2.val (ep 2),-a.2.val (ep 0)]
    have sumFour (x:Point):x.val 0+x.val 1+x.val 2+x.val 3=1 := by
      simpa [Fin.sum_univ_succ,add_assoc] using x.property.1.2
    have permSum (g:Equiv.Perm (Fin 4)) (x:Point):
        x.val (g 0)+x.val (g 1)+x.val (g 2)+x.val (g 3)=1 := by
      have hh : ∑ k:Fin 4,x.val (g k)=1 := by rw [Equiv.sum_comp g,x.property.1.2]
      simpa [Fin.sum_univ_succ,add_assoc] using hh
    have reconstruct (g:Equiv.Perm (Fin 4)) (x:Point):
        (fun k:Fin 4=>x.val (g k))=fold ![x.val (g 1),x.val (g 2),x.val (g 0)] := by
      funext k
      have hx:x.val (g 0)≥0:=x.property.1.1 _
      have hh:=permSum g x
      fin_cases k <;> simp [fold,abs_of_nonneg hx] <;> linarith
    have cpB (a:Occurrence T) (ha:a∈up):cp a∈B := by
      have hr:=reconstruct e a.2
      refine ⟨?_,?_,?_⟩
      · simpa [cp,abs_of_nonneg (a.2.property.1.1 _),he] using ha.2.1
      · intro k hk
        rw [←hr]
        apply ha.2.2.1
        exact fun hh=>hk (e.injective (hh.trans he.symm))
      · intro k
        rw [←hr]
        exact ha.2.2.2 _
    have cmB (a:Occurrence T) (ha:a∈down):cm a∈B := by
      have hr : (fun k:Fin 4=>a.2.val (ep k))=fold (cm a) := by
        rw [reconstruct ep a.2]
        simp [fold,cm,abs_of_nonneg (a.2.property.1.1 _)]
      refine ⟨?_,?_,?_⟩
      · simpa [cm,abs_of_nonneg (a.2.property.1.1 _),hep] using ha.2.1
      · intro k hk
        rw [←hr]
        apply ha.2.2.1
        exact fun hh=>hk (ep.injective (hh.trans hep.symm))
      · intro k
        rw [←hr]
        exact ha.2.2.2 _
    have backPlus (a:Occurrence T) (ha:a∈up):plus ⟨cp a,cpB a ha⟩=a := by
      apply Prod.ext ha.1.symm
      apply Subtype.ext
      funext k
      change fold (cp a) (e.symm k)=a.2.val k
      rw [←reconstruct e a.2]
      simp
    have backMinus (a:Occurrence T) (ha:a∈down):minus ⟨cm a,cmB a ha⟩=a := by
      apply Prod.ext ha.1.symm
      apply Subtype.ext
      funext k
      change fold (cm a) (ep.symm k)=a.2.val k
      have hr : fold (cm a)=fold ![a.2.val (ep 1),a.2.val (ep 2),a.2.val (ep 0)] := by
        simp [fold,cm,abs_of_nonneg (a.2.property.1.1 _)]
      rw [hr,←reconstruct ep a.2]
      simp
    have cpPlus (w:B):cp (plus w)=![w.val 0,w.val 1,|w.val 2|] := by
      funext k
      fin_cases k <;> simp [cp,plus,permute,fp,fold]
    have cmMinus (w:B):cm (minus w)=![w.val 0,w.val 1,-|w.val 2|] := by
      funext k
      fin_cases k <;> simp [cm,minus,permute,fp,fold]
    have qBackPlus (a:Occurrence T) (ha:a∈up):inv ⟨cp a,cpB a ha⟩=qmap P a := by
      have hs:0≤cp a 2:=a.2.property.1.1 _
      simp only [inv,hs,ite_true,backPlus a ha]
    have qBackMinus (a:Occurrence T) (ha:a∈down):inv ⟨cm a,cmB a ha⟩=qmap P a := by
      by_cases hs:cm a 2<0
      · simp only [inv,not_le_of_gt hs,ite_false,backMinus a ha]
      · have hz:cm a 2=0:=by
          have hh:a.2.val (ep 0)≥0:=a.2.property.1.1 _
          dsimp [cm] at hs ⊢
          linarith
        simp only [inv,le_of_eq hz.symm,ite_true]
        exact (seam ⟨cm a,cmB a ha⟩ hz).trans (congrArg (qmap P) (backMinus a ha))
    have onlyZero (a:Occurrence T) (i:Fin 4) (ha:a.2∈Collar i δ)
        (k:Fin 4) (hk:a.2.val k=0):k=i := by
      by_contra hki
      have hp:=ha.2.1 k hki
      rw [hk] at hp
      linarith
    have stepPlus (a b:Occurrence T) (ha:a∈up) (hs:Step P a b):
        b∈down ∧ cp a=cm b := by
      obtain ⟨i,hi,rfl⟩:=hs
      have heif:i=f.2:=onlyZero a f.2 ha.2 i hi
      have hf:(a.1,i)=f:=Prod.ext ha.1 heif
      constructor
      · refine ⟨?_,?_⟩
        · change (P.mate (a.1,i)).1=(P.mate f).1
          rw [hf]
        · change permute (P.sigma (a.1,i)) a.2∈Collar (P.mate f).2 δ
          rw [hf,←P.omitted f]
          exact permCollar _ a.2 f.2 ha.2
      · funext k
        have hz:a.2.val (e 0)=0:=by rw [he,←heif];exact hi
        fin_cases k <;> simp [cp,cm,ep,glue,permute,hf,σ,hz]
    have stepMinus (a b:Occurrence T) (ha:a∈down) (hs:Step P a b):
        b∈up ∧ cm a=cp b := by
      obtain ⟨i,hi,rfl⟩:=hs
      have heif:i=(P.mate f).2:=onlyZero a (P.mate f).2 ha.2 i hi
      have hf:(a.1,i)=P.mate f:=Prod.ext ha.1 heif
      constructor
      · refine ⟨?_,?_⟩
        · change (P.mate (a.1,i)).1=f.1
          rw [hf,P.involutive]
        · change permute (P.sigma (a.1,i)) a.2∈Collar f.2 δ
          rw [hf]
          have hidx:(P.sigma (P.mate f)) (P.mate f).2=f.2:=by
            simpa only [P.involutive f] using P.omitted (P.mate f)
          rw [←hidx]
          exact permCollar _ a.2 _ ha.2
      · funext k
        have hz:a.2.val (ep 0)=0:=by rw [hep,←heif];exact hi
        have hz' : a.2.val (σ (e 0))=0:=hz
        fin_cases k <;> simp [cp,cm,ep,glue,permute,hf,P.inverse,σ,hz']
    let CF : Occurrence T→(Fin 3→ℝ) := fun a=>if a∈up then cp a else if a∈down then cm a else 0
    have hCFplus (a:Occurrence T) (ha:a∈up):CF a=cp a := by simp [CF,ha]
    have hCFminus (a:Occurrence T) (ha:a∈down):CF a=cm a := by
      have hu:a∉up:=fun hh=>disjoint a hh ha
      simp [CF,hu,ha]
    have hCFstep (a b:Occurrence T) (hs:Step P a b):CF a=CF b := by
      by_cases hu:a∈up
      · obtain ⟨hd,heq⟩:=stepPlus a b hu hs
        rw [hCFplus a hu,hCFminus b hd]
        exact heq
      · by_cases hd:a∈down
        · obtain ⟨hu',heq⟩:=stepMinus a b hd hs
          rw [hCFminus a hd,hCFplus b hu']
          exact heq
        · have ha:a∉Patch P f δ:=fun h=>h.elim hu hd
          have hb:b∉Patch P f δ:=by
            intro hh
            exact ha ((openpatch f δ hδ).2.1 b a hh (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ hs)))
          have hbu:b∉up:=fun h=>hb (Or.inl h)
          have hbd:b∉down:=fun h=>hb (Or.inr h)
          simp [CF,hu,hd,hbu,hbd]
    let desc : RawQuotient P→(Fin 3→ℝ) := Quot.lift CF hCFstep
    have descRep (a:Occurrence T):desc (qmap P a)=CF a:=rfl
    have descB (q:RawQuotient P) (hq:q∈qmap P '' Patch P f δ):desc q∈B := by
      obtain ⟨a,ha,rfl⟩:=hq
      rw [descRep]
      rcases ha with hu|hd
      · rw [hCFplus a hu]
        exact cpB a hu
      · rw [hCFminus a hd]
        exact cmB a hd
    have descInv (w:B):desc (inv w)=w.val := by
      dsimp [inv]
      split_ifs with hs
      · have hu:plus w∈up:=⟨rfl,he ▸ permCollar e (fp w) 0 (foldCollar w)⟩
        rw [descRep,hCFplus _ hu]
        rw [cpPlus]
        funext k
        fin_cases k <;> simp [abs_of_nonneg hs]
      · have hd:minus w∈down:=⟨rfl,hep ▸ permCollar ep (fp w) 0 (foldCollar w)⟩
        rw [descRep,hCFminus _ hd,cmMinus]
        funext k
        fin_cases k <;> simp [abs_of_neg (lt_of_not_ge hs)]
    let U : Set (RawQuotient P) := qmap P '' Patch P f δ
    let forward : U→B := fun q=>⟨desc q.val,descB q.val q.property⟩
    let backward : B→U := fun w=>⟨inv w,hinvmem w⟩
    have leftInverse (q:U):backward (forward q)=q := by
      apply Subtype.ext
      obtain ⟨a,ha,heq⟩:=q.property
      change inv (forward q)=q.val
      rcases ha with hu|hd
      · have hw:forward q=⟨cp a,cpB a hu⟩:=by
          apply Subtype.ext
          change desc q.val=cp a
          rw [←heq,descRep,hCFplus a hu]
        rw [hw]
        exact (qBackPlus a hu).trans heq
      · have hw:forward q=⟨cm a,cmB a hd⟩:=by
          apply Subtype.ext
          change desc q.val=cm a
          rw [←heq,descRep,hCFminus a hd]
        rw [hw]
        exact (qBackMinus a hd).trans heq
    have rightInverse (w:B):forward (backward w)=w := by
      apply Subtype.ext
      exact descInv w
    have hcp : Continuous cp := by
      apply continuous_pi
      intro k
      fin_cases k <;> dsimp [cp] <;> exact (continuous_apply _).comp (continuous_subtype_val.comp continuous_snd)
    have hcm : Continuous cm := by
      apply continuous_pi
      intro k
      fin_cases k <;> dsimp [cm]
      · exact (continuous_apply _).comp (continuous_subtype_val.comp continuous_snd)
      · exact (continuous_apply _).comp (continuous_subtype_val.comp continuous_snd)
      · exact ((continuous_apply _).comp (continuous_subtype_val.comp continuous_snd)).neg
    have openCollar (i:Fin 4):IsOpen (Collar i δ) := by
      have hc (k:Fin 4):Continuous (fun x:Point=>x.val k):=(continuous_apply k).comp continuous_subtype_val
      have hn:IsOpen {x:Point|∀ k,k≠i→δ<x.val k}:=by
        simp only [setOf_forall]
        apply isOpen_iInter_of_finite
        intro k
        apply isOpen_iInter_of_finite
        intro hk
        exact isOpen_lt continuous_const (hc k)
      have ht:IsOpen {x:Point|∀ k,x.val k<(3/4:ℝ)}:=by
        simp only [setOf_forall]
        exact isOpen_iInter_of_finite fun k=>isOpen_lt (hc k) continuous_const
      exact (isOpen_lt (hc i) continuous_const).inter (hn.inter ht)
    have hup:IsOpen up:=(isOpen_discrete _).prod (openCollar _)
    have hdown:IsOpen down:=(isOpen_discrete _).prod (openCollar _)
    have hU:IsOpen U:=(openpatch f δ hδ).2.2.2
    have hpre:qmap P ⁻¹' U=Patch P f δ:=(openpatch f δ hδ).2.2.1
    have hCFcont : Continuous (fun a:qmap P ⁻¹' U=>CF a.val) := by
      apply continuous_iff_continuousAt.mpr
      intro a
      have ha:a.val∈Patch P f δ:=hpre ▸ a.property
      rcases ha with hu|hd
      · apply ((hcp.comp continuous_subtype_val).continuousAt).congr_of_eventuallyEq
        filter_upwards [(hup.preimage continuous_subtype_val).mem_nhds hu] with z hz
        exact hCFplus z.val hz
      · apply ((hcm.comp continuous_subtype_val).continuousAt).congr_of_eventuallyEq
        filter_upwards [(hdown.preimage continuous_subtype_val).mem_nhds hd] with z hz
        exact hCFminus z.val hz
    have hforward : Continuous forward := by
      have hq : Topology.IsQuotientMap (U.restrictPreimage (qmap P)):=
        (isQuotientMap_quot_mk).restrictPreimage_isOpen hU
      have hc:Continuous (fun q:U=>desc q.val):=by
        apply hq.continuous_iff.mpr
        exact hCFcont
      exact hc.subtype_mk _
    have hbackward : Continuous backward := hinv.subtype_mk _
    let h : U ≃ₜ B := {
      toFun:=forward
      invFun:=backward
      left_inv:=leftInverse
      right_inv:=rightInverse
      continuous_toFun:=hforward
      continuous_invFun:=hbackward }
    exact ⟨hU,B,hB,⟨h⟩⟩
  intro a i hi hpos hupper
  let e : Equiv.Perm (Fin 4) := Equiv.swap 0 i
  have he:e 0=i:=by simp [e]
  have hp (j:Fin 4) (hj:j≠0):0<a.2.val (e j):=by
    apply hpos
    intro hh
    exact hj (e.injective (hh.trans he.symm))
  let m : ℝ := min (a.2.val (e 1)) (min (a.2.val (e 2)) (a.2.val (e 3)))
  have hm:0<m:=lt_min (hp 1 (by decide)) (lt_min (hp 2 (by decide)) (hp 3 (by decide)))
  let δ : ℝ := m/2
  have hδ:0<δ:=by dsimp [δ];linarith
  have hmδ:δ<m:=by dsimp [δ];linarith
  have hsmall (j:Fin 4) (hj:j≠i):δ<a.2.val j := by
    let k:=e.symm j
    have hk:k≠0:=by
      intro hh
      apply hj
      calc
        j=e (e.symm j):=(e.apply_symm_apply j).symm
        _=e 0:=congrArg e hh
        _=i:=he
    have hjk:e k=j:=e.apply_symm_apply j
    have hbound (l:Fin 4) (hl:l≠0):m≤a.2.val (e l):=by
      fin_cases l
      · exact False.elim (hl rfl)
      · exact min_le_left _ _
      · exact (min_le_right _ _).trans (min_le_left _ _)
      · exact (min_le_right _ _).trans (min_le_right _ _)
    have hmk:m≤a.2.val (e k):=hbound k hk
    rw [hjk] at hmk
    exact hmδ.trans_le hmk
  have hcollar:a.2∈Collar i δ:=⟨by simpa only [hi] using hδ,hsmall,hupper⟩
  let f : T×Fin 4 := (a.1,i)
  obtain ⟨hU,B,hB,hchart⟩:=chart f δ hδ
  refine ⟨qmap P '' Patch P f δ,hU,⟨a,Or.inl ⟨rfl,hcollar⟩,rfl⟩,B,hB,hchart⟩

def CapCollar (i c:Fin 4) (δ:ℝ):Set Point:=
  {x|x.val i<δ ∧ (∀ k,k≠i→δ<x.val k) ∧ (3/4:ℝ)-δ<x.val c ∧ ∀ k,k≠c→x.val k<(3/4:ℝ)}
def CapPatch {T:Type*} (P:Pairing T) (f:T×Fin 4) (c:Fin 4) (δ:ℝ):Set (Occurrence T):=
  ({f.1} ×ˢ CapCollar f.2 c δ) ∪
    ({(P.mate f).1} ×ˢ CapCollar (P.mate f).2 (P.sigma f c) δ)
abbrev HalfSpace := {w:Fin 3→ℝ|0≤w 0}

def CapMarked {T:Type*} (P:Pairing T):RawQuotient P→Prop :=
  Quot.lift (fun a:Occurrence T=>∃ j,a.2.val j=(3/4:ℝ)) (by
    intro a b hab
    obtain ⟨i,hi,rfl⟩:=hab
    apply propext
    constructor
    · rintro ⟨j,hj⟩
      exact ⟨P.sigma (a.1,i) j,by simpa [glue,permute] using hj⟩
    · rintro ⟨j,hj⟩
      exact ⟨(P.sigma (a.1,i)).symm j,hj⟩)
def SeamMarked {T:Type*} (P:Pairing T):RawQuotient P→Prop :=
  Quot.lift (fun a:Occurrence T=>∃ j,a.2.val j=0) (by
    intro a b hab
    obtain ⟨i,hi,rfl⟩:=hab
    apply propext
    constructor
    · rintro ⟨j,hj⟩
      exact ⟨P.sigma (a.1,i) j,by simpa [glue,permute] using hj⟩
    · rintro ⟨j,hj⟩
      exact ⟨(P.sigma (a.1,i)).symm j,hj⟩)

theorem literal_paired_cap_halfchart {T:Type*} [TopologicalSpace T] [DiscreteTopology T]
    (P:Pairing T):
    ∀ (a:Occurrence T) (i c:Fin 4),a.2.val i=0→a.2.val c=(3/4:ℝ)→
      (∀ j,j≠i→0<a.2.val j)→
      ∃ U:Set (RawQuotient P),IsOpen U ∧ qmap P a∈U ∧
        ∃ B:Set HalfSpace,IsOpen B ∧ ∃ h:U ≃ₜ B,
          (∀ q:U,CapMarked P q.val ↔ (h q).val.val 0=0) ∧
          (∀ q:U,SeamMarked P q.val ↔ (h q).val.val 2=0) := by
  classical
  have permCollar (g:Equiv.Perm (Fin 4)) (x:Point) (i c:Fin 4) (δ:ℝ)
      (hx:x∈CapCollar i c δ):permute g x∈CapCollar (g i) (g c) δ := by
    refine ⟨?_,?_,?_,?_⟩
    · simpa [permute] using hx.1
    · intro k hk
      apply hx.2.1
      exact fun hh=>hk ((g.apply_symm_apply k).symm.trans (congrArg g hh))
    · simpa [permute] using hx.2.2.1
    · intro k hk
      apply hx.2.2.2
      exact fun hh=>hk ((g.apply_symm_apply k).symm.trans (congrArg g hh))
  have openCollar (i c:Fin 4) (δ:ℝ):IsOpen (CapCollar i c δ) := by
    have hc (k:Fin 4):Continuous (fun x:Point=>x.val k):=(continuous_apply k).comp continuous_subtype_val
    have hn:IsOpen {x:Point|∀ k,k≠i→δ<x.val k}:=by
      simp only [setOf_forall]
      apply isOpen_iInter_of_finite
      intro k
      apply isOpen_iInter_of_finite
      intro hk
      exact isOpen_lt continuous_const (hc k)
    have ht:IsOpen {x:Point|∀ k,k≠c→x.val k<(3/4:ℝ)}:=by
      simp only [setOf_forall]
      apply isOpen_iInter_of_finite
      intro k
      apply isOpen_iInter_of_finite
      intro hk
      exact isOpen_lt (hc k) continuous_const
    exact (isOpen_lt (hc i) continuous_const).inter
      (hn.inter ((isOpen_lt continuous_const (hc c)).inter ht))
  have onlyZero (a:Occurrence T) (i c:Fin 4) (δ:ℝ) (hδ:0<δ)
      (ha:a.2∈CapCollar i c δ) (k:Fin 4) (hk:a.2.val k=0):k=i := by
    by_contra hki
    have hp:=ha.2.1 k hki
    rw [hk] at hp
    linarith
  have hback (a:Occurrence T) (i:Fin 4):
      glue P (glue P a i) (P.mate (a.1,i)).2=a := by
    apply Prod.ext
    · dsimp [glue]
      rw [P.involutive]
    · apply Subtype.ext
      funext k
      change a.2.val ((P.sigma (a.1,i)).symm
        ((P.sigma (P.mate (a.1,i))).symm k))=a.2.val k
      rw [P.inverse]
      simp
  have hsymm (a b:Occurrence T) (hab:Step P a b):Step P b a := by
    obtain ⟨i,hi,rfl⟩:=hab
    refine ⟨(P.mate (a.1,i)).2,?_,(hback a i).symm⟩
    change a.2.val ((P.sigma (a.1,i)).symm (P.mate (a.1,i)).2)=0
    rw [←P.omitted]
    simpa using hi
  have openpatch :
      ∀ (f:T×Fin 4) (c:Fin 4) (δ:ℝ),0<δ→
      IsOpen (CapPatch P f c δ) ∧
      (∀ a b:Occurrence T,a∈CapPatch P f c δ→Relation.EqvGen (Step P) a b→b∈CapPatch P f c δ) ∧
      qmap P ⁻¹' (qmap P '' CapPatch P f c δ)=CapPatch P f c δ ∧
      IsOpen (qmap P '' CapPatch P f c δ) := by
    intro f c δ hδ
    have hopen:IsOpen (CapPatch P f c δ):=
      ((isOpen_discrete ({f.1}:Set T)).prod (openCollar f.2 c δ)).union
        ((isOpen_discrete ({(P.mate f).1}:Set T)).prod
          (openCollar (P.mate f).2 (P.sigma f c) δ))
    have stepStays (a b:Occurrence T) (ha:a∈CapPatch P f c δ) (hab:Step P a b):
        b∈CapPatch P f c δ := by
      obtain ⟨k,hk,rfl⟩:=hab
      rcases ha with hu|hd
      · have hki:k=f.2:=onlyZero a f.2 c δ hδ hu.2 k hk
        have hf:(a.1,k)=f:=Prod.ext hu.1 hki
        apply Or.inr
        refine ⟨?_,?_⟩
        · change (P.mate (a.1,k)).1=(P.mate f).1
          rw [hf]
        · change permute (P.sigma (a.1,k)) a.2∈CapCollar (P.mate f).2 (P.sigma f c) δ
          rw [hf,←P.omitted f]
          exact permCollar _ a.2 _ _ δ hu.2
      · have hki:k=(P.mate f).2:=onlyZero a (P.mate f).2 (P.sigma f c) δ hδ hd.2 k hk
        have hf:(a.1,k)=P.mate f:=Prod.ext hd.1 hki
        apply Or.inl
        refine ⟨?_,?_⟩
        · change (P.mate (a.1,k)).1=f.1
          rw [hf,P.involutive]
        · change permute (P.sigma (a.1,k)) a.2∈CapCollar f.2 c δ
          rw [hf]
          have hi:(P.sigma (P.mate f)) (P.mate f).2=f.2:=by
            simpa only [P.involutive f] using P.omitted (P.mate f)
          have hc:(P.sigma (P.mate f)) (P.sigma f c)=c:=by rw [P.inverse];simp
          rw [←hi,←hc]
          exact permCollar _ a.2 _ _ δ hd.2
    let R : Occurrence T→Occurrence T→Prop := fun a b=>a∈CapPatch P f c δ ↔ b∈CapPatch P f c δ
    have hR:Equivalence R:=⟨fun _=>Iff.rfl,fun h=>h.symm,fun h h'=>h.trans h'⟩
    have hSR:Step P≤R:=fun a b hab=>⟨fun ha=>stepStays a b ha hab,fun hb=>stepStays b a hb (hsymm a b hab)⟩
    have saturated (a b:Occurrence T) (ha:a∈CapPatch P f c δ)
        (hab:Relation.EqvGen (Step P) a b):b∈CapPatch P f c δ:=
      ((hR.eqvGen_iff).mp (Relation.EqvGen.mono hSR a b hab)).mp ha
    have hpre:qmap P ⁻¹' (qmap P '' CapPatch P f c δ)=CapPatch P f c δ := by
      ext a
      constructor
      · rintro ⟨b,hb,he⟩
        exact saturated b a hb (Quot.eqvGen_exact he)
      · exact fun ha=>⟨a,ha,rfl⟩
    refine ⟨hopen,saturated,hpre,?_⟩
    rw [←(isQuotientMap_quot_mk (r:=Step P)).isOpen_preimage]
    change IsOpen (qmap P ⁻¹' (qmap P '' CapPatch P f c δ))
    rw [hpre]
    exact hopen
  have chart :
      ∀ (f:T×Fin 4) (c:Fin 4) (e:Equiv.Perm (Fin 4)), e 0=f.2→e 1=c→
      ∀ (δ:ℝ),0<δ→
      IsOpen (qmap P '' CapPatch P f c δ) ∧
        ∃ B:Set HalfSpace,IsOpen B ∧ ∃ h:(qmap P '' CapPatch P f c δ) ≃ₜ B,
          (∀ q:(qmap P '' CapPatch P f c δ),CapMarked P q.val ↔ (h q).val.val 0=0) ∧
          (∀ q:(qmap P '' CapPatch P f c δ),SeamMarked P q.val ↔ (h q).val.val 2=0) := by
    intro f c e he hc δ hδ
    let σ := P.sigma f
    let ep : Equiv.Perm (Fin 4) := e.trans σ
    have hep : ep 0=(P.mate f).2 := by simpa [ep,he] using P.omitted f
    have hepc : ep 1=σ c:=by simp [ep,hc]
    let fold : (Fin 3→ℝ)→Coeff := fun w=>![|w 2|,(3/4:ℝ)-w 0,w 1,(1/4:ℝ)+w 0-|w 2|-w 1]
    let B : Set HalfSpace := {w | |w.val 2|<δ ∧ (∀ k:Fin 4,k≠0→δ<fold w.val k) ∧
      w.val 0<δ ∧ ∀ k:Fin 4,k≠1→fold w.val k<(3/4:ℝ)}
    have hfcont : Continuous fold := by
      apply continuous_pi
      intro k
      fin_cases k <;> dsimp [fold] <;> fun_prop
    have hB : IsOpen B := by
      have hw (j:Fin 3):Continuous (fun w:HalfSpace=>w.val j):=(continuous_apply j).comp continuous_subtype_val
      have hk (k:Fin 4):Continuous (fun w:HalfSpace=>fold w.val k):=
        (continuous_apply k).comp (hfcont.comp continuous_subtype_val)
      have hn:IsOpen {w:HalfSpace|∀ k:Fin 4,k≠0→δ<fold w.val k}:=by
        simp only [setOf_forall]
        apply isOpen_iInter_of_finite
        intro k
        apply isOpen_iInter_of_finite
        intro hk'
        exact isOpen_lt continuous_const (hk k)
      have hu:IsOpen {w:HalfSpace|∀ k:Fin 4,k≠1→fold w.val k<(3/4:ℝ)}:=by
        simp only [setOf_forall]
        apply isOpen_iInter_of_finite
        intro k
        apply isOpen_iInter_of_finite
        intro hk'
        exact isOpen_lt (hk k) continuous_const
      exact (isOpen_lt (hw 2).abs continuous_const).inter
        (hn.inter ((isOpen_lt (hw 0) continuous_const).inter hu))
    have foldValid (w:B):fold w.val.val∈TruncatedSimplex := by
      refine ⟨⟨?_,?_⟩,?_⟩
      · intro k
        by_cases hk:k=0
        · subst k
          exact abs_nonneg _
        · exact le_of_lt (hδ.trans (w.property.2.1 k hk))
      · simp [fold,Fin.sum_univ_succ]
        ring
      · intro k
        by_cases hk:k=1
        · subst k
          have hh:0≤w.val.val 0:=w.val.property
          change (3/4:ℝ)-w.val.val 0≤3/4
          linarith
        · exact le_of_lt (w.property.2.2.2 k hk)
    let fp : B→Point := fun w=>⟨fold w.val.val,foldValid w⟩
    have hfp : Continuous fp :=
      (hfcont.comp (continuous_subtype_val.comp continuous_subtype_val)).subtype_mk _
    have permCont (g:Equiv.Perm (Fin 4)):Continuous (permute g) := by
      apply Continuous.subtype_mk
      apply continuous_pi
      intro k
      exact (continuous_apply (g.symm k)).comp continuous_subtype_val
    have foldCollar (w:B):fp w∈CapCollar 0 1 δ := by
      refine ⟨w.property.1,w.property.2.1,?_,w.property.2.2.2⟩
      change (3/4:ℝ)-δ<3/4-w.val.val 0
      have hh:=w.property.2.2.1
      linarith
    let plus : B→Occurrence T := fun w=>(f.1,permute e (fp w))
    let minus : B→Occurrence T := fun w=>((P.mate f).1,permute ep (fp w))
    have hplus : Continuous plus := continuous_const.prodMk ((permCont e).comp hfp)
    have hminus : Continuous minus := continuous_const.prodMk ((permCont ep).comp hfp)
    have hplusmem (w:B):plus w∈CapPatch P f c δ := by
      apply Or.inl
      exact ⟨rfl,by simpa only [he,hc] using permCollar e (fp w) 0 1 δ (foldCollar w)⟩
    have hminusmem (w:B):minus w∈CapPatch P f c δ := by
      apply Or.inr
      exact ⟨rfl,by simpa only [hep,hepc] using permCollar ep (fp w) 0 1 δ (foldCollar w)⟩
    have seam (w:B) (hs:w.val.val 2=0):qmap P (plus w)=qmap P (minus w) := by
      apply Quot.sound
      refine ⟨f.2,?_,?_⟩
      · change fold w.val.val (e.symm f.2)=0
        rw [←he,e.symm_apply_apply]
        simp [fold,hs]
      · apply Prod.ext
        · rfl
        · apply Subtype.ext
          funext k
          rfl
    let inv : B→RawQuotient P := fun w=>if 0≤w.val.val 2 then qmap P (plus w) else qmap P (minus w)
    have hinv : Continuous inv := by
      apply Continuous.if_le ((continuous_quot_mk).comp hplus) ((continuous_quot_mk).comp hminus)
        continuous_const ((continuous_apply 2).comp (continuous_subtype_val.comp continuous_subtype_val))
      intro w hw
      exact seam w hw.symm
    have hinvmem (w:B):inv w∈qmap P '' CapPatch P f c δ := by
      dsimp [inv]
      split_ifs
      · exact ⟨plus w,hplusmem w,rfl⟩
      · exact ⟨minus w,hminusmem w,rfl⟩
    let up : Set (Occurrence T) := {f.1} ×ˢ CapCollar f.2 c δ
    let down : Set (Occurrence T) := {(P.mate f).1} ×ˢ CapCollar (P.mate f).2 (σ c) δ
    have disjoint (a:Occurrence T) (hu:a∈up) (hd:a∈down):False := by
      have hi:f.2≠(P.mate f).2 := by
        intro hh
        apply P.no_fixed f
        exact Prod.ext (hd.1.symm.trans hu.1) hh.symm
      have hlo:=hd.2.2.1 f.2 hi
      have hhi:=hu.2.1
      linarith
    let cp : Occurrence T→HalfSpace := fun a=>
      ⟨![(3/4:ℝ)-a.2.val (e 1),a.2.val (e 2),a.2.val (e 0)],by
        change 0≤(3/4:ℝ)-a.2.val (e 1)
        have hh:=a.2.property.2 (e 1)
        linarith⟩
    let cm : Occurrence T→HalfSpace := fun a=>
      ⟨![(3/4:ℝ)-a.2.val (ep 1),a.2.val (ep 2),-a.2.val (ep 0)],by
        change 0≤(3/4:ℝ)-a.2.val (ep 1)
        have hh:=a.2.property.2 (ep 1)
        linarith⟩
    have sumFour (x:Point):x.val 0+x.val 1+x.val 2+x.val 3=1 := by
      simpa [Fin.sum_univ_succ,add_assoc] using x.property.1.2
    have permSum (g:Equiv.Perm (Fin 4)) (x:Point):
        x.val (g 0)+x.val (g 1)+x.val (g 2)+x.val (g 3)=1 := by
      have hh : ∑ k:Fin 4,x.val (g k)=1 := by rw [Equiv.sum_comp g,x.property.1.2]
      simpa [Fin.sum_univ_succ,add_assoc] using hh
    have reconstruct (g:Equiv.Perm (Fin 4)) (x:Point):
        (fun k:Fin 4=>x.val (g k))=fold ![(3/4:ℝ)-x.val (g 1),x.val (g 2),x.val (g 0)] := by
      funext k
      have hx:x.val (g 0)≥0:=x.property.1.1 _
      have hh:=permSum g x
      fin_cases k <;> simp [fold,abs_of_nonneg hx] <;> linarith
    have cpB (a:Occurrence T) (ha:a∈up):cp a∈B := by
      have hr:=reconstruct e a.2
      refine ⟨?_,?_,?_,?_⟩
      · simpa [cp,abs_of_nonneg (a.2.property.1.1 _),he] using ha.2.1
      · intro k hk
        rw [←hr]
        apply ha.2.2.1
        exact fun hh=>hk (e.injective (hh.trans he.symm))
      · change (3/4:ℝ)-a.2.val (e 1)<δ
        have hh:=ha.2.2.2.1
        rw [hc]
        linarith
      · intro k hk
        rw [←hr]
        apply ha.2.2.2.2
        exact fun hh=>hk (e.injective (hh.trans hc.symm))
    have cmB (a:Occurrence T) (ha:a∈down):cm a∈B := by
      have hr : (fun k:Fin 4=>a.2.val (ep k))=fold (cm a).val := by
        rw [reconstruct ep a.2]
        simp [fold,cm,abs_of_nonneg (a.2.property.1.1 _)]
      refine ⟨?_,?_,?_,?_⟩
      · simpa [cm,abs_of_nonneg (a.2.property.1.1 _),hep] using ha.2.1
      · intro k hk
        rw [←hr]
        apply ha.2.2.1
        exact fun hh=>hk (ep.injective (hh.trans hep.symm))
      · change (3/4:ℝ)-a.2.val (ep 1)<δ
        have hh:=ha.2.2.2.1
        rw [hepc]
        linarith
      · intro k hk
        rw [←hr]
        apply ha.2.2.2.2
        exact fun hh=>hk (ep.injective (hh.trans hepc.symm))
    have backPlus (a:Occurrence T) (ha:a∈up):plus ⟨cp a,cpB a ha⟩=a := by
      apply Prod.ext ha.1.symm
      apply Subtype.ext
      funext k
      change fold (cp a).val (e.symm k)=a.2.val k
      rw [←reconstruct e a.2]
      simp
    have backMinus (a:Occurrence T) (ha:a∈down):minus ⟨cm a,cmB a ha⟩=a := by
      apply Prod.ext ha.1.symm
      apply Subtype.ext
      funext k
      change fold (cm a).val (ep.symm k)=a.2.val k
      have hr : fold (cm a).val=fold ![(3/4:ℝ)-a.2.val (ep 1),a.2.val (ep 2),a.2.val (ep 0)] := by
        simp [fold,cm,abs_of_nonneg (a.2.property.1.1 _)]
      rw [hr,←reconstruct ep a.2]
      simp
    have cpPlus (w:B):(cp (plus w)).val=![w.val.val 0,w.val.val 1,|w.val.val 2|] := by
      funext k
      fin_cases k <;> simp [cp,plus,permute,fp,fold]
    have cmMinus (w:B):(cm (minus w)).val=![w.val.val 0,w.val.val 1,-|w.val.val 2|] := by
      funext k
      fin_cases k <;> simp [cm,minus,permute,fp,fold]
    have qBackPlus (a:Occurrence T) (ha:a∈up):inv ⟨cp a,cpB a ha⟩=qmap P a := by
      have hs:0≤(cp a).val 2:=a.2.property.1.1 _
      simp only [inv,hs,ite_true,backPlus a ha]
    have qBackMinus (a:Occurrence T) (ha:a∈down):inv ⟨cm a,cmB a ha⟩=qmap P a := by
      by_cases hs:(cm a).val 2<0
      · simp only [inv,not_le_of_gt hs,ite_false,backMinus a ha]
      · have hz:(cm a).val 2=0:=by
          have hh:a.2.val (ep 0)≥0:=a.2.property.1.1 _
          dsimp [cm] at hs ⊢
          linarith
        simp only [inv,le_of_eq hz.symm,ite_true]
        exact (seam ⟨cm a,cmB a ha⟩ hz).trans (congrArg (qmap P) (backMinus a ha))
    have stepPlus (a b:Occurrence T) (ha:a∈up) (hs:Step P a b):
        b∈down ∧ cp a=cm b := by
      obtain ⟨i,hi,rfl⟩:=hs
      have heif:i=f.2:=onlyZero a f.2 c δ hδ ha.2 i hi
      have hf:(a.1,i)=f:=Prod.ext ha.1 heif
      constructor
      · refine ⟨?_,?_⟩
        · change (P.mate (a.1,i)).1=(P.mate f).1
          rw [hf]
        · change permute (P.sigma (a.1,i)) a.2∈CapCollar (P.mate f).2 (σ c) δ
          rw [hf,←P.omitted f]
          exact permCollar _ a.2 f.2 c δ ha.2
      · apply Subtype.ext
        funext k
        have hz:a.2.val (e 0)=0:=by rw [he,←heif];exact hi
        fin_cases k <;> simp [cp,cm,ep,glue,permute,hf,σ,hz]
    have stepMinus (a b:Occurrence T) (ha:a∈down) (hs:Step P a b):
        b∈up ∧ cm a=cp b := by
      obtain ⟨i,hi,rfl⟩:=hs
      have heif:i=(P.mate f).2:=onlyZero a (P.mate f).2 (σ c) δ hδ ha.2 i hi
      have hf:(a.1,i)=P.mate f:=Prod.ext ha.1 heif
      constructor
      · refine ⟨?_,?_⟩
        · change (P.mate (a.1,i)).1=f.1
          rw [hf,P.involutive]
        · change permute (P.sigma (a.1,i)) a.2∈CapCollar f.2 c δ
          rw [hf]
          have hidx:(P.sigma (P.mate f)) (P.mate f).2=f.2:=by
            simpa only [P.involutive f] using P.omitted (P.mate f)
          have hcap:(P.sigma (P.mate f)) (σ c)=c:=by rw [P.inverse];simp [σ]
          rw [←hidx,←hcap]
          exact permCollar _ a.2 _ _ δ ha.2
      · apply Subtype.ext
        funext k
        have hz:a.2.val (ep 0)=0:=by rw [hep,←heif];exact hi
        have hz' : a.2.val (σ (e 0))=0:=hz
        fin_cases k <;> simp [cp,cm,ep,glue,permute,hf,P.inverse,σ,hz']
    let zeroH : HalfSpace := ⟨0,by simp⟩
    let CF : Occurrence T→HalfSpace := fun a=>if a∈up then cp a else if a∈down then cm a else zeroH
    have hCFplus (a:Occurrence T) (ha:a∈up):CF a=cp a := by simp [CF,ha]
    have hCFminus (a:Occurrence T) (ha:a∈down):CF a=cm a := by
      have hu:a∉up:=fun hh=>disjoint a hh ha
      simp [CF,hu,ha]
    have hCFstep (a b:Occurrence T) (hs:Step P a b):CF a=CF b := by
      by_cases hu:a∈up
      · obtain ⟨hd,heq⟩:=stepPlus a b hu hs
        rw [hCFplus a hu,hCFminus b hd]
        exact heq
      · by_cases hd:a∈down
        · obtain ⟨hu',heq⟩:=stepMinus a b hd hs
          rw [hCFminus a hd,hCFplus b hu']
          exact heq
        · have ha:a∉CapPatch P f c δ:=fun h=>h.elim hu hd
          have hb:b∉CapPatch P f c δ:=by
            intro hh
            exact ha ((openpatch f c δ hδ).2.1 b a hh (Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _ hs)))
          have hbu:b∉up:=fun h=>hb (Or.inl h)
          have hbd:b∉down:=fun h=>hb (Or.inr h)
          simp [CF,hu,hd,hbu,hbd]
    let desc : RawQuotient P→HalfSpace := Quot.lift CF hCFstep
    have descRep (a:Occurrence T):desc (qmap P a)=CF a:=rfl
    have descB (q:RawQuotient P) (hq:q∈qmap P '' CapPatch P f c δ):desc q∈B := by
      obtain ⟨a,ha,rfl⟩:=hq
      rw [descRep]
      rcases ha with hu|hd
      · rw [hCFplus a hu]
        exact cpB a hu
      · rw [hCFminus a hd]
        exact cmB a hd
    have descInv (w:B):desc (inv w)=w.val := by
      apply Subtype.ext
      dsimp [inv]
      split_ifs with hs
      · have hu:plus w∈up:=⟨rfl,by simpa only [he,hc] using permCollar e (fp w) 0 1 δ (foldCollar w)⟩
        rw [descRep,hCFplus _ hu]
        rw [cpPlus]
        funext k
        fin_cases k <;> simp [abs_of_nonneg hs]
      · have hd:minus w∈down:=⟨rfl,by simpa only [hep,hepc] using permCollar ep (fp w) 0 1 δ (foldCollar w)⟩
        rw [descRep,hCFminus _ hd,cmMinus]
        funext k
        fin_cases k <;> simp [abs_of_neg (lt_of_not_ge hs)]
    let U : Set (RawQuotient P) := qmap P '' CapPatch P f c δ
    let forward : U→B := fun q=>⟨desc q.val,descB q.val q.property⟩
    let backward : B→U := fun w=>⟨inv w,hinvmem w⟩
    have leftInverse (q:U):backward (forward q)=q := by
      apply Subtype.ext
      obtain ⟨a,ha,heq⟩:=q.property
      change inv (forward q)=q.val
      rcases ha with hu|hd
      · have hw:forward q=⟨cp a,cpB a hu⟩:=by
          apply Subtype.ext
          change desc q.val=cp a
          rw [←heq,descRep,hCFplus a hu]
        rw [hw]
        exact (qBackPlus a hu).trans heq
      · have hw:forward q=⟨cm a,cmB a hd⟩:=by
          apply Subtype.ext
          change desc q.val=cm a
          rw [←heq,descRep,hCFminus a hd]
        rw [hw]
        exact (qBackMinus a hd).trans heq
    have rightInverse (w:B):forward (backward w)=w := by
      apply Subtype.ext
      exact descInv w
    have coordCont (g:Equiv.Perm (Fin 4)) (k:Fin 4):
        Continuous (fun a:Occurrence T=>a.2.val (g k)):=
      (continuous_apply _).comp (continuous_subtype_val.comp continuous_snd)
    have hcp : Continuous cp := by
      apply Continuous.subtype_mk
      apply continuous_pi
      intro k
      fin_cases k <;> dsimp [cp]
      · exact continuous_const.sub (coordCont e 1)
      · exact coordCont e 2
      · exact coordCont e 0
    have hcm : Continuous cm := by
      apply Continuous.subtype_mk
      apply continuous_pi
      intro k
      fin_cases k <;> dsimp [cm]
      · exact continuous_const.sub (coordCont ep 1)
      · exact coordCont ep 2
      · exact (coordCont ep 0).neg
    have hup:IsOpen up:=(isOpen_discrete _).prod (openCollar _ _ δ)
    have hdown:IsOpen down:=(isOpen_discrete _).prod (openCollar _ _ δ)
    have hU:IsOpen U:=(openpatch f c δ hδ).2.2.2
    have hpre:qmap P ⁻¹' U=CapPatch P f c δ:=(openpatch f c δ hδ).2.2.1
    have hCFcont : Continuous (fun a:qmap P ⁻¹' U=>CF a.val) := by
      apply continuous_iff_continuousAt.mpr
      intro a
      have ha:a.val∈CapPatch P f c δ:=hpre ▸ a.property
      rcases ha with hu|hd
      · apply ((hcp.comp continuous_subtype_val).continuousAt).congr_of_eventuallyEq
        filter_upwards [(hup.preimage continuous_subtype_val).mem_nhds hu] with z hz
        exact hCFplus z.val hz
      · apply ((hcm.comp continuous_subtype_val).continuousAt).congr_of_eventuallyEq
        filter_upwards [(hdown.preimage continuous_subtype_val).mem_nhds hd] with z hz
        exact hCFminus z.val hz
    have hforward : Continuous forward := by
      have hq : Topology.IsQuotientMap (U.restrictPreimage (qmap P)):=
        (isQuotientMap_quot_mk).restrictPreimage_isOpen hU
      have hdesccont:Continuous (fun q:U=>desc q.val):=by
        apply hq.continuous_iff.mpr
        exact hCFcont
      exact hdesccont.subtype_mk _
    have hbackward : Continuous backward := hinv.subtype_mk _
    let h : U ≃ₜ B := {
      toFun:=forward
      invFun:=backward
      left_inv:=leftInverse
      right_inv:=rightInverse
      continuous_toFun:=hforward
      continuous_invFun:=hbackward }
    have capActive (a:Occurrence T) (i c:Fin 4) (ha:a.2∈CapCollar i c δ):
        (∃ j,a.2.val j=(3/4:ℝ)) ↔ a.2.val c=(3/4:ℝ):=by
      constructor
      · rintro ⟨j,hj⟩
        by_cases hjc:j=c
        · simpa only [hjc] using hj
        · have hh:=ha.2.2.2 j hjc
          rw [hj] at hh
          exact False.elim (lt_irrefl _ hh)
      · exact fun hh=>⟨c,hh⟩
    have seamActive (a:Occurrence T) (i c:Fin 4) (ha:a.2∈CapCollar i c δ):
        (∃ j,a.2.val j=0) ↔ a.2.val i=0:=by
      constructor
      · rintro ⟨j,hj⟩
        have heq:=onlyZero a i c δ hδ ha j hj
        simpa only [heq] using hj
      · exact fun hh=>⟨i,hh⟩
    have capMark (q:U):CapMarked P q.val ↔ (h q).val.val 0=0:=by
      obtain ⟨a,ha,heq⟩:=q.property
      change CapMarked P q.val ↔ (desc q.val).val 0=0
      rw [←heq,descRep]
      rcases ha with hu|hd
      · rw [hCFplus a hu]
        change (∃ j,a.2.val j=(3/4:ℝ)) ↔ (3/4:ℝ)-a.2.val (e 1)=0
        rw [hc,capActive a _ _ hu.2]
        constructor <;> intro hh <;> linarith
      · rw [hCFminus a hd]
        change (∃ j,a.2.val j=(3/4:ℝ)) ↔ (3/4:ℝ)-a.2.val (ep 1)=0
        rw [hepc,capActive a _ _ hd.2]
        constructor <;> intro hh <;> linarith
    have seamMark (q:U):SeamMarked P q.val ↔ (h q).val.val 2=0:=by
      obtain ⟨a,ha,heq⟩:=q.property
      change SeamMarked P q.val ↔ (desc q.val).val 2=0
      rw [←heq,descRep]
      rcases ha with hu|hd
      · rw [hCFplus a hu]
        change (∃ j,a.2.val j=0) ↔ a.2.val (e 0)=0
        rw [he]
        exact seamActive a _ _ hu.2
      · rw [hCFminus a hd]
        change (∃ j,a.2.val j=0) ↔ -a.2.val (ep 0)=0
        rw [hep,neg_eq_zero]
        exact seamActive a _ _ hd.2
    exact ⟨hU,B,hB,h,capMark,seamMark⟩
  intro a i c hi hcap hpos
  have hic:i≠c:=by
    intro hh
    subst c
    rw [hi] at hcap
    norm_num at hcap
  let e0 : Equiv.Perm (Fin 4) := Equiv.swap 0 i
  have he0:e0 0=i:=by simp [e0]
  let k:Fin 4:=e0.symm c
  have hk:k≠0:=by
    intro hh
    apply hic
    calc i=e0 0:=he0.symm
         _=e0 k:=congrArg e0 hh.symm
         _=c:=e0.apply_symm_apply c
  let e:Equiv.Perm (Fin 4):=(Equiv.swap 1 k).trans e0
  have he:e 0=i:=by
    change e0 (Equiv.swap 1 k 0)=i
    rw [Equiv.swap_apply_of_ne_of_ne (by decide) (Ne.symm hk)]
    exact he0
  have hc:e 1=c:=by simp [e,k]
  have hp (j:Fin 4) (hj:j≠0):0<a.2.val (e j):=by
    apply hpos
    intro hh
    exact hj (e.injective (hh.trans he.symm))
  let m:ℝ:=min (a.2.val (e 1)) (min (a.2.val (e 2)) (a.2.val (e 3)))
  have hm:0<m:=lt_min (hp 1 (by decide)) (lt_min (hp 2 (by decide)) (hp 3 (by decide)))
  let δ:ℝ:=m/2
  have hδ:0<δ:=by dsimp [δ];linarith
  have hmδ:δ<m:=by dsimp [δ];linarith
  have hsmall (j:Fin 4) (hj:j≠i):δ<a.2.val j:=by
    have hz:e.symm j≠0:=by
      intro hh
      apply hj
      calc j=e (e.symm j):=(e.apply_symm_apply j).symm
           _=e 0:=congrArg e hh
           _=i:=he
    have hbound (l:Fin 4) (hl:l≠0):m≤a.2.val (e l):=by
      fin_cases l
      · exact False.elim (hl rfl)
      · exact min_le_left _ _
      · exact (min_le_right _ _).trans (min_le_left _ _)
      · exact (min_le_right _ _).trans (min_le_right _ _)
    have hb:=hbound (e.symm j) hz
    simpa using hmδ.trans_le hb
  have hupper (j:Fin 4) (hj:j≠c):a.2.val j<(3/4:ℝ):=by
    have hle:a.2.val j+a.2.val c≤1:=by
      have hsub:({j,c}:Finset (Fin 4))⊆Finset.univ:=Finset.subset_univ _
      have hh:=Finset.sum_le_sum_of_subset_of_nonneg hsub (fun l _ _=>a.2.property.1.1 l)
      rw [a.2.property.1.2] at hh
      simpa [Finset.sum_insert,hj] using hh
    rw [hcap] at hle
    linarith
  have hcollar:a.2∈CapCollar i c δ:=by
    refine ⟨?_,hsmall,?_,hupper⟩
    · simpa only [hi] using hδ
    · rw [hcap]
      linarith
  let f:T×Fin 4:=(a.1,i)
  obtain ⟨hU,B,hB,hchart⟩:=chart f c e he hc δ hδ
  exact ⟨qmap P '' CapPatch P f c δ,hU,⟨a,Or.inl ⟨rfl,hcollar⟩,rfl⟩,B,hB,hchart⟩


end D5.S3.Geometry.Hyperideal.PairedFaceCharts
