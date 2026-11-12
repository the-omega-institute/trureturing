/- GID: D5/S3/Combinatorics/Orthogonality/NineteenColorObstruction
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Orthogonality/NineteenColorObstruction
   mirror-E: none(waiver:kernel-checked-refutation)
   anchors: []
   utility: kind=certified-instance; basis=refutes=gid:D5/S3/Combinatorics/Orthogonality/NineteenColorObstruction.claim; result=D5/S3/Combinatorics/Orthogonality/NineteenColorObstruction.result; claim=D5/S3/Combinatorics/Orthogonality/NineteenColorObstruction.claim
   digest: The complete written nineteen-color obstruction on the original deleted line graph. -/

import Mathlib.Combinatorics.SimpleGraph.Coloring.Vertex
import D5.S3.Combinatorics.Orthogonality.SevenBitCapacity
import D5.S3.Combinatorics.Orthogonality.PartialSpreadHoles
import D5.S3.Combinatorics.Orthogonality.SevenBitParity

/-! This implements the original quadratic-parity and universal partial-spread
argument on the entire126-line graph. Exactn7 and a nineteen-color witness
remain open. No paused characteristic-class exclusions are executed. -/
set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0
noncomputable section
namespace D5.S3.Combinatorics.Orthogonality.NineteenColorObstruction
open SevenBitGeometry SevenBitParity

private def D : Finset Vector := deleted.toFinset
private theorem mem_D (v : Vector) : v ∈ D ↔ v ≠ 0 ∧ v ≠ 127 := by simp [D,deleted]
private theorem D_card : D.card = 126 := by decide +kernel
private theorem z_odd : ¬ even (127 : Vector) := by decide +kernel

private theorem even_mem_D (u : Vector) (hu : u ∈ evenPoints) : u ∈ D := by
  have hh := Finset.mem_filter.mp hu
  apply (mem_D u).mpr
  refine ⟨hh.2.1,?_⟩
  intro h
  subst u
  exact z_odd hh.2.2

private def ProperOn (c : Vector → Fin 18) : Prop :=
  ∀ u ∈ D, ∀ v ∈ D, u ≠ v → dot u v = 0 → c u ≠ c v

private def colorClass (c : Vector → Fin 18) (i : Fin 18) : Finset Vector :=
  D.filter (fun v => c v = i)
private def evenCount (c : Vector → Fin 18) (i : Fin 18) : ℕ :=
  (evenPart (colorClass c i)).card
private def A (c : Vector → Fin 18) : Finset (Fin 18) :=
  Finset.univ.filter (fun i => evenCount c i = 7)
private def B (c : Vector → Fin 18) : Finset (Fin 18) :=
  Finset.univ.filter (fun i => evenCount c i = 6)
private def Q (c : Vector → Fin 18) : Finset (Fin 18) :=
  Finset.univ.filter (fun i => evenCount c i = 0)

private theorem class_property (c : Vector → Fin 18) (hc : ProperOn c) (i : Fin 18) :
    ClassProperty (colorClass c i) := by
  apply SevenBitCapacity.class_property
  · intro v hv
    exact (mem_D v).mp (Finset.mem_filter.mp hv).1
  · intro u hu v hv huv hd
    have h1 := Finset.mem_filter.mp hu
    have h2 := Finset.mem_filter.mp hv
    exact hc u h1.1 v h2.1 huv hd (h1.2.trans h2.2.symm)

private theorem sum_class_cards (c : Vector → Fin 18) :
    ∑ i : Fin 18, (colorClass c i).card = 126 := by
  have h := Finset.card_eq_sum_card_fiberwise (s := D) (t := Finset.univ) (f := c)
    (fun _ _ => Finset.mem_univ _)
  simpa only [colorClass,D_card] using h.symm

private theorem saturated (c : Vector → Fin 18) (hc : ProperOn c) (i : Fin 18) :
    (colorClass c i).card = 7 := by
  have hsmall (j : Fin 18) : (colorClass c j).card ≤ 7 := (class_property c hc j).1
  have hs := sum_class_cards c
  have he := Finset.sum_erase_add (Finset.univ : Finset (Fin 18))
    (fun j => (colorClass c j).card) (Finset.mem_univ i)
  have hr : ∑ j ∈ (Finset.univ : Finset (Fin 18)).erase i,
      (colorClass c j).card ≤ 119 := by
    calc
      _ ≤ ∑ j ∈ (Finset.univ : Finset (Fin 18)).erase i, 7 :=
        Finset.sum_le_sum (fun j _ => hsmall j)
      _ = 119 := by simp
  have hi := hsmall i
  omega

private theorem class_types (c : Vector → Fin 18) (hc : ProperOn c) (i : Fin 18) :
    evenCount c i = 7 ∨ evenCount c i = 6 ∨ evenCount c i = 0 := by
  rcases (class_property c hc i).2 (saturated c hc i) with ⟨h,_⟩ | h | ⟨h,_⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

private theorem even_fiber (c : Vector → Fin 18) (i : Fin 18) :
    evenPart (colorClass c i) = evenPoints.filter (fun v => c v = i) := by
  ext v
  by_cases he : even v
  · have hz : v ≠ 127 := by
      intro h
      subst v
      exact z_odd he
    simp [evenPart,colorClass,D,deleted,evenPoints,he,hz,and_assoc,and_comm,and_left_comm]
  · simp [evenPart,colorClass,evenPoints,he]

private theorem sum_even_counts (c : Vector → Fin 18) :
    ∑ i : Fin 18, evenCount c i = 63 := by
  have h := Finset.card_eq_sum_card_fiberwise (s := evenPoints)
    (t := Finset.univ) (f := c) (fun _ _ => Finset.mem_univ _)
  simpa only [evenCount,even_fiber,even_card] using h.symm

private theorem label_counts (c : Vector → Fin 18) (hc : ProperOn c) :
    (A c).card + (B c).card + (Q c).card = 18 ∧
    7 * (A c).card + 6 * (B c).card = 63 := by
  have hp (i : Fin 18) :
      (if evenCount c i = 7 then 1 else 0) +
      (if evenCount c i = 6 then 1 else 0) +
      (if evenCount c i = 0 then 1 else 0) = 1 := by
    rcases class_types c hc i with h | h | h <;> simp [h]
  have hs := Finset.sum_congr (s₁ := Finset.univ) (s₂ := Finset.univ) rfl
    (fun i _ => hp i)
  have hfirst : (A c).card + (B c).card + (Q c).card = 18 := by
    simpa [Finset.sum_add_distrib,A,B,Q] using hs
  have hv (i : Fin 18) : evenCount c i =
      7 * (if evenCount c i = 7 then 1 else 0) +
      6 * (if evenCount c i = 6 then 1 else 0) := by
    rcases class_types c hc i with h | h | h <;> simp [h]
  have he : (∑ i : Fin 18, evenCount c i) = 7 * (A c).card + 6 * (B c).card := by
    calc
      _ = ∑ i : Fin 18, (7 * (if evenCount c i = 7 then 1 else 0) +
          6 * (if evenCount c i = 6 then 1 else 0)) :=
        Finset.sum_congr rfl (fun i _ => hv i)
      _ = _ := by
        rw [Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum]
        simp [A,B]
  exact ⟨hfirst,he.symm.trans (sum_even_counts c)⟩

private theorem two_types (c : Vector → Fin 18) (hc : ProperOn c) :
    ((A c).card = 9 ∧ (B c).card = 0 ∧ (Q c).card = 9) ∨
    ((A c).card = 3 ∧ (B c).card = 7 ∧ (Q c).card = 8) := by
  have h := label_counts c hc
  omega

private def qClass (c : Vector → Fin 18) (i : Fin 18) : ℕ :=
  ∑ v ∈ evenPart (colorClass c i), quadratic v

private theorem sum_qClass (c : Vector → Fin 18) : ∑ i : Fin 18, qClass c i = 28 := by
  have h := Finset.sum_fiberwise evenPoints c quadratic
  simpa only [qClass,even_fiber,quadratic_total] using h

private theorem exclude_nine (c : Vector → Fin 18) (hc : ProperOn c)
    (hA : (A c).card = 9) (hB : (B c).card = 0) : False := by
  have hBe : B c = ∅ := Finset.card_eq_zero.mp hB
  have hm (i : Fin 18) : qClass c i % 2 = if evenCount c i = 7 then 1 else 0 := by
    rcases (class_property c hc i).2 (saturated c hc i) with ⟨h,hq⟩ | h | ⟨h,_⟩
    · change evenCount c i = 7 at h
      simpa only [qClass,if_pos h] using hq
    · have hi : i ∈ B c := Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩
      rw [hBe] at hi
      exact (Finset.notMem_empty _ hi).elim
    · have he : evenPart (colorClass c i) = ∅ := Finset.card_eq_zero.mp h
      simp [qClass,he,show evenCount c i = 0 from h]
  have h := Finset.sum_nat_mod (Finset.univ : Finset (Fin 18)) 2 (qClass c)
  rw [sum_qClass] at h
  simp_rw [hm] at h
  have ha : (∑ i : Fin 18, if evenCount c i = 7 then 1 else 0) = (A c).card := by
    simp [A]
  rw [ha,hA] at h
  norm_num at h

private theorem oddPoint_involutive : Function.Involutive oddPoint := by
  change ∀ v : Vector, oddPoint (oddPoint v) = v
  decide +kernel
private theorem oddPoint_injective : Function.Injective oddPoint :=
  oddPoint_involutive.injective

private theorem pure_odd_data (c : Vector → Fin 18) (hc : ProperOn c)
    (i : Fin 18) (hi : i ∈ Q c) : LagrangianData (oddPoints (colorClass c i)) := by
  have hz : evenCount c i = 0 := (Finset.mem_filter.mp hi).2
  rcases (class_property c hc i).2 (saturated c hc i) with ⟨h,_⟩ | h | ⟨_,h⟩
  · change evenCount c i = 7 at h
    omega
  · change evenCount c i = 6 at h
    omega
  · exact h

private theorem odd_fiber (c : Vector → Fin 18) (i : Fin 18)
    (e : Vector) (he : e ∈ evenPoints) :
    e ∈ oddPoints (colorClass c i) ↔ c (oddPoint e) = i := by
  have hd := oddPoint_domain e he
  constructor
  · intro h
    obtain ⟨v,hv,hve⟩ := Finset.mem_image.mp h
    have hv' := Finset.mem_filter.mp hv
    have hi := (Finset.mem_filter.mp hv'.1).2
    have hve' : v = oddPoint e := by
      rw [← hve,oddPoint_involutive v]
    simpa [hve'] using hi
  · intro hi
    apply Finset.mem_image.mpr
    refine ⟨oddPoint e,?_,oddPoint_involutive e⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_filter.mpr ⟨(mem_D _).mpr ⟨hd.1,hd.2.1⟩,hi⟩,hd.2.2⟩

private theorem odd_disjoint (c : Vector → Fin 18) (i j : Fin 18) (hij : i ≠ j) :
    Disjoint (oddPoints (colorClass c i)) (oddPoints (colorClass c j)) := by
  apply Finset.disjoint_left.mpr
  intro e hei hej
  obtain ⟨u,hu,hue⟩ := Finset.mem_image.mp hei
  obtain ⟨v,hv,hve⟩ := Finset.mem_image.mp hej
  have huv : u = v := oddPoint_involutive.injective (hue.trans hve.symm)
  have hi := (Finset.mem_filter.mp (Finset.mem_filter.mp hu).1).2
  have hj := (Finset.mem_filter.mp (Finset.mem_filter.mp hv).1).2
  exact hij (hi.symm.trans ((congrArg c huv).trans hj))

private theorem exclude_eight (c : Vector → Fin 18) (hc : ProperOn c)
    (hA : (A c).card = 3) (hQ : (Q c).card = 8) : False := by
  let f : Fin 8 ≃ Q c := (Finset.equivFinOfCardEq hQ).symm
  let L : Fin 8 → Finset Vector := fun i => oddPoints (colorClass c (f i).val)
  have hdata (i : Fin 8) : LagrangianData (L i) := pure_odd_data c hc _ (f i).property
  have hh := PartialSpreadHoles.result evenPoints (fun e v => dot e v = 0) L
    even_card (fun i => (hdata i).1) (fun i => (hdata i).2.1)
    (fun i j hij => odd_disjoint c _ _ (by
      intro h
      exact hij (f.injective (Subtype.ext h))))
    hyperplane_card (fun e he i => (hdata i).2.2.2.2 e he)
  let R := PartialSpreadHoles.holes evenPoints L
  have hR : R.card = 7 := hh.1
  have horth : ∀ x ∈ R, ∀ y ∈ R, dot x y = 0 := hh.2
  have hE {x : Vector} (hx : x ∈ R) : x ∈ evenPoints := (Finset.mem_sdiff.mp hx).1
  have hAcolor {x : Vector} (hx : x ∈ R) : c x ∈ A c := by
    have hxd : x ∈ D := even_mem_D x (hE hx)
    have he : even x := (Finset.mem_filter.mp (hE hx)).2.2
    have hcl : x ∈ colorClass c (c x) := Finset.mem_filter.mpr ⟨hxd,rfl⟩
    have hm : x ∈ evenPart (colorClass c (c x)) := Finset.mem_filter.mpr ⟨hcl,he⟩
    have hn : evenCount c (c x) ≠ 0 := by
      intro hz
      exact Finset.card_ne_zero.mpr ⟨x,hm⟩ hz
    rcases class_types c hc (c x) with ha | hb | hq
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha⟩
    · have hsize := saturated c hc (c x)
      have hod : ∃ y ∈ colorClass c (c x), ¬ even y := by
        by_contra ho
        have hall : ∀ y ∈ colorClass c (c x), even y := by
          intro y hy
          by_contra hn
          exact ho ⟨y,hy,hn⟩
        have heq : evenPart (colorClass c (c x)) = colorClass c (c x) :=
          Finset.filter_eq_self.mpr hall
        have hsz : evenCount c (c x) = 7 := by simpa [evenCount,heq] using hsize
        omega
      obtain ⟨y,hy,hyo⟩ := hod
      have hyn : y ≠ x := by intro h; exact hyo (h ▸ he)
      have hdy := (Finset.mem_filter.mp hy).1
      have hey : oddPoint y ∈ evenPoints := by
        have hde := (mem_D y).mp hdy
        have hz : oddPoint y ≠ 0 := by
          intro hz
          have hyz : y = 127 := by
            have hz' := congrArg oddPoint hz
            have hz0 : oddPoint 0 = 127 := by decide +kernel
            simpa only [oddPoint_involutive y,hz0] using hz'
          exact hde.2 hyz
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hz,(oddPoint_parity y).mpr hyo⟩
      have hyR : oddPoint y ∈ R := by
        apply Finset.mem_sdiff.mpr
        refine ⟨hey,?_⟩
        intro hu
        obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hu
        have hcolor := (odd_fiber c _ _ hey).mp hi
        rw [oddPoint_involutive] at hcolor
        have hcy : c y = c x := (Finset.mem_filter.mp hy).2
        have hQx : c x ∈ Q c := by
          rw [← hcy,hcolor]
          exact (f i).property
        have he0 := (Finset.mem_filter.mp hQx).2
        omega
      have hdxy : dot x y = 0 := by
        have h := horth x hx (oddPoint y) hyR
        rwa [dot_oddPoint x (hE hx) y] at h
      exact (hc x hxd y hdy hyn.symm hdxy (Finset.mem_filter.mp hy).2.symm).elim
    · exact (hn hq).elim
  have hinj : Set.InjOn c (R : Set Vector) := by
    intro x hx y hy heq
    by_contra hxy
    exact hc x (even_mem_D x (hE hx)) y (even_mem_D y (hE hy)) hxy
      (horth x hx y hy) heq
  have himg : R.image c ⊆ A c := by
    intro i hi
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hi
    exact hAcolor hx
  have hle := Finset.card_le_card himg
  rw [Finset.card_image_of_injOn hinj,hR,hA] at hle
  omega

/-- The exact full deleted graph cannot be colored with eighteen labels. -/
private theorem no_eighteen_deleted : ¬ deletedGraph.Colorable 18 := by
  rintro ⟨f⟩
  let c : Vector → Fin 18 := fun v => if h : v ∈ D then f ⟨⟨v,((mem_D v).mp h).1⟩,((mem_D v).mp h).2⟩ else 0
  have hc : ProperOn c := by
    intro u hu v hv huv hdot
    have ha : deletedGraph.Adj ⟨⟨u,((mem_D u).mp hu).1⟩,((mem_D u).mp hu).2⟩
        ⟨⟨v,((mem_D v).mp hv).1⟩,((mem_D v).mp hv).2⟩ := ⟨by
          intro h
          exact huv (congrArg (fun x : LineVertex => x.val) h),hdot⟩
    have hne := f.valid ha
    simpa only [c,dif_pos hu,dif_pos hv] using hne
  rcases two_types c hc with ⟨ha,hb,_⟩ | ⟨ha,_,hq⟩
  · exact exclude_nine c hc ha hb
  · exact exclude_eight c hc ha hq

/-- The same actual line/subspace objects as the manuscript, including the
entire nonzero-Submodule graph and its characteristic-line deletion. -/
def claim : Prop := deletedGraph.Colorable 18 ∨
  (BinaryLineGraph.lineGraph 7).Colorable 18 ∨
  (NikandishClique.orthogonalityGraph 7).Colorable 18

/-- All three original graphs require at least nineteen colors. -/
theorem result : ¬ claim := by
  intro h
  let d : deletedGraph →g graph := ⟨Subtype.val,fun h => h⟩
  let l : deletedGraph →g BinaryLineGraph.lineGraph 7 := actualLineGraphIso.toHom.comp d
  let a : deletedGraph →g NikandishClique.orthogonalityGraph 7 :=
    { toFun := fun x => (l x).val
      map_rel' := fun h => l.map_rel h }
  rcases h with h | h | h
  · exact no_eighteen_deleted h
  · exact no_eighteen_deleted (h.of_hom l)
  · exact no_eighteen_deleted (h.of_hom a)

#print axioms result
end D5.S3.Combinatorics.Orthogonality.NineteenColorObstruction
