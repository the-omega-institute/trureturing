/- GID: D5/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnRootGraph
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/TypeA/RootGeometry/PartIISLnRootGraph
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual type-A matrix and quotient mathematics for uniform ordered products. -/

import D5.S3.FiniteGroups.NikolovSegal.TypeA.RootGeometry.PartIISLnRootIncidence

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

namespace NikolovSegal.SLnRootAction
variable {n : ℕ}

def RootCompose (a b c : PositiveIndex n) : Prop :=
  (a.val.2=b.val.1 ∧ c.val.1=a.val.1 ∧ c.val.2=b.val.2) ∨
  (b.val.2=a.val.1 ∧ c.val.1=b.val.1 ∧ c.val.2=a.val.2)

def reflectRoot (r : PositiveIndex n) : PositiveIndex n :=
  ⟨(r.val.2.rev,r.val.1.rev),by
    have h := r.property
    change r.val.2.rev.val < r.val.1.rev.val
    simp only [Fin.val_rev]
    omega⟩

theorem reflectRoot_twice (r : PositiveIndex n) : reflectRoot (reflectRoot r) = r := by
  apply Subtype.ext
  simp [reflectRoot]

def simpleRoot (i : Fin (n-1)) : PositiveIndex n :=
  ⟨(⟨i.val,by omega⟩,⟨i.val+1,by omega⟩),by change i.val < i.val+1; omega⟩

def Composite (r : PositiveIndex n) : Prop := r.val.1.val+1 < r.val.2.val

theorem simpleRoot_injective : Function.Injective (simpleRoot (n := n)) := by
  intro i j h
  exact Fin.ext (congrArg (fun r : PositiveIndex n => r.val.1.val) h)

theorem not_composite_iff (r : PositiveIndex n) :
    ¬ Composite r ↔ ∃ i : Fin (n-1), simpleRoot i = r := by
  constructor
  · intro h
    have hij := r.property
    have he : r.val.2.val = r.val.1.val+1 := by dsimp [Composite] at h; omega
    let i : Fin (n-1) := ⟨r.val.1.val,by have hb:=r.val.2.isLt; omega⟩
    refine ⟨i,Subtype.ext (Prod.ext (Fin.ext rfl) (Fin.ext he.symm))⟩
  · rintro ⟨i,rfl⟩
    change ¬ i.val+1 < i.val+1
    exact lt_irrefl _

private theorem path_increasing {m : ℕ} (hm : 2 ≤ m) (f : Fin m → Fin m)
    (hinj : Function.Injective f)
    (hstep : ∀ (i : ℕ) (hi : i+1< m),
      (f ⟨i+1,hi⟩).val = (f ⟨i,by omega⟩).val+1 ∨
      (f ⟨i,by omega⟩).val = (f ⟨i+1,hi⟩).val+1)
    (hstart : (f ⟨1,by omega⟩).val = (f ⟨0,by omega⟩).val+1) : ∀ i, f i = i := by
  have hlin : ∀ (i : ℕ) (hi : i< m), (f ⟨i,hi⟩).val = (f ⟨0,by omega⟩).val+i := by
    intro i
    induction i using Nat.strong_induction_on with
    | h i ih =>
      intro hi
      by_cases h0 : i=0
      · subst i; simp
      by_cases h1 : i=1
      · subst i; exact hstart
      have hge : 2 ≤ i := by omega
      have hp : i-1< i := by omega
      have hpp : i-2< i := by omega
      have hfp := ih (i-1) hp (by omega)
      have hfpp := ih (i-2) hpp (by omega)
      have hs := hstep (i-1) (by omega)
      have hs' : (f ⟨i,hi⟩).val = (f ⟨i-1,by omega⟩).val+1 ∨
          (f ⟨i-1,by omega⟩).val = (f ⟨i,hi⟩).val+1 := by
        simpa only [Nat.sub_add_cancel (by omega : 1 ≤ i)] using hs
      rcases hs' with hs|hs
      · omega
      · have he : f ⟨i,hi⟩ = f ⟨i-2,by omega⟩ := Fin.ext (by omega)
        have hi' := congrArg Fin.val (hinj he)
        change i=i-2 at hi'
        omega
  have he := hlin (m-1) (by omega)
  have hb := (f ⟨m-1,by omega⟩).isLt
  have hz : (f ⟨0,by omega⟩).val=0 := by omega
  intro i
  apply Fin.ext
  rw [hlin i.val i.isLt,hz,zero_add]

/-- An injective traversal of the FULL finite path is identity or reversal.
This proves the combinatorial restriction, rather than assuming a graph law. -/
theorem path_embedding_identity_or_rev {m : ℕ} (hm : 2 ≤ m) (f : Fin m → Fin m)
    (hinj : Function.Injective f)
    (hstep : ∀ (i : ℕ) (hi : i+1< m),
      (f ⟨i+1,hi⟩).val = (f ⟨i,by omega⟩).val+1 ∨
      (f ⟨i,by omega⟩).val = (f ⟨i+1,hi⟩).val+1) :
    (∀ i, f i=i) ∨ (∀ i, f i=i.rev) := by
  rcases hstep 0 (by omega) with hs|hs
  · exact Or.inl (path_increasing hm f hinj hstep hs)
  · have hs0 : (f ⟨0,by omega⟩).val = (f ⟨1,by omega⟩).val+1 := by simpa using hs
    let g : Fin m → Fin m := fun i => (f i).rev
    have hgi : Function.Injective g := fun a b h => hinj (Fin.rev_inj.mp h)
    have hgstep : ∀ (i : ℕ) (hi : i+1< m),
        (g ⟨i+1,hi⟩).val = (g ⟨i,by omega⟩).val+1 ∨
        (g ⟨i,by omega⟩).val = (g ⟨i+1,hi⟩).val+1 := by
      intro i hi
      have hb0 := (f ⟨i,by omega⟩).isLt
      have hb1 := (f ⟨i+1,hi⟩).isLt
      simp only [g,Fin.val_rev]
      rcases hstep i hi with h|h
      · right; omega
      · left; omega
    have hgstart : (g ⟨1,by omega⟩).val = (g ⟨0,by omega⟩).val+1 := by
      have hb0 := (f ⟨0,by omega⟩).isLt
      have hb1 := (f ⟨1,by omega⟩).isLt
      simp only [g,Fin.val_rev]
      omega
    have hg := path_increasing hm g hgi hgstep hgstart
    right
    intro i
    have he := congrArg Fin.val (hg i)
    apply Fin.ext
    simp only [g,Fin.val_rev] at he ⊢
    have hb := (f i).isLt
    omega

theorem reflect_compose {a b c : PositiveIndex n} (h : RootCompose a b c) :
    RootCompose (reflectRoot a) (reflectRoot b) (reflectRoot c) := by
  rcases h with ⟨h1,h2,h3⟩|⟨h1,h2,h3⟩
  · right
    exact ⟨congrArg Fin.rev h1.symm,congrArg Fin.rev h3,congrArg Fin.rev h2⟩
  · left
    exact ⟨congrArg Fin.rev h1.symm,congrArg Fin.rev h3,congrArg Fin.rev h2⟩

private theorem fixed_of_simple_fixed (sigma : PositiveIndex n → PositiveIndex n)
    (hinc : ∀ (i j k : Fin n) (hij : i< j) (hjk : j< k),
      RootCompose (sigma ⟨(i,j),hij⟩) (sigma ⟨(j,k),hjk⟩) (sigma ⟨(i,k),hij.trans hjk⟩))
    (hsimple : ∀ i, sigma (simpleRoot i)=simpleRoot i) : ∀ r, sigma r=r := by
  have hfix : ∀ d : ℕ, ∀ (i j : Fin n) (hij : i< j), j.val-i.val=d → sigma ⟨(i,j),hij⟩=⟨(i,j),hij⟩ := by
    intro d
    induction d using Nat.strong_induction_on with
    | h d ih =>
      intro i j hij hd
      by_cases hadj : j.val=i.val+1
      · let a : Fin (n-1) := ⟨i.val,by have hj:=j.isLt; omega⟩
        have he : simpleRoot a = (⟨(i,j),hij⟩ : PositiveIndex n) :=
          Subtype.ext (Prod.ext (Fin.ext rfl) (Fin.ext hadj.symm))
        rw [← he]
        exact hsimple a
      · let k : Fin n := ⟨j.val-1,by have hj:=j.isLt; omega⟩
        have hik : i< k := by change i.val< j.val-1; have hi:=hij; change i.val< j.val at hi; omega
        have hkj : k< j := by change j.val-1< j.val; have hi:=hij; change i.val< j.val at hi; omega
        have hshort : k.val-i.val< d := by dsimp [k]; have hi:=hij; change i.val< j.val at hi; omega
        have h1 := ih (k.val-i.val) hshort i k hik rfl
        let a : Fin (n-1) := ⟨k.val,by dsimp [k]; have hj:=j.isLt; omega⟩
        have he : simpleRoot a = (⟨(k,j),hkj⟩ : PositiveIndex n) :=
          Subtype.ext (Prod.ext (Fin.ext rfl) (Fin.ext (by
            change k.val+1=j.val
            dsimp [k]
            have hi:=hij
            change i.val< j.val at hi
            omega)))
        have h2 : sigma ⟨(k,j),hkj⟩=⟨(k,j),hkj⟩ := by rw [← he]; exact hsimple a
        have hc := hinc i k j hik hkj
        rw [h1,h2] at hc
        rcases hc with ⟨_,hc1,hc2⟩|⟨hc1,_,_⟩
        · exact Subtype.ext (Prod.ext hc1 hc2)
        · exact ((ne_of_lt hij).symm hc1).elim
  intro r
  exact hfix _ r.val.1 r.val.2 r.property rfl

/-- A permutation of ALL positive A-type roots preserving genuine root
composition is forced to be identity or the unique Dynkin reflection. -/
theorem root_permutation_identity_or_reflection (hn : 2 < n)
    (sigma : Equiv.Perm (PositiveIndex n))
    (hinc : ∀ (i j k : Fin n) (hij : i< j) (hjk : j< k),
      RootCompose (sigma ⟨(i,j),hij⟩) (sigma ⟨(j,k),hjk⟩) (sigma ⟨(i,k),hij.trans hjk⟩)) :
    (∀ r, sigma r=r) ∨ (∀ r, sigma r=reflectRoot r) := by
  classical
  have hcomp : ∀ r, Composite r → Composite (sigma r) := by
    intro r hr
    let k : Fin n := ⟨r.val.1.val+1,by have hb:=r.val.2.isLt; dsimp [Composite] at hr; omega⟩
    have h1 : r.val.1< k := by change r.val.1.val< r.val.1.val+1; omega
    have h2 : k< r.val.2 := hr
    have hc : RootCompose (sigma ⟨(r.val.1,k),h1⟩) (sigma ⟨(k,r.val.2),h2⟩) (sigma r) :=
      hinc r.val.1 k r.val.2 h1 h2
    rcases hc with ⟨hc1,hc2,hc3⟩|⟨hc1,hc2,hc3⟩
    all_goals
      have ha := (sigma ⟨(r.val.1,k),h1⟩).property
      have hb := (sigma ⟨(k,r.val.2),h2⟩).property
      change (sigma r).val.1.val+1< (sigma r).val.2.val
      have hv1 := congrArg Fin.val hc1
      have hv2 := congrArg Fin.val hc2
      have hv3 := congrArg Fin.val hc3
      change _<_ at ha hb
      omega
  let S : Finset (PositiveIndex n) := Finset.univ.filter Composite
  have hs : S.image sigma ⊆ S := by
    intro r hr
    obtain ⟨s,hs,rfl⟩ := Finset.mem_image.mp hr
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,hcomp s (Finset.mem_filter.mp hs).2⟩
  have he : S.image sigma = S := Finset.eq_of_subset_of_card_le hs
    (by rw [Finset.card_image_of_injective _ sigma.injective])
  have hback : ∀ r, Composite (sigma r) → Composite r := by
    intro r hr
    have hm : sigma r ∈ S.image sigma := he.symm ▸ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hr⟩)
    obtain ⟨s,hs,hσ⟩ := Finset.mem_image.mp hm
    have hsr : s=r := sigma.injective hσ
    exact hsr ▸ (Finset.mem_filter.mp hs).2
  have hsimple : ∀ i : Fin (n-1), ∃ j, simpleRoot j = sigma (simpleRoot i) := by
    intro i
    apply (not_composite_iff _).mp
    intro h
    exact (not_composite_iff (simpleRoot i)).mpr ⟨i,rfl⟩ (hback _ h)
  choose f hf using hsimple
  have hfi : Function.Injective f := by
    intro i j h
    apply simpleRoot_injective
    apply sigma.injective
    rw [← hf i,← hf j,h]
  have hstep : ∀ (i : ℕ) (hi : i+1< n-1),
      (f ⟨i+1,hi⟩).val = (f ⟨i,by omega⟩).val+1 ∨
      (f ⟨i,by omega⟩).val = (f ⟨i+1,hi⟩).val+1 := by
    intro i hi
    let a : Fin n := ⟨i,by omega⟩
    let b : Fin n := ⟨i+1,by omega⟩
    let c : Fin n := ⟨i+2,by omega⟩
    have hab : a< b := by change i< i+1; omega
    have hbc : b< c := by change i+1< i+2; omega
    have hc := hinc a b c hab hbc
    have h1 : sigma ⟨(a,b),hab⟩ = simpleRoot (f ⟨i,by omega⟩) := (hf ⟨i,by omega⟩).symm
    have h2 : sigma ⟨(b,c),hbc⟩ = simpleRoot (f ⟨i+1,hi⟩) := (hf ⟨i+1,hi⟩).symm
    rw [h1,h2] at hc
    rcases hc with ⟨h,_,_⟩|⟨h,_,_⟩
    · left; exact (congrArg Fin.val h).symm
    · right; exact (congrArg Fin.val h).symm
  rcases path_embedding_identity_or_rev (by omega : 2 ≤ n-1) f hfi hstep with hid|hrev
  · left
    apply fixed_of_simple_fixed sigma hinc
    intro i
    rw [← hf i,hid i]
  · right
    let tau : PositiveIndex n → PositiveIndex n := fun r => reflectRoot (sigma r)
    have htinc : ∀ (i j k : Fin n) (hij : i< j) (hjk : j< k),
        RootCompose (tau ⟨(i,j),hij⟩) (tau ⟨(j,k),hjk⟩) (tau ⟨(i,k),hij.trans hjk⟩) :=
      fun i j k hij hjk => reflect_compose (hinc i j k hij hjk)
    have hts : ∀ i, tau (simpleRoot i)=simpleRoot i := by
      intro i
      change reflectRoot (sigma (simpleRoot i))=simpleRoot i
      rw [← hf i,hrev i]
      apply Subtype.ext
      apply Prod.ext <;> apply Fin.ext
      all_goals simp only [reflectRoot,simpleRoot,Fin.val_rev]; have hb:=i.isLt; omega
    have ht := fixed_of_simple_fixed tau htinc hts
    intro r
    have he := congrArg reflectRoot (ht r)
    simpa only [tau,reflectRoot_twice] using he

end NikolovSegal.SLnRootAction
