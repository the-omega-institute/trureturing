/- GID: D5/S3/Combinatorics/Circle/FourNegative/AscendingD2/Schedule
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/AscendingD2/Schedule
   mirror-E: none(waiver:private-consumed-physical-schedule)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Three shifted library masks and four physical negative labels control every prefix. -/
import D5.S3.Combinatorics.Circle.FourNegative.AscendingD2.Paired
import D5.S3.Combinatorics.Circle.ThreeNegativeMinimumTwoJointLift

/-! Physical supports are the existing three-ladder supports translated by two. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.AscendingD2
open SourceWidth PeriodicShortening RunFirstEarTransport
open scoped BigOperators
open private Table Table.u Table.un Table.v Table.vn Table.w Table.wn Table.x Table.xn
  Table.nu Table.nun Table.nv Table.nvn Table.nw Table.nwn Table.nx Table.nxn
  from D5.S3.Combinatorics.Circle.FourNegative.AscendingD2.Paired
open private PhysicalMask support support_good support_sum support_disjoint
  from D5.S3.Combinatorics.Circle.ThreeNegativeMinimumTwoJointLift
open private positive_block_strip from D5.S3.Combinatorics.Circle.ThreeBitSource

private abbrev Mask := PhysicalMask
private def shiftedSupport (a b c : ℕ) (m : Mask a b c) : Finset ℕ :=
  (support a b c m).image (fun i => 2+i)

private theorem shifted_good (a b c : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (m : Mask a b c) (i : ℕ) (hi : i ∈ shiftedSupport a b c m) :
    i < a+b+c+2 ∧ i ≠ a+b+c+1 ∧ i ≠ c+b+1 ∧ i ≠ c+1 ∧ i ≠ 1 := by
  obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hi
  have h := support_good a b c ha hb hc m j hj
  omega

private theorem shifted_sum (a b c : ℕ) (m : Mask a b c) (f : ℕ → ℤ)
    (V W X : ℤ)
    (hv : ∀ i<c-1, f (2+i)=(2 : ℤ)^i*V)
    (hw : ∀ i<b-1, f (c+2+i)=(2 : ℤ)^i*W)
    (hx : ∀ i<a-1, f (c+b+2+i)=(2 : ℤ)^i*X) :
    ((shiftedSupport a b c m).toList.map f).sum =
      (m.1.val : ℤ)*V+m.2.1.val*W+m.2.2.val*X := by
  have hs := support_sum a b c m (fun i => f (2+i)) V W X hv
    (by intro i hi; simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hw i hi)
    (by intro i hi; simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hx i hi)
  have sum_toList (S : Finset ℕ) (v : ℕ → ℤ) : (S.toList.map v).sum = ∑ i ∈ S, v i := by
    change ((S.toList : Multiset ℕ).map v).sum = _
    rw [Finset.coe_toList]; rfl
  rw [sum_toList,shiftedSupport,Finset.sum_image] <;> try omega
  simpa only [sum_toList] using hs

private theorem shifted_disjoint (a b c : ℕ) (p q : Mask a b c)
    (hv : Disjoint p.1.val.bitIndices.toFinset q.1.val.bitIndices.toFinset)
    (hw : Disjoint p.2.1.val.bitIndices.toFinset q.2.1.val.bitIndices.toFinset)
    (hx : Disjoint p.2.2.val.bitIndices.toFinset q.2.2.val.bitIndices.toFinset) :
    Disjoint (shiftedSupport a b c p) (shiftedSupport a b c q) := by
  have hd := support_disjoint a b c p q hv hw hx
  apply Finset.disjoint_left.mpr
  intro i hi hj
  obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp hi
  obtain ⟨l,hl,he⟩ := Finset.mem_image.mp hj
  have : l=j := by omega
  subst l
  exact Finset.disjoint_left.mp hd hj hl

private theorem table_positive (a b c : ℕ) (R T Z : ℤ) (f g : ℕ → ℤ)
    (hR : 0<R) (hT : 0<T) (hZ : 0<Z) (tab : Table a b c R T Z f g)
    (i : ℕ) (hi : i<a+b+c+2 ∧ i ≠ a+b+c+1 ∧ i ≠ c+b+1 ∧ i ≠ c+1 ∧ i ≠ 1) :
    0 ≤ f i ∧ 0 ≤ g i := by
  by_cases h0 : i=0
  · subst i; rw [tab.u,tab.un]; constructor <;> positivity
  by_cases hv : i<c+1
  · have he : i=2+(i-2) := by omega
    rw [he,tab.v _ (by omega),tab.vn _ (by omega)]
    constructor <;> positivity
  by_cases hw : i<c+b+1
  · have he : i=c+2+(i-(c+2)) := by omega
    rw [he,tab.w _ (by omega),tab.wn _ (by omega)]
    constructor <;> positivity
  · have he : i=c+b+2+(i-(c+b+2)) := by omega
    rw [he,tab.x _ (by omega),tab.xn _ (by omega)]
    constructor <;> positivity

private theorem four_perm (k nx nw nv nu : ℕ) (P Q R : Finset ℕ)
    (hp : ∀ i∈P, i<k ∧ i≠nx ∧ i≠nw ∧ i≠nv ∧ i≠nu)
    (hq : ∀ i∈Q, i<k ∧ i≠nx ∧ i≠nw ∧ i≠nv ∧ i≠nu)
    (hr : ∀ i∈R, i<k ∧ i≠nx ∧ i≠nw ∧ i≠nv ∧ i≠nu)
    (hpq : Disjoint P Q) (hpr : Disjoint P R) (hqr : Disjoint Q R)
    (hn : ([nx,nw,nv,nu] : List ℕ).Nodup)
    (hb : ∀ i∈([nx,nw,nv,nu] : List ℕ), i<k) :
    let G := Finset.range k \ (P∪Q∪R∪{nx,nw,nv,nu})
    (P.toList ++ nx :: Q.toList ++ nw :: R.toList ++ nv :: G.toList ++ [nu]).Perm
      (List.range k) := by
  classical
  let E : Finset ℕ := ⟨([nx,nw,nv,nu] : List ℕ), hn⟩
  have he : E={nx,nw,nv,nu} := by ext i; simp [E]
  have hsubE : E ⊆ Finset.range k := by intro i hi; exact Finset.mem_range.mpr (hb i (by simpa [E] using hi))
  have hPE : Disjoint P E := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    have hh := hp i hi
    simp only [E,Finset.mem_mk,Multiset.mem_coe,List.mem_cons,List.mem_singleton] at hj
    tauto
  have hQE : Disjoint Q E := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    have hh := hq i hi
    simp only [E,Finset.mem_mk,Multiset.mem_coe,List.mem_cons,List.mem_singleton] at hj
    tauto
  have hRE : Disjoint R E := by
    apply Finset.disjoint_left.mpr
    intro i hi hj
    have hh := hr i hi
    simp only [E,Finset.mem_mk,Multiset.mem_coe,List.mem_cons,List.mem_singleton] at hj
    tauto
  let S := P ∪ Q ∪ R ∪ E
  have hsub : S ⊆ Finset.range k := by
    intro i hi
    simp only [S,Finset.mem_union] at hi
    rcases hi with ((hi|hi)|hi)|hi
    · exact Finset.mem_range.mpr (hp i hi).1
    · exact Finset.mem_range.mpr (hq i hi).1
    · exact Finset.mem_range.mpr (hr i hi).1
    · exact hsubE hi
  have hfull := Finset.sdiff_union_of_subset hsub
  have hdis : Disjoint (Finset.range k \ S) S := Finset.sdiff_disjoint
  have hPQ : Disjoint (P∪Q) R := Finset.disjoint_union_left.mpr ⟨hpr,hqr⟩
  have hE : Disjoint (P∪Q∪R) E := Finset.disjoint_union_left.mpr
    ⟨Finset.disjoint_union_left.mpr ⟨hPE,hQE⟩,hRE⟩
  have hval : (Finset.range k).val = (Finset.range k \ S).val+P.val+Q.val+R.val+E.val := by
    rw [←hfull,Finset.val_union hdis]
    dsimp [S]
    rw [Finset.val_union hE,Finset.val_union hPQ,Finset.val_union hpq]
    ac_rfl
  change (P.toList ++ nx :: Q.toList ++ nw :: R.toList ++ nv ::
    (Finset.range k \ (P∪Q∪R∪{nx,nw,nv,nu})).toList ++ [nu]).Perm _
  rw [←he]
  apply Multiset.coe_eq_coe.mp
  change P.val+({nx}+Q.val)+({nw}+R.val)+({nv}+(Finset.range k \ S).val)+{nu} = (Finset.range k).val
  rw [hval]
  dsimp [E]
  change _ = (Finset.range k \ S).val+P.val+Q.val+R.val+({nx}+{nw}+{nv}+{nu})
  ac_rfl

/-- Four positive blocks ending at four specified jumps; all natural takes are included. -/
private theorem four_strip (f : ℕ → ℤ) (P Q R G : List ℕ) (nx nw nv nu : ℕ)
    (C h : ℤ)
    (hp : ∀ i∈P, 0≤f i) (hq : ∀ i∈Q, 0≤f i)
    (hr : ∀ i∈R, 0≤f i) (hg : ∀ i∈G, 0≤f i)
    (hh : 0≤h)
    (h1 : h+(P.map f).sum ≤ C ∧ 0≤h+(P.map f).sum+f nx)
    (h2 : h+(P.map f).sum+f nx+(Q.map f).sum ≤ C ∧
      0≤h+(P.map f).sum+f nx+(Q.map f).sum+f nw)
    (h3 : h+(P.map f).sum+f nx+(Q.map f).sum+f nw+(R.map f).sum ≤ C ∧
      0≤h+(P.map f).sum+f nx+(Q.map f).sum+f nw+(R.map f).sum+f nv)
    (h4 : 0≤-f nu ∧ -f nu≤C)
    (ht : h+((P++nx::Q++nw::R++nv::G++[nu]).map f).sum=0) :
    InStrip f C h (P++nx::Q++nw::R++nv::G++[nu]) := by
  simp only [List.map_append,List.sum_append,List.map_cons,List.sum_cons,
    List.map_singleton,List.sum_singleton] at ht
  have endG : h+(P.map f).sum+f nx+(Q.map f).sum+f nw+(R.map f).sum+f nv+(G.map f).sum = -f nu := by omega
  simp only [List.append_assoc]
  apply inStrip_append (l := P) (r := nx::(Q++nw::R++nv::G++[nu]))
    (positive_block_strip hp hh h1.1)
  change 0≤h+(P.map f).sum ∧ h+(P.map f).sum≤C ∧ _
  refine ⟨by have := inStrip_prefix (positive_block_strip hp hh h1.1) P.length; simpa using this.1, h1.1, ?_⟩
  apply inStrip_append (l := Q) (r := nw::(R++nv::G++[nu]))
    (positive_block_strip hq h1.2 h2.1)
  change 0≤h+(P.map f).sum+f nx+(Q.map f).sum ∧ _ ∧ _
  refine ⟨?_,h2.1,?_⟩
  · have := inStrip_prefix (positive_block_strip hq h1.2 h2.1) Q.length
    simpa only [List.take_length,add_assoc] using this.1
  apply inStrip_append (l := R) (r := nv::(G++[nu]))
    (positive_block_strip hr h2.2 h3.1)
  change 0≤h+(P.map f).sum+f nx+(Q.map f).sum+f nw+(R.map f).sum ∧ _ ∧ _
  refine ⟨?_,h3.1,?_⟩
  · have := inStrip_prefix (positive_block_strip hr h2.2 h3.1) R.length
    simpa only [List.take_length,add_assoc] using this.1
  apply inStrip_append (l := G) (r := [nu])
    (positive_block_strip hg h3.2 (by omega))
  simp only [InStrip]
  exact ⟨by omega,by omega,by simpa [endG] using h4.1,by simpa [endG] using h4.2⟩

end D5.S3.Combinatorics.Circle.FourNegative.AscendingD2
