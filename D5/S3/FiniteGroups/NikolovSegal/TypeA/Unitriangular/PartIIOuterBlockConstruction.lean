/- GID: D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIOuterBlockConstruction
   generality: G
   mirror-B: D5/B/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIOuterBlockConstruction
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual type-A matrix and quotient mathematics for uniform ordered products. -/

import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Group.Conj
import Mathlib.Algebra.Group.Subgroup.Basic
import Mathlib.Data.List.TakeDrop
import Mathlib.Data.List.OfFn
import D5.S3.FiniteGroups.NikolovSegal.CosetPowerBridge
import Mathlib.Tactic.Group
import Lean.Elab.Tactic.Omega
set_option autoImplicit false
/-! Continuing Part II printed pp246,250--251. These are actual ordered
word kernels; they are not a finite-simple quantitative supplier. The
exact finite-outer tuple consumer is constructed below; genuine uniform
fixed-root/class-width existence remains unproved. -/
namespace NikolovSegal.PartIIOuterBlockConstruction
universe u
variable {S : Type u} [Group S]
private def trajectory : List (MulAut S) → S → List S
  | [],_ => []
  | beta::tail,g => g::trajectory tail (beta g)
private def values (beta : List (MulAut S)) (c : List S) : List S :=
  List.zipWith (fun alpha x => x⁻¹*alpha x) beta c
private theorem trajectory_length (beta : List (MulAut S)) (g : S) :
    (trajectory beta g).length=beta.length := by
  induction beta generalizing g with
  | nil => rfl
  | cons b bs ih => simpa only [trajectory,List.length_cons] using congrArg Nat.succ (ih (b g))
/-- Forward maps compose in reverse order here. The chosen variables are
an actual trajectory, so consecutive group factors cancel in their exact
printed order. Opposite maps are independent automorphisms. -/
theorem actual_ordered_value_trajectory (beta : List (MulAut S)) (g : S) :
    (values beta (trajectory beta g)).prod=g⁻¹*(beta.reverse.prod) g := by
  induction beta generalizing g with
  | nil => simp [values,trajectory]
  | cons b bs ih =>
    simp only [trajectory,values,List.zipWith_cons_cons,List.prod_cons,
      List.reverse_cons,List.prod_append,List.prod_singleton,List.prod_nil,MulAut.one_apply,MulAut.mul_apply]
    change (g⁻¹*b g)*(values bs (trajectory bs (b g))).prod=_
    rw [ih]
    group
/-- Actual Lemma3.1(i): the interval is nonempty and consecutive. This
will be applied to INVERSE powered automorphism words, whose inverse gives
exact reverse composition for actual_ordered_value_trajectory. -/
theorem actual_finite_identity_interval {H : Type*} [Group H] [Fintype H]
    (l : List H) (hcard : Fintype.card H≤l.length) :
    ∃ i j : ℕ, i < j ∧ j≤l.length ∧ ((l.drop i).take (j-i)).prod=1 := by
  classical
  let prefixWord : Fin (l.length+1) → H := fun i => (l.take i.val).prod
  obtain ⟨a,b,hab,he⟩ := Fintype.exists_ne_map_eq_of_card_lt prefixWord (by simp only [Fintype.card_fin]; omega)
  have hne : a.val≠b.val := Fin.val_ne_of_ne hab
  have hstep : ∀ i j : Fin (l.length+1), i.val < j.val → prefixWord i=prefixWord j →
      ((l.drop i.val).take (j.val-i.val)).prod=1 := by
    intro i j hij hp
    have hsplit : l.take j.val=l.take i.val++(l.drop i.val).take (j.val-i.val) := by
      conv_lhs => rw [show j.val=i.val+(j.val-i.val) by omega,List.take_add]
    have heq : (l.take i.val).prod=(l.take i.val).prod*((l.drop i.val).take (j.val-i.val)).prod := by
      change (l.take i.val).prod=(l.take j.val).prod at hp
      rw [hsplit,List.prod_append] at hp
      exact hp
    exact mul_left_cancel (by simpa only [mul_one] using heq.symm)
  rcases lt_or_gt_of_ne hne with h | h
  · exact ⟨a.val,b.val,h,by omega,hstep a b h he⟩
  · exact ⟨b.val,a.val,h,by omega,hstep b a h he.symm⟩
private theorem fixed_conj_commute (beta : MulAut S) (z : S) (hz : beta z=z) :
    Commute (MulAut.conj z) beta := by
  apply MulEquiv.ext
  intro x
  simp only [MulAut.mul_apply,MulAut.conj_apply,map_mul,map_inv,hz]
/-- The original d-power is retained. The root z is fixed BEFORE targets
by the actual finite outer action, and d|q supplies its corrected power. -/
theorem actual_fixed_root_power (beta : MulAut S) (z : S) (hz : beta z=z)
    {q d : ℕ} (hd : d ∣ q) :
    (MulAut.conj (z^(q/d))*beta)^d=MulAut.conj (z^q)*beta^d := by
  have hroot : beta (z^(q/d))=z^(q/d) := by simp only [map_pow,hz]
  rw [(fixed_conj_commute beta _ hroot).mul_pow,← map_pow,← pow_mul,Nat.div_mul_cancel hd]
/-- Actual Section5 one-block construction, in the forward convention.
The inverse outer interval gives reverse-composition identity. One fixed
inner root at its first entry then makes the whole corrected action exactly
conjugation by z^q; the genuine coordinate witnesses are the trajectory. -/
theorem actual_fixed_outer_block (beta : MulAut S) (tail : List (MulAut S))
    (z : S) (hz : beta z=z) {q d : ℕ} (hd : d ∣ q)
    (hword : tail.reverse.prod*beta^d=1) :
    ∀ g : S, (values ((MulAut.conj (z^(q/d))*beta)^d::tail)
      (trajectory ((MulAut.conj (z^(q/d))*beta)^d::tail) g)).prod=
        g⁻¹*(z^q)*g*(z^q)⁻¹ := by
  have hzq : beta (z^q)=z^q := by simp only [map_pow,hz]
  have hc := (fixed_conj_commute beta (z^q) hzq).pow_right d
  have hreverse : (((MulAut.conj (z^(q/d))*beta)^d::tail).reverse).prod=MulAut.conj (z^q) := by
    rw [List.reverse_cons,List.prod_append,List.prod_singleton,actual_fixed_root_power beta z hz hd]
    rw [hc.eq,← mul_assoc,hword,one_mul]
  intro g
  rw [actual_ordered_value_trajectory,hreverse,MulAut.conj_apply]
  group
/-- The finite interval is actually selected from the given POWERED outer
action word. It is nonempty, its first divisor is genuine, and its one
inner correction precedes EVERY ordinary commutator target. This consumes
both elementary paper lemmas; quantitative fixed-root/class existence is
not assumed to have been proved. -/
theorem actual_finite_outer_interval_values (H : Subgroup (MulAut S)) [Fintype H]
    (z : S) (hz : ∀ beta : H, (beta : MulAut S) z=z)
    (l : List (H×ℕ)) (hcard : Fintype.card H≤l.length) {q : ℕ}
    (hd : ∀ p∈l, 0<p.2 ∧ p.2 ∣ q) :
    ∃ i j : ℕ, ∃ beta : H, ∃ d : ℕ, ∃ tail : List (H×ℕ),
      i < j ∧ j≤l.length ∧ (l.drop i).take (j-i)=(beta,d)::tail ∧
      0<d ∧ d ∣ q ∧
      ∀ g : S, (values (((MulAut.conj (z^(q/d))*(beta : MulAut S))^d)::
          tail.map (fun p => (p.1 : MulAut S)^p.2))
        (trajectory (((MulAut.conj (z^(q/d))*(beta : MulAut S))^d)::
          tail.map (fun p => (p.1 : MulAut S)^p.2)) g)).prod=
          g⁻¹*(z^q)*g*(z^q)⁻¹ := by
  classical
  let W : List H := l.map (fun p => (p.1^p.2)⁻¹)
  obtain ⟨i,j,hij,hj,hword⟩ := actual_finite_identity_interval W (by simpa only [W,List.length_map] using hcard)
  have hjl : j≤l.length := by simpa only [W,List.length_map] using hj
  let slice := (l.drop i).take (j-i)
  have hlen : 0<slice.length := by
    simp only [slice,List.length_take,List.length_drop]
    omega
  obtain ⟨p,tail,hs⟩ : ∃ p tail, slice=p::tail := by
    cases hs : slice with
    | nil => simp only [hs,List.length_nil] at hlen; omega
    | cons p tail => exact ⟨p,tail,rfl⟩
  rcases p with ⟨beta,d⟩
  have hmem : (beta,d)∈l := List.mem_of_mem_drop (List.mem_of_mem_take (by
    change (beta,d)∈slice
    rw [hs]; exact List.mem_cons_self))
  let B : List (MulAut S) := slice.map (fun p => (p.1 : MulAut S)^p.2)
  have hInv : (B.map (fun b => b⁻¹)).prod=1 := by
    have hh := congrArg H.subtype hword
    simpa only [B,slice,W,← List.map_drop,← List.map_take,map_list_prod,map_one,
      List.map_map,Function.comp_def,map_inv,map_pow,Subgroup.subtype_apply] using hh
  have hB : B.reverse.prod=1 := by rw [List.prod_reverse_noncomm,hInv,inv_one]
  have hActual : (tail.map (fun p => (p.1 : MulAut S)^p.2)).reverse.prod*
      (beta : MulAut S)^d=1 := by
    simpa only [B,hs,List.map_cons,List.reverse_cons,List.prod_append,List.prod_cons,
      List.prod_nil,mul_one] using hB
  exact ⟨i,j,beta,d,tail,hij,hjl,hs,(hd _ hmem).1,(hd _ hmem).2,
    actual_fixed_outer_block (beta : MulAut S) _ z (hz beta) (hd _ hmem).2 hActual⟩
private def wordValues {H : Subgroup (MulAut S)} (l : List (H×ℕ)) (h c : List S) : List S :=
  List.zipWith (fun p hx => hx.2⁻¹*((MulAut.conj hx.1*(p.1 : MulAut S))^p.2) hx.2) l (h.zip c)
private theorem wordValues_append {H : Subgroup (MulAut S)}
    (l0 l1 : List (H×ℕ)) (h0 h1 c0 c1 : List S)
    (hh : h0.length=l0.length) (hc : c0.length=l0.length) :
    wordValues (l0++l1) (h0++h1) (c0++c1)=wordValues l0 h0 c0++wordValues l1 h1 c1 := by
  dsimp only [wordValues]
  rw [List.zip_append (hh.trans hc.symm),List.zipWith_append (by simp only [List.length_zip,hh,hc,Nat.min_self])]
private theorem wordValues_ones {H : Subgroup (MulAut S)} (l : List (H×ℕ)) :
    wordValues l (List.replicate l.length 1) (List.replicate l.length 1)=List.replicate l.length 1 := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    simpa only [wordValues,List.length_cons,List.replicate_succ,List.zip_cons_cons,
      List.zipWith_cons_cons,inv_one,map_one,one_mul] using congrArg (List.cons (1:S)) ih
private theorem zero_correction_values {H : Subgroup (MulAut S)} (l : List (H×ℕ)) (c : List S) :
    wordValues l (List.replicate l.length 1) c=values (l.map (fun p => (p.1 : MulAut S)^p.2)) c := by
  induction l generalizing c with
  | nil => simp [wordValues,values]
  | cons p ps ih =>
    cases c with
    | nil => simp [wordValues,values]
    | cons x xs =>
      simpa only [wordValues,values,List.length_cons,List.replicate_succ,List.zip_cons_cons,
        List.zipWith_cons_cons,List.map_cons,map_one,one_mul] using
        congrArg (List.cons (x⁻¹*((p.1 : MulAut S)^p.2) x)) (ih xs)
private theorem one_correction_values {H : Subgroup (MulAut S)} (p : H×ℕ)
    (tail : List (H×ℕ)) (h : S) (c : List S) :
    wordValues (p::tail) (h::List.replicate tail.length 1) c=
      values (((MulAut.conj h*(p.1 : MulAut S))^p.2)::tail.map (fun p => (p.1 : MulAut S)^p.2)) c := by
  cases c with
  | nil => simp [wordValues,values]
  | cons x xs =>
    simpa only [wordValues,values,List.zip_cons_cons,List.zipWith_cons_cons] using
      congrArg (List.cons (x⁻¹*((MulAut.conj h*(p.1 : MulAut S))^p.2) x))
        (zero_correction_values tail xs)
/-- Full one-block VALUE supplier, consuming the ACTUALLY selected finite
outer interval. Prefix/suffix witnesses are identities, every variable is
paired with its original prescribed automorphism/divisor, and h is chosen
before ALL g. The range is ordinary commutator values of z^q, not all S. -/
theorem actual_finite_outer_block_values (H : Subgroup (MulAut S)) [Fintype H]
    (z : S) (hz : ∀ beta : H, (beta : MulAut S) z=z)
    (l : List (H×ℕ)) (hcard : Fintype.card H≤l.length) {q : ℕ}
    (hd : ∀ p∈l, 0<p.2 ∧ p.2 ∣ q) :
    ∃ h : List S, h.length=l.length ∧ ∀ g : S, ∃ c : List S,
      c.length=l.length ∧ (wordValues l h c).prod=g⁻¹*(z^q)*g*(z^q)⁻¹ := by
  obtain ⟨i,j,beta,d,tail,hij,hj,hs,hdpos,hdq,hcover⟩ :=
    actual_finite_outer_interval_values H z hz l hcard hd
  let pref := l.take i
  let suff := l.drop j
  let mid := (beta,d)::tail
  have hsplit : l=pref++mid++suff := by
    have he : l.take j=l.take i++(l.drop i).take (j-i) := by
      conv_lhs => rw [show j=i+(j-i) by omega,List.take_add]
    have hh := List.take_append_drop j l
    rw [he,hs] at hh
    exact hh.symm
  let hmid := z^(q/d)::List.replicate tail.length 1
  let h := List.replicate pref.length 1++hmid++List.replicate suff.length 1
  have hml : hmid.length=mid.length := by simp only [hmid,mid,List.length_cons,List.length_replicate]
  have hlen : h.length=l.length := by rw [hsplit]; simp only [h,List.length_append,List.length_replicate,hml]
  refine ⟨h,hlen,?_⟩
  intro g
  let powers := ((MulAut.conj (z^(q/d))*(beta : MulAut S))^d)::tail.map (fun p => (p.1 : MulAut S)^p.2)
  let cmid := trajectory powers g
  let c := List.replicate pref.length 1++cmid++List.replicate suff.length 1
  have cml : cmid.length=mid.length := by
    rw [trajectory_length]; simp only [powers,mid,List.length_cons,List.length_map]
  have clen : c.length=l.length := by rw [hsplit]; simp only [c,List.length_append,List.length_replicate,cml]
  refine ⟨c,clen,?_⟩
  rw [hsplit]
  change (wordValues (pref++mid++suff)
    (List.replicate pref.length 1++hmid++List.replicate suff.length 1)
    (List.replicate pref.length 1++cmid++List.replicate suff.length 1)).prod=_
  rw [wordValues_append _ suff _ _ _ _ (by simp only [List.length_append,List.length_replicate,hml])
      (by simp only [List.length_append,List.length_replicate,cml]),
    wordValues_append pref mid _ _ _ _ (by simp) (by simp),
    List.prod_append,List.prod_append,wordValues_ones,wordValues_ones]
  simp only [List.prod_replicate,one_pow,one_mul,mul_one]
  rw [one_correction_values]
  exact hcover g
/-- Repeated actual finite-outer blocks. ONE complete correction list
precedes every tuple g; all prefix/suffix positions keep their ORIGINAL
automorphism/divisor and identity witness. The output is the ordered R-fold
product of ordinary z^q commutator VALUES, with no coverage premise. -/
theorem actual_finite_outer_blocks_values (H : Subgroup (MulAut S)) [Fintype H]
    (z : S) (hz : ∀ beta : H, (beta : MulAut S) z=z) (q R : ℕ) :
    ∀ (blocks : Fin R → List (H×ℕ)),
      (∀ r, Fintype.card H≤(blocks r).length) →
      (∀ r p, p∈blocks r → 0<p.2 ∧ p.2 ∣ q) →
      ∃ h : List S, h.length=(List.ofFn blocks).flatten.length ∧
      ∀ g : Fin R → S, ∃ c : List S, c.length=(List.ofFn blocks).flatten.length ∧
        (wordValues (List.ofFn blocks).flatten h c).prod=
          (List.ofFn (fun r => (g r)⁻¹*(z^q)*(g r)*(z^q)⁻¹)).prod := by
  induction R with
  | zero =>
    intro blocks hcard hd
    refine ⟨[],by simp,?_⟩
    intro g
    refine ⟨[],by simp,?_⟩
    simp [wordValues]
  | succ R ih =>
    intro blocks hcard hd
    obtain ⟨h0,h0len,h0val⟩ := actual_finite_outer_block_values H z hz (blocks 0) (hcard 0) (hd 0)
    obtain ⟨hRest,hRestlen,hRestval⟩ := ih (fun r => blocks r.succ)
      (fun r => hcard r.succ) (fun r => hd r.succ)
    refine ⟨h0++hRest,?_,?_⟩
    · simpa only [List.ofFn_succ,List.flatten_cons,List.length_append,h0len,hRestlen]
    · intro g
      obtain ⟨c0,c0len,c0val⟩ := h0val (g 0)
      obtain ⟨cRest,cRestlen,cRestval⟩ := hRestval (fun r => g r.succ)
      refine ⟨c0++cRest,?_,?_⟩
      · simpa only [List.ofFn_succ,List.flatten_cons,List.length_append,c0len,cRestlen]
      · rw [List.ofFn_succ,List.flatten_cons,wordValues_append _ _ _ _ _ _ h0len c0len,
          List.prod_append,c0val,cRestval]
        simp only [List.ofFn_succ,List.prod_cons]
private theorem ofFn_of_length {T : Type*} {n : ℕ} (l : List T)
    (hl : l.length=n) : ∃ f : Fin n → T, List.ofFn f=l := by
  cases hl
  exact ⟨l.get,List.ofFn_get l⟩
private theorem zipWith_ofFn {T U V : Type*} (f : T → U → V) {n : ℕ}
    (a : Fin n → T) (b : Fin n → U) :
    List.zipWith f (List.ofFn a) (List.ofFn b)=List.ofFn (fun i => f (a i) (b i)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simpa only [List.ofFn_succ,List.zipWith_cons_cons] using
      congrArg (List.cons (f (a 0) (b 0))) (ih (fun i => a i.succ) (fun i => b i.succ))
private theorem wordValues_ofFn {H : Subgroup (MulAut S)} {n : ℕ}
    (l : Fin n → H×ℕ) (h c : Fin n → S) :
    wordValues (List.ofFn l) (List.ofFn h) (List.ofFn c)=
      List.ofFn (fun i => (c i)⁻¹*((MulAut.conj (h i)*(l i).1)^((l i).2)) (c i)) := by
  dsimp only [wordValues]
  rw [List.zip_eq_zipWith,zipWith_ofFn,zipWith_ofFn]
/-- The exact row-major Fin tuple consumer of the actual Section5 blocks.
The chosen correction is global and precedes every tuple of ordinary
commutator witnesses. The range is R ordered z^q commutator VALUES;
quantitative class-width/fixed-root inputs are not asserted. -/
theorem actual_finite_outer_Fin_values (H : Subgroup (MulAut S)) [Fintype H]
    (z : S) (hz : ∀ beta : H, (beta : MulAut S) z=z)
    (q R A : ℕ) (hcard : Fintype.card H≤A)
    (beta : Fin (R*A) → H) (d : Fin (R*A) → ℕ)
    (hd : ∀ i, 0<d i ∧ d i ∣ q) :
    ∃ h : Fin (R*A) → S, ∀ g : Fin R → S, ∃ c : Fin (R*A) → S,
      NikolovSegal.orderedProduct (fun i => (c i)⁻¹*
        ((MulAut.conj (h i)*(beta i : MulAut S))^(d i)) (c i))=
      NikolovSegal.orderedProduct (fun r => (g r)⁻¹*z^q*(g r)*(z^q)⁻¹) := by
  let l : Fin (R*A) → H×ℕ := fun i => (beta i,d i)
  let idx (r : Fin R) (j : Fin A) : Fin (R*A) := ⟨r.val*A+j.val,
    calc r.val*A+j.val < (r.val+1)*A :=
          (Nat.add_lt_add_left j.isLt _).trans_eq (by rw [Nat.add_mul,Nat.one_mul])
         _ ≤ R*A := Nat.mul_le_mul_right A r.isLt⟩
  let blocks : Fin R → List (H×ℕ) := fun r => List.ofFn (fun j => l (idx r j))
  have hflat : (List.ofFn blocks).flatten=List.ofFn l := (List.ofFn_mul l).symm
  obtain ⟨h,hlen,hval⟩ := actual_finite_outer_blocks_values H z hz q R blocks
    (fun r => by simpa only [blocks,List.length_ofFn] using hcard)
    (fun r p hp => by
      obtain ⟨j,hj⟩ := List.mem_ofFn.mp hp
      subst p
      exact hd (idx r j))
  rw [hflat,List.length_ofFn] at hlen
  obtain ⟨hf,hhf⟩ := ofFn_of_length h hlen
  refine ⟨hf,?_⟩
  intro g
  obtain ⟨c,clen,hc⟩ := hval g
  rw [hflat,List.length_ofFn] at clen
  obtain ⟨cf,hcf⟩ := ofFn_of_length c clen
  refine ⟨cf,?_⟩
  rw [hflat,← hhf,← hcf,wordValues_ofFn] at hc
  exact hc
/-- The q=1 Section4 block requires no fixed root. In the forward
composition convention its first correction is beta(z), so reverse
composition of the actual corrected interval is conjugation by z. -/
theorem actual_finite_untwisted_block_values (H : Subgroup (MulAut S)) [Fintype H]
    (z : S) (l : List (H×ℕ)) (hcard : Fintype.card H≤l.length)
    (hd : ∀ p∈l, p.2=1) :
    ∃ h : List S, h.length=l.length ∧ ∀ g : S, ∃ c : List S,
      c.length=l.length ∧ (wordValues l h c).prod=g⁻¹*z*g*z⁻¹ := by
  classical
  let W : List H := l.map (fun p => (p.1^p.2)⁻¹)
  obtain ⟨i,j,hij,hj,hword⟩ := actual_finite_identity_interval W
    (by simpa only [W,List.length_map] using hcard)
  have hjl : j≤l.length := by simpa only [W,List.length_map] using hj
  let slice := (l.drop i).take (j-i)
  have hlen : 0<slice.length := by
    simp only [slice,List.length_take,List.length_drop]
    omega
  obtain ⟨p,tail,hs⟩ : ∃ p tail, slice=p::tail := by
    cases hs : slice with
    | nil => simp only [hs,List.length_nil] at hlen; omega
    | cons p tail => exact ⟨p,tail,rfl⟩
  rcases p with ⟨beta,d⟩
  have hmem : (beta,d)∈l := List.mem_of_mem_drop (List.mem_of_mem_take (by
    change (beta,d)∈slice
    rw [hs]; exact List.mem_cons_self))
  have hd1 : d=1 := hd _ hmem
  let B : List (MulAut S) := slice.map (fun p => (p.1 : MulAut S)^p.2)
  have hInv : (B.map (fun b => b⁻¹)).prod=1 := by
    have hh := congrArg H.subtype hword
    simpa only [B,slice,W,← List.map_drop,← List.map_take,map_list_prod,map_one,
      List.map_map,Function.comp_def,map_inv,map_pow,Subgroup.subtype_apply] using hh
  have hB : B.reverse.prod=1 := by rw [List.prod_reverse_noncomm,hInv,inv_one]
  have hActual : (tail.map (fun p => (p.1 : MulAut S)^p.2)).reverse.prod*
      (beta : MulAut S)=1 := by
    simpa only [B,hs,List.map_cons,List.reverse_cons,List.prod_append,List.prod_cons,
      List.prod_nil,mul_one,hd1,pow_one] using hB
  have hTail : (tail.map (fun p => (p.1 : MulAut S)^p.2)).reverse.prod=
      (beta : MulAut S)⁻¹ := by
    calc _ = ((tail.map (fun p => (p.1 : MulAut S)^p.2)).reverse.prod*
             (beta : MulAut S))*(beta : MulAut S)⁻¹ := by group
         _ = _ := by rw [hActual,one_mul]
  have hreverse : ((((MulAut.conj ((beta : MulAut S) z)*(beta : MulAut S))^d)::
      tail.map (fun p => (p.1 : MulAut S)^p.2)).reverse).prod=MulAut.conj z := by
    rw [List.reverse_cons,List.prod_append,List.prod_singleton,hd1,pow_one,hTail]
    apply MulEquiv.ext; intro x
    simp only [MulAut.mul_apply,MulAut.conj_apply,MulAut.inv_apply,map_mul,map_inv,
      MulEquiv.symm_apply_apply]
  let pref := l.take i
  let suff := l.drop j
  let mid := (beta,d)::tail
  have hsplit : l=pref++mid++suff := by
    have he : l.take j=l.take i++(l.drop i).take (j-i) := by
      conv_lhs => rw [show j=i+(j-i) by omega,List.take_add]
    have hh := List.take_append_drop j l
    rw [he,show (l.drop i).take (j-i)=(beta,d)::tail from hs] at hh
    exact hh.symm
  let hmid := (beta : MulAut S) z::List.replicate tail.length 1
  let h := List.replicate pref.length 1++hmid++List.replicate suff.length 1
  have hml : hmid.length=mid.length := by simp only [hmid,mid,List.length_cons,List.length_replicate]
  have hlen : h.length=l.length := by rw [hsplit]; simp only [h,List.length_append,List.length_replicate,hml]
  refine ⟨h,hlen,?_⟩
  intro g
  let powers := ((MulAut.conj ((beta : MulAut S) z)*(beta : MulAut S))^d)::tail.map (fun p => (p.1 : MulAut S)^p.2)
  let cmid := trajectory powers g
  let c := List.replicate pref.length 1++cmid++List.replicate suff.length 1
  have cml : cmid.length=mid.length := by
    rw [trajectory_length]; simp only [powers,mid,List.length_cons,List.length_map]
  have clen : c.length=l.length := by rw [hsplit]; simp only [c,List.length_append,List.length_replicate,cml]
  refine ⟨c,clen,?_⟩
  rw [hsplit]
  change (wordValues (pref++mid++suff)
    (List.replicate pref.length 1++hmid++List.replicate suff.length 1)
    (List.replicate pref.length 1++cmid++List.replicate suff.length 1)).prod=_
  rw [wordValues_append _ suff _ _ _ _ (by simp only [List.length_append,List.length_replicate,hml])
      (by simp only [List.length_append,List.length_replicate,cml]),
    wordValues_append pref mid _ _ _ _ (by simp) (by simp),
    List.prod_append,List.prod_append,wordValues_ones,wordValues_ones]
  simp only [List.prod_replicate,one_pow,one_mul,mul_one]
  rw [one_correction_values]
  rw [actual_ordered_value_trajectory,hreverse,MulAut.conj_apply]
  group
/-- Actual untwisted repeated blocks, used for the finite exceptional
q=1 step of PartII Section4. No element is assumed fixed by the outer group. -/
theorem actual_finite_untwisted_blocks_values (H : Subgroup (MulAut S)) [Fintype H]
    (z : S) (R : ℕ) :
    ∀ (blocks : Fin R → List (H×ℕ)),
      (∀ r, Fintype.card H≤(blocks r).length) →
      (∀ r p, p∈blocks r → p.2=1) →
      ∃ h : List S, h.length=(List.ofFn blocks).flatten.length ∧
      ∀ g : Fin R → S, ∃ c : List S, c.length=(List.ofFn blocks).flatten.length ∧
        (wordValues (List.ofFn blocks).flatten h c).prod=
          (List.ofFn (fun r => (g r)⁻¹*z*(g r)*z⁻¹)).prod := by
  induction R with
  | zero =>
    intro blocks hcard hd
    refine ⟨[],by simp,?_⟩
    intro g
    refine ⟨[],by simp,?_⟩
    simp [wordValues]
  | succ R ih =>
    intro blocks hcard hd
    obtain ⟨h0,h0len,h0val⟩ := actual_finite_untwisted_block_values H z (blocks 0) (hcard 0) (hd 0)
    obtain ⟨hRest,hRestlen,hRestval⟩ := ih (fun r => blocks r.succ)
      (fun r => hcard r.succ) (fun r => hd r.succ)
    refine ⟨h0++hRest,?_,?_⟩
    · simpa only [List.ofFn_succ,List.flatten_cons,List.length_append,h0len,hRestlen]
    · intro g
      obtain ⟨c0,c0len,c0val⟩ := h0val (g 0)
      obtain ⟨cRest,cRestlen,cRestval⟩ := hRestval (fun r => g r.succ)
      refine ⟨c0++cRest,?_,?_⟩
      · simpa only [List.ofFn_succ,List.flatten_cons,List.length_append,c0len,cRestlen]
      · rw [List.ofFn_succ,List.flatten_cons,wordValues_append _ _ _ _ _ _ h0len c0len,
          List.prod_append,c0val,cRestval]
        simp only [List.ofFn_succ,List.prod_cons]
/-- Original Fin tuple and exact increasing order, q=1, without a fixed-root
hypothesis. The corrections precede all ordinary commutator witness tuples. -/
theorem actual_finite_untwisted_Fin_values (H : Subgroup (MulAut S)) [Fintype H]
    (z : S) (R A : ℕ) (hcard : Fintype.card H≤A)
    (beta : Fin (R*A) → H) :
    ∃ h : Fin (R*A) → S, ∀ g : Fin R → S, ∃ c : Fin (R*A) → S,
      NikolovSegal.orderedProduct (fun i => (c i)⁻¹*
        (MulAut.conj (h i)*(beta i : MulAut S)) (c i))=
      NikolovSegal.orderedProduct (fun r => (g r)⁻¹*z*(g r)*z⁻¹) := by
  let l : Fin (R*A) → H×ℕ := fun i => (beta i,1)
  let idx (r : Fin R) (j : Fin A) : Fin (R*A) := ⟨r.val*A+j.val,
    calc r.val*A+j.val < (r.val+1)*A :=
          (Nat.add_lt_add_left j.isLt _).trans_eq (by rw [Nat.add_mul,Nat.one_mul])
         _ ≤ R*A := Nat.mul_le_mul_right A r.isLt⟩
  let blocks : Fin R → List (H×ℕ) := fun r => List.ofFn (fun j => l (idx r j))
  have hflat : (List.ofFn blocks).flatten=List.ofFn l := (List.ofFn_mul l).symm
  obtain ⟨h,hlen,hval⟩ := actual_finite_untwisted_blocks_values H z R blocks
    (fun r => by simpa only [blocks,List.length_ofFn] using hcard)
    (fun r p hp => by
      obtain ⟨j,hj⟩ := List.mem_ofFn.mp hp
      subst p
      rfl)
  rw [hflat,List.length_ofFn] at hlen
  obtain ⟨hf,hhf⟩ := ofFn_of_length h hlen
  refine ⟨hf,?_⟩
  intro g
  obtain ⟨c,clen,hc⟩ := hval g
  rw [hflat,List.length_ofFn] at clen
  obtain ⟨cf,hcf⟩ := ofFn_of_length c clen
  refine ⟨cf,?_⟩
  rw [hflat,← hhf,← hcf,wordValues_ofFn] at hc
  simpa only [l,pow_one,NikolovSegal.orderedProduct] using hc
/-- Section5 consumer on the ORIGINAL action tuple and original q/e
powers, with a supplied genuine inner/finite-outer normal form. The normal
form is an action identity, not a coverage premise. The actual finite blocks
construct ONE right-side correction before every ordinary witness tuple. -/
theorem actual_finite_outer_original_power_values (H : Subgroup (MulAut S)) [Fintype H]
    (z : S) (hz : ∀ b : H, (b : MulAut S) z=z)
    (q : ℕ) (hq : 0<q) (R A : ℕ) (hcard : Fintype.card H≤A)
    (beta : Fin (R*A) → MulAut S) (a : Fin (R*A) → S)
    (outer : Fin (R*A) → H)
    (hnormal : ∀ i, beta i=MulAut.conj (a i)*(outer i : MulAut S))
    (e : Fin (R*A) → ℕ) (he : ∀ i, 0<e i ∧ e i ∣ q) :
    ∃ y : Fin (R*A) → S, ∀ g : Fin R → S, ∃ c : Fin (R*A) → S,
      NikolovSegal.orderedProduct (fun i => (c i)⁻¹*
        ((beta i*MulAut.conj (y i)⁻¹)^(q/e i)) (c i))=
      NikolovSegal.orderedProduct (fun r => (g r)⁻¹*z^q*(g r)*(z^q)⁻¹) := by
  have hd : ∀ i, 0<q/e i ∧ q/e i ∣ q := fun i =>
    ⟨Nat.div_pos (Nat.le_of_dvd hq (he i).2) (he i).1,Nat.div_dvd_of_dvd (he i).2⟩
  obtain ⟨h,hvals⟩ := actual_finite_outer_Fin_values H z hz q R A hcard outer (fun i => q/e i) hd
  let h' := fun i => h i*(a i)⁻¹
  let y := fun i => (beta i).symm ((h' i)⁻¹)
  have hleft : ∀ i, MulAut.conj (h' i)*beta i=MulAut.conj (h i)*(outer i : MulAut S) := by
    intro i
    rw [hnormal i]
    simp only [h',map_mul,map_inv]
    group
  have hright : ∀ i, beta i*MulAut.conj (y i)⁻¹=MulAut.conj (h' i)*beta i := by
    intro i
    apply MulEquiv.ext; intro x
    simp only [y,MulAut.mul_apply,MulAut.conj_apply,map_mul,map_inv,
      MulEquiv.apply_symm_apply,inv_inv]
  refine ⟨y,?_⟩
  intro g
  obtain ⟨c,hc⟩ := hvals g
  refine ⟨c,?_⟩
  simpa only [hright,hleft] using hc
end NikolovSegal.PartIIOuterBlockConstruction
