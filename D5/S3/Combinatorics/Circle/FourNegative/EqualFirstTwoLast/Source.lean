/- GID: D5/S3/Combinatorics/Circle/FourNegative/EqualFirstTwoLast/Source
   generality: I
   mirror-B: none(waiver:private-consumed-source-described-at-endpoint)
   mirror-E: none(waiver:private-consumed-source)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Canonical native rows, exact totals and literal physical-label transport. -/
import D5.S3.Combinatorics.Circle.FourNegative.EqualFirstTwoLast.Arithmetic
import D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
import D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Transport

/-! UNCOMPILED source draft. All centered rows are obtained from the canonical
SourceTable at (s,s,t,s); no vector table is supplied as a hypothesis. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.EqualFirstTwoLast
open SourceWidth PeriodicShortening RunFirstEarTransport
open private A B L M N Bn Ln Mn Margin
  from D5.S3.Combinatorics.Circle.FourNegative.EqualFirstTwoLast.Arithmetic
open private source_table
  from D5.S3.Combinatorics.Circle.FourNegative.MaxPlusTwo.SourceTable
open private negative_step
  from D5.S3.Combinatorics.Circle.FourNegative.FourNegativeEventualJointLift
open private Gates
  from D5.S3.Combinatorics.Circle.FourNegative.Adjacent.FourNegativeAdjacentDoubleSchedule
open private label lift_order marked_word ladder_sum
  from D5.S3.Combinatorics.Circle.ThreeNegativeEqualOuterJointLift

private def oldValue (s t i : ℕ) : ℤ :=
  centered (N (2^s) (2^t)) ((2 : ℤ)^i * A (2^s) (2^t))
private def newValue (s t i : ℕ) : ℤ :=
  centered (2*N (2^s) (2^t)+1) ((2 : ℤ)^i * (2*A (2^s) (2^t)))
private def seed (s t : ℕ) : ℕ := 1+2^s+2^(s+s)+2^(s+s+t)

structure Rows (s t : ℕ) (q z : ℤ) (f g : ℕ → ℤ) : Prop where
  mod_nonneg : 0 ≤ N q z
  a_nonneg : 0 ≤ A q z
  b_nonneg : 0 ≤ B q
  l_nonneg : 0 ≤ L q z
  m_nonneg : 0 ≤ M q z
  bn_nonneg : 0 ≤ Bn q
  ln_nonneg : 0 ≤ Ln q z
  mn_nonneg : 0 ≤ Mn q z
  posU : ∀ i < s-1, f i=2^i*(A q z) ∧ g i=2^i*(2*A q z)
  packetU : ((List.range' (0) (s-1)).map f).sum+f (s-1)=(B q)-(A q z) ∧
    ((List.range' (0) (s-1)).map g).sum+g (s-1)=(Bn q)-(2*A q z)
  stepU : 2*f (s-1)=(B q)-N q z ∧
    2*g (s-1)=(Bn q)-(2*N q z+1)
  posV : ∀ i < t-1, f (s+i)=2^i*(B q) ∧ g (s+i)=2^i*(Bn q)
  packetV : ((List.range' (s) (t-1)).map f).sum+f (s+t-1)=(L q z)-(B q) ∧
    ((List.range' (s) (t-1)).map g).sum+g (s+t-1)=(Ln q z)-(Bn q)
  stepV : 2*f (s+t-1)=(L q z)-N q z ∧
    2*g (s+t-1)=(Ln q z)-(2*N q z+1)
  posW : ∀ i < s-1, f (s+t+i)=2^i*(L q z) ∧ g (s+t+i)=2^i*(Ln q z)
  packetW : ((List.range' (s+t) (s-1)).map f).sum+f (s+t+s-1)=(M q z)-(L q z) ∧
    ((List.range' (s+t) (s-1)).map g).sum+g (s+t+s-1)=(Mn q z)-(Ln q z)
  stepW : 2*f (s+t+s-1)=(M q z)-N q z ∧
    2*g (s+t+s-1)=(Mn q z)-(2*N q z+1)
  posX : ∀ i < s-1, f (s+t+s+i)=2^i*(M q z) ∧ g (s+t+s+i)=2^i*(Mn q z)
  packetX : ((List.range' (s+t+s) (s-1)).map f).sum+f (s+t+s+s-1)=(A q z)-(M q z) ∧
    ((List.range' (s+t+s) (s-1)).map g).sum+g (s+t+s+s-1)=(A q z)-(Mn q z)
  stepX : 2*f (s+t+s+s-1)=(A q z)-N q z ∧
    2*g (s+t+s+s-1)=(A q z)-(2*N q z+1)
  fresh : g (s+t+s+s)=A q z
  totalOld : ((List.range (s+t+s+s)).map f).sum=0
  totalNew : ((List.range (s+t+s+s+1)).map g).sum=0

private theorem pow_step (n : ℕ) (hn : 1 ≤ n) :
    (2 : ℤ)^n=2*2^(n-1) := by
  calc
    (2 : ℤ)^n=2^((n-1)+1) := by congr 1; omega
    _=2*2^(n-1) := by rw [pow_succ]; ring

set_option maxHeartbeats 1400000 in
private theorem native (s t : ℕ) (hs : 2 ≤ s) (ht : 2 ≤ t) :
    Rows s t (2^s) (2^t) (oldValue s t) (newValue s t) := by
  let q : ℤ := 2^s
  let z : ℤ := 2^t
  let r : ℤ := 2^(s-1)
  let u : ℤ := 2^(t-1)
  let f := oldValue s t
  let g := newValue s t
  have hq : q=2*r := pow_step s (by omega)
  have hz : z=2*u := pow_step t (by omega)
  obtain ⟨hA,hB,hL,hM,huf,hvf,hwf,hxf,hug,hvg,hwg,hxg,hfresh⟩ :=
    source_table s s t s hs hs ht hs
  change 1≤A q z ∧ A q z<N q z at hA
  change 1≤B q ∧ B q<N q z at hB
  change 1≤L q z ∧ L q z<N q z at hL
  change 1≤M q z ∧ M q z<N q z at hM
  change ∀ i<s, f i=if i+1<s then 2^i*(A q z) else -(N q z-(B q))/2 at huf
  change ∀ i<s, g i=if i+1<s then 2^i*(2*A q z) else -((2*N q z+1)-(Bn q))/2 at hug
  have posU (i : ℕ) (hi : i<s-1) :
      f i=2^i*(A q z) ∧ g i=2^i*(2*A q z) :=
    ⟨(huf i (by omega)).trans (ite_eq_left (by omega)),
     (hug i (by omega)).trans (ite_eq_left (by omega))⟩
  change ∀ i<t, f (s+i)=if i+1<t then 2^i*(B q) else -(N q z-(L q z))/2 at hvf
  change ∀ i<t, g (s+i)=if i+1<t then 2^i*(Bn q) else -((2*N q z+1)-(Ln q z))/2 at hvg
  have posV (i : ℕ) (hi : i<t-1) :
      f (s+i)=2^i*(B q) ∧ g (s+i)=2^i*(Bn q) :=
    ⟨(hvf i (by omega)).trans (ite_eq_left (by omega)),
     (hvg i (by omega)).trans (ite_eq_left (by omega))⟩
  change ∀ i<s, f (s+t+i)=if i+1<s then 2^i*(L q z) else -(N q z-(M q z))/2 at hwf
  change ∀ i<s, g (s+t+i)=if i+1<s then 2^i*(Ln q z) else -((2*N q z+1)-(Mn q z))/2 at hwg
  have posW (i : ℕ) (hi : i<s-1) :
      f (s+t+i)=2^i*(L q z) ∧ g (s+t+i)=2^i*(Ln q z) :=
    ⟨(hwf i (by omega)).trans (ite_eq_left (by omega)),
     (hwg i (by omega)).trans (ite_eq_left (by omega))⟩
  change ∀ i<s, f (s+t+s+i)=if i+1<s then 2^i*(M q z) else -(N q z-(A q z))/2 at hxf
  change ∀ i<s, g (s+t+s+i)=if i+1<s then 2^i*(Mn q z) else -((2*N q z+1)-(A q z))/2 at hxg
  have posX (i : ℕ) (hi : i<s-1) :
      f (s+t+s+i)=2^i*(M q z) ∧ g (s+t+s+i)=2^i*(Mn q z) :=
    ⟨(hxf i (by omega)).trans (ite_eq_left (by omega)),
     (hxg i (by omega)).trans (ite_eq_left (by omega))⟩
  change g (s+t+s+s)=A q z at hfresh
  have relU : 2*r*(A q z)=N q z+(B q) := by
    rw [← hq]; dsimp [A,B,L,M,N]; ring
  have relUn : 2*r*(2*A q z)=2*N q z+1+(Bn q) := by
    rw [← hq]; dsimp [A,B,L,M,N,Bn,Ln,Mn]; ring
  have negU : f (s-1)=(B q)-r*(A q z) ∧
      g (s-1)=(Bn q)-r*(2*A q z) := by
    have hf := huf (s-1) (by omega)
    have hg := hug (s-1) (by omega)
    rw [ite_eq_right (by omega),negative_step _ _ _ _ relU] at hf
    rw [ite_eq_right (by omega),negative_step _ _ _ _ relUn] at hg
    simpa only [show 0+(s-1)=s-1 by omega] using And.intro hf hg
  have sumUf := ladder_sum f (0) (s-1) (A q z)
    (by intro i hi; simpa only [Nat.zero_add] using (posU i hi).1)
  have sumUg := ladder_sum g (0) (s-1) (2*A q z)
    (by intro i hi; simpa only [Nat.zero_add] using (posU i hi).2)
  have relV : 2*u*(B q)=N q z+(L q z) := by
    rw [← hz]; dsimp [A,B,L,M,N]; ring
  have relVn : 2*u*(Bn q)=2*N q z+1+(Ln q z) := by
    rw [← hz]; dsimp [A,B,L,M,N,Bn,Ln,Mn]; ring
  have negV : f (s+t-1)=(L q z)-u*(B q) ∧
      g (s+t-1)=(Ln q z)-u*(Bn q) := by
    have hf := hvf (t-1) (by omega)
    have hg := hvg (t-1) (by omega)
    rw [ite_eq_right (by omega),negative_step _ _ _ _ relV] at hf
    rw [ite_eq_right (by omega),negative_step _ _ _ _ relVn] at hg
    simpa only [show s+(t-1)=s+t-1 by omega] using And.intro hf hg
  have sumVf := ladder_sum f (s) (t-1) (B q)
    (by intro i hi; simpa only [Nat.zero_add] using (posV i hi).1)
  have sumVg := ladder_sum g (s) (t-1) (Bn q)
    (by intro i hi; simpa only [Nat.zero_add] using (posV i hi).2)
  have relW : 2*r*(L q z)=N q z+(M q z) := by
    rw [← hq]; dsimp [A,B,L,M,N]; ring
  have relWn : 2*r*(Ln q z)=2*N q z+1+(Mn q z) := by
    rw [← hq]; dsimp [A,B,L,M,N,Bn,Ln,Mn]; ring
  have negW : f (s+t+s-1)=(M q z)-r*(L q z) ∧
      g (s+t+s-1)=(Mn q z)-r*(Ln q z) := by
    have hf := hwf (s-1) (by omega)
    have hg := hwg (s-1) (by omega)
    rw [ite_eq_right (by omega),negative_step _ _ _ _ relW] at hf
    rw [ite_eq_right (by omega),negative_step _ _ _ _ relWn] at hg
    simpa only [show s+t+(s-1)=s+t+s-1 by omega] using And.intro hf hg
  have sumWf := ladder_sum f (s+t) (s-1) (L q z)
    (by intro i hi; simpa only [Nat.zero_add] using (posW i hi).1)
  have sumWg := ladder_sum g (s+t) (s-1) (Ln q z)
    (by intro i hi; simpa only [Nat.zero_add] using (posW i hi).2)
  have relX : 2*r*(M q z)=N q z+(A q z) := by
    rw [← hq]; dsimp [A,B,L,M,N]; ring
  have relXn : 2*r*(Mn q z)=2*N q z+1+(A q z) := by
    rw [← hq]; dsimp [A,B,L,M,N,Bn,Ln,Mn]; ring
  have negX : f (s+t+s+s-1)=(A q z)-r*(M q z) ∧
      g (s+t+s+s-1)=(A q z)-r*(Mn q z) := by
    have hf := hxf (s-1) (by omega)
    have hg := hxg (s-1) (by omega)
    rw [ite_eq_right (by omega),negative_step _ _ _ _ relX] at hf
    rw [ite_eq_right (by omega),negative_step _ _ _ _ relXn] at hg
    simpa only [show s+t+s+(s-1)=s+t+s+s-1 by omega] using And.intro hf hg
  have sumXf := ladder_sum f (s+t+s) (s-1) (M q z)
    (by intro i hi; simpa only [Nat.zero_add] using (posX i hi).1)
  have sumXg := ladder_sum g (s+t+s) (s-1) (Mn q z)
    (by intro i hi; simpa only [Nat.zero_add] using (posX i hi).2)
  have hmod : modulus (s+t+s+s)=N q z := by
    dsimp [modulus,N,q,z]; simp only [pow_add]; ring
  have hmod' : modulus (s+t+s+s+1)=2*N q z+1 := by
    dsimp [modulus,N,q,z]; simp only [pow_add,pow_one]; ring
  have hseed : (seed s t : ℤ)=A q z := by
    dsimp [seed]; push_cast
    dsimp [A,q,z]; simp only [pow_add]; ring
  have hzold := ThreeNegativeEqualOuterSourceBridge.source_zero
    (s+t+s+s) (seed s t) (by omega)
  have hznew := ThreeNegativeEqualOuterSourceBridge.source_zero
    (s+t+s+s+1) (2*seed s t) (by omega)
  dsimp only [f,g] at sumUf sumUg negU sumVf sumVg negV sumWf sumWg negW sumXf sumXg negX
  have hq1 : (1 : ℤ) ≤ q := by
    dsimp [q]
    have := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) hs
    norm_num at this ⊢
    omega
  have hz1 : (1 : ℤ) ≤ z := by
    dsimp [z]
    have := pow_le_pow_right₀ (by norm_num : (1 : ℤ) ≤ 2) ht
    norm_num at this ⊢
    omega
  have hprod : (1 : ℤ) ≤ q*q*z*q := by
    calc
      (1 : ℤ) = 1*1*1*1 := by ring
      _ ≤ q*q*z*q := by gcongr
  refine {
    mod_nonneg := by
      change 0 ≤ q*q*z*q - 1
      omega
    a_nonneg := by dsimp [A]; positivity
    b_nonneg := by dsimp [B]; positivity
    l_nonneg := by dsimp [L]; positivity
    m_nonneg := by dsimp [M]; positivity
    bn_nonneg := by
      have hB0 : (0 : ℤ) ≤ q*(1+q+q*q) := by positivity
      have hB : (1 : ℤ) ≤ B q := by
        dsimp [B]
        nlinarith
      change 0 ≤ 2*B q - 1
      omega
    ln_nonneg := by dsimp [Ln,L,q,z]; ring_nf; positivity
    mn_nonneg := by dsimp [Mn,M,q,z]; ring_nf; positivity
    posU := posU, posV := posV, posW := posW, posX := posX
    packetU := by rw [sumUf,sumUg,negU.1,negU.2]; dsimp only [r,u]; exact ⟨by ring,by ring⟩
    stepU := by rw [negU.1,negU.2]; constructor <;> nlinarith only [relU,relUn]
    packetV := by rw [sumVf,sumVg,negV.1,negV.2]; dsimp only [r,u]; exact ⟨by ring,by ring⟩
    stepV := by rw [negV.1,negV.2]; constructor <;> nlinarith only [relV,relVn]
    packetW := by rw [sumWf,sumWg,negW.1,negW.2]; dsimp only [r,u]; exact ⟨by ring,by ring⟩
    stepW := by rw [negW.1,negW.2]; constructor <;> nlinarith only [relW,relWn]
    packetX := by rw [sumXf,sumXg,negX.1,negX.2]; dsimp only [r,u]; exact ⟨by ring,by ring⟩
    stepX := by rw [negX.1,negX.2]; constructor <;> nlinarith only [relX,relXn]
    fresh := hfresh
    totalOld := by
      change ((List.range (s+t+s+s)).map
        (fun i => centered (N q z) ((2 : ℤ)^i * A q z))).sum = 0
      simpa [hmod,hseed] using hzold
    totalNew := by
      change ((List.range (s+t+s+s+1)).map
        (fun i => centered (2*N q z+1) ((2 : ℤ)^i * (2*A q z)))).sum = 0
      simpa [hmod',Nat.cast_mul,Nat.cast_ofNat,hseed] using hznew }

private theorem positive_pair (f g : ℕ → ℤ) (H J : ℤ) (off len : ℕ)
    (hH : 0 ≤ H) (hJ : 0 ≤ J)
    (hrow : ∀ i<len, f (off+i)=2^i*H ∧ g (off+i)=2^i*J) :
    ∀ i ∈ List.range' off len, 0 ≤ f i ∧ 0 ≤ g i := by
  intro i hi
  have hi' := List.mem_range'.mp hi
  rw [show i=off+(i-off) by omega,(hrow (i-off) (by omega)).1,
    (hrow (i-off) (by omega)).2]
  constructor <;> positivity

private theorem gates_of_margins {D C m1 d1 m2 d2 m3 d3 m4 d4 S1 S2 S3 J1 J2 J3 J4 : ℤ}
    (hC : 0 ≤ C) (hD : D ≤ 2*C+1)
    (hs1 : m1+d1=S1) (hs2 : S1+m2+d2=S2)
    (hs3 : S2+m3+d3=S3) (hs4 : S3+m4+d4=0)
    (hd1 : 2*d1=J1-D) (hd2 : 2*d2=J2-D)
    (hd3 : 2*d3=J3-D) (hd4 : 2*d4=J4-D)
    (hm1 : Margin S1 J1) (hm2 : Margin S2 J2)
    (hm3 : Margin S3 J3) (hm4 : Margin 0 J4) :
    Gates C m1 d1 m2 d2 m3 d3 m4 d4 := by
  dsimp only [Margin] at hm1 hm2 hm3 hm4
  dsimp only [Gates]
  refine ⟨hC,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> omega

private theorem native_inventory (s t : ℕ) (hs : 2 ≤ s) (ht : 2 ≤ t) :
    ((List.range' 0 (s-1)++[s-1])++
      (List.range' s (t-1)++[s+t-1])++
      (List.range' (s+t) (s-1)++[s+t+s-1])++
      (List.range' (s+t+s) (s-1)++[s+t+s+s-1]))=
      List.range (s+t+s+s) := by
  have merge (o n : ℕ) (hn : 1 ≤ n) :
      List.range' o (n-1)++[o+n-1]=List.range' o n := by
    simpa only [show o+(n-1)=o+n-1 by omega,show n-1+1=n by omega] using
      (List.range'_1_concat (s:=o) (n:=n-1)).symm
  have hU : List.range' 0 (s-1)++[s-1]=List.range' 0 s := by
    simpa only [Nat.zero_add] using merge 0 s (by omega)
  rw [hU,merge s t (by omega),
    merge (s+t) s (by omega),merge (s+t+s) s (by omega)]
  have h1 := List.range'_append_1 (s:=0) (m:=s) (n:=t)
  have h2 := List.range'_append_1 (s:=0) (m:=s+t) (n:=s)
  have h3 := List.range'_append_1 (s:=0) (m:=s+t+s) (n:=s)
  simp only [Nat.zero_add] at h1 h2 h3
  rw [h1,h2,h3,←List.range_eq_range']

private theorem realize (s t cut : ℕ) (hs : 2 ≤ s) (ht : 2 ≤ t)
    (pre post : List ℕ) (hlen : pre.length=cut)
    (hp : (pre++post).Perm (List.range (s+t+s+s)))
    (hold : InStrip (oldValue s t) (N (2^s) (2^t)/2) 0 (pre++post))
    (hnew : InStrip (newValue s t) (N (2^s) (2^t)) 0 (pre++(s+t+s+s)::post)) :
    ∃ sigma : List (Fin (s+t+s+s)),
      OriginalOrder (s+t+s+s) (seed s t) sigma ∧
      OriginalOrder (s+t+s+s+1) (2*seed s t) (earWord (s+t+s+s) sigma cut) := by
  let k := s+t+s+s
  let a := seed s t
  let q : ℤ := 2^s
  let z : ℤ := 2^t
  have hk : 0<k := by dsimp [k]; omega
  have rows := native s t hs ht
  have hmod : modulus k=N q z := by
    dsimp [k,modulus,N,q,z]; simp only [pow_add]; ring
  have hmod' : modulus (k+1)=2*N q z+1 := by
    dsimp [k,modulus,N,q,z]; simp only [pow_add,pow_one]; ring
  have hseed : (a:ℤ)=A q z := by
    dsimp [a,seed]; push_cast
    dsimp [A,q,z]; simp only [pow_add]; ring
  change InStrip (fun i => centered (N (2^s) (2^t)) ((2 : ℤ)^i * A (2^s) (2^t)))
      (N (2^s) (2^t)/2) 0 (pre++post) at hold
  change InStrip (fun i => centered (2*N (2^s) (2^t)+1)
      ((2 : ℤ)^i * (2*A (2^s) (2^t))))
      (N (2^s) (2^t)) 0 (pre++(s+t+s+s)::post) at hnew
  have old : OriginalOrder k a ((pre++post).map (label k hk)) := by
    apply lift_order k a hk (pre++post) hp
    · simpa [hmod,hseed] using hold
    · exact ThreeNegativeEqualOuterSourceBridge.source_zero k a (by dsimp [k]; omega)
  have hp' : (pre++k::post).Perm (List.range (k+1)) := by
    have hreorder : (pre++k::post).Perm ((pre++post)++[k]) := by
      simpa only [List.append_assoc] using
        (List.perm_append_singleton k post).symm.append_left pre
    exact hreorder.trans (by simpa only [List.range_succ] using hp.append_right [k])
  have new : OriginalOrder (k+1) (2*a)
      ((pre++k::post).map (label (k+1) (by omega))) := by
    apply lift_order (k+1) (2*a) (by omega) (pre++k::post) hp'
    · have hhalf : (2*N q z+1)/2=N q z := by omega
      simpa [hmod',Nat.cast_mul,Nat.cast_ofNat,hseed,hhalf] using hnew
    · exact ThreeNegativeEqualOuterSourceBridge.source_zero (k+1) (2*a) (by dsimp [k]; omega)
  refine ⟨(pre++post).map (label k hk),old,?_⟩
  rw [marked_word k cut hk pre post hlen hp]
  exact new

end D5.S3.Combinatorics.Circle.FourNegative.EqualFirstTwoLast
