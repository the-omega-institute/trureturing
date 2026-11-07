/- GID: D5/S3/Combinatorics/Circle/FourNegative/OppositeFirstThirdMaximum/Arithmetic
   generality: I
   mirror-B: none(waiver:private-consumed-endpoint-implementation)
   mirror-E: none(waiver:private-consumed-endpoint-implementation)
   anchors: [mathlib/module/Mathlib.Data.Int.ModEq]
   utility: none
   digest: Unbounded quotient and residue estimates for the two original opposite-maximum orders. -/
import D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Endpoint

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000
namespace D5.S3.Combinatorics.Circle.FourNegative.OppositeFirstThirdMaximum

private def C (x y : ℤ) : ℤ := 1+y*(x+1)
private def A (x y : ℤ) : ℤ := x*C x y+1
private def B (x y t : ℤ) : ℤ := 1+t*(x+1)+x*y*t
private def L (x t : ℤ) : ℤ := (x+1)*(1+x*t)
private def K (x y t : ℤ) : ℤ := C x y+x*y*t
private def SU (x y t : ℤ) : ℤ := 2*B x y t-1
private def SV (x t : ℤ) : ℤ := 2*L x t-(x+1)
private def SW (x y t : ℤ) : ℤ := 2*K x y t-C x y

/-- Doubled mixed margins: old upper/new lower before the ear, and old lower/new upper after it. -/
private def gates (x y t eta m : ℤ) (early : Bool) : Fin 6 → ℤ :=
  if early then
    ![2*A x y-B x y t-2*m*K x y t,
      2*m*SW x y t+2*B x y t-3*A x y-1,
      2*(B x y t-K x y t),2*(SW x y t-B x y t),
      (eta+2)*B x y t-K x y t-L x t,
      2*SV x t+SW x y t-1-(eta+2)*SU x y t]
  else
    ![2*L x t-K x y t-eta*B x y t,
      2*(eta*B x y t-L x t+K x y t)+x-y*(x+1)-eta,
      2*B x y t-K x y t,2*(SW x y t-SU x y t),
      2*A x y+B x y t-2*(m+1)*K x y t,
      (x-2*(m+1))*C x y-2*(2*A x y+B x y t-1-2*(m+1)*K x y t)]

private theorem common_bounds (x y t : ℤ) (hy : 4≤y) (ht : 4≤t)
    (hxt : 2*t≤x) (hxy : 2*y≤x) :
    0<C x y ∧ 0<K x y t ∧ t*C x y<K x y t ∧
    K x y t<(t+1)*C x y ∧ B x y t<A x y ∧ K x y t<L x t := by
  have hx : 8≤x := by omega
  have hx0 : 0≤x := by omega
  have hy0 : 0≤y := by omega
  have ht0 : 0≤t := by omega
  have hxt0 : 0≤x-2*t := by omega
  have hxy0 : 0≤x-2*y := by omega
  have hym1 : 0≤y-1 := by omega
  have htm1 : 0≤t-1 := by omega
  have hC : 0<C x y := by dsimp [C]; positivity
  have hK : 0<K x y t := by dsimp [K]; positivity
  have hgap : K x y t-t*C x y=
      (x-2*t)*y+t*(y-1)+y+1 := by dsimp [K,C]; ring
  have hg0 : 0≤(x-2*t)*y := mul_nonneg (by omega) (by omega)
  have hg1 : 0<t*(y-1) := mul_pos (by omega) (by omega)
  have hkupper : (t+1)*C x y-K x y t=t*(y+1) := by dsimp [K,C]; ring
  have hab : A x y-B x y t=
      x*y*(x-2*t)+x*t*(y-1)+x*y+x-t := by dsimp [A,B,C]; ring
  have hab0 : 0≤x*y*(x-2*t) := by positivity
  have hab1 : 0≤x*t*(y-1) := by positivity
  have hab2 : 0≤x*y := by positivity
  have hlk : L x t-K x y t=
      x*t*(x-2*y)+x*y*(t-1)+x*t+x-y := by dsimp [L,K,C]; ring
  have hlk0 : 0≤x*t*(x-2*y) := by positivity
  have hlk1 : 0≤x*y*(t-1) := by positivity
  have hlk2 : 0≤x*t := by positivity
  exact ⟨hC,hK,by omega,by nlinarith,by omega,by omega⟩

private theorem quotient_data (E D : ℤ) (hE : 0≤E) (hD : 0<D) :
    0≤E/D ∧ 0≤E%D ∧ E%D<D ∧ E=D*(E/D)+E%D := by
  exact ⟨Int.ediv_nonneg hE hD.le,Int.emod_nonneg E (ne_of_gt hD),
    Int.emod_lt_of_pos E hD,by nlinarith only [Int.emod_add_mul_ediv E D]⟩

private theorem early_quotient (x y t g eta : ℤ)
    (hy : 4≤y) (ht : 8≤t) (hty : 2*y≤t)
    (hg : 2≤g) (hxg : x=g*t) (hxe : x=eta*y)
    (hdyadic : g=2 ∨ g=4 ∨ 8≤g) :
    ∃ m : ℤ, 0≤m ∧ m≤g-1 ∧ ∀ i : Fin 6, 0≤gates x y t eta m true i := by
  have hxt : 2*t≤x := by nlinarith
  have hxy : 2*y≤x := by omega
  have hx : 16≤x := by omega
  have heta : 4≤eta := by nlinarith
  have hx0 : 0≤x := by omega
  have hy0 : 0≤y := by omega
  have ht0 : 0≤t := by omega
  have hg0 : 0≤g := by omega
  have heta0 : 0≤eta := by omega
  have hetam1 : 0≤eta-1 := by omega
  have hym1 : 0≤y-1 := by omega
  have htm1 : 0≤t-1 := by omega
  have htmy : 0≤t-y := by omega
  have h2tmy : 0≤2*t-y := by omega
  obtain ⟨hC,hK,hKlo,hKhi,hBA,hKL⟩ := common_bounds x y t hy (by omega) hxt hxy
  have hgK : A x y<g*K x y t := by
    have hgap : 1≤K x y t-t*C x y := by omega
    have hm := mul_le_mul_of_nonneg_left hgap (show 0≤g by omega)
    have he : g*(t*C x y)=(A x y-1) := by rw [←mul_assoc,←hxg]; dsimp [A]; ring
    nlinarith only [hm,he,hg]
  let E := 2*A x y-B x y t-1
  let m := E/(2*K x y t)
  let R := E%(2*K x y t)
  have hApos : 0<A x y := by dsimp [A]; positivity
  have hBpos : 0<B x y t := by dsimp [B]; positivity
  have hE : 0≤E := by dsimp [E]; omega
  obtain ⟨hm0,hR0,hRlt,hdiv⟩ := quotient_data E (2*K x y t) hE (by omega)
  change 0≤m at hm0
  change 0≤R at hR0
  change R<2*K x y t at hRlt
  change E=2*K x y t*m+R at hdiv
  have hmcap : m≤g-1 := by dsimp [E] at hdiv; nlinarith only [hdiv,hR0,hgK,hBpos,hK]
  have lambda : 0≤2*m*SW x y t+2*B x y t-3*A x y-1 := by
    have hid : 2*m*SW x y t+2*B x y t-3*A x y-1=
        (x-2*m)*C x y-2*R-2 := by
      dsimp [E] at hdiv
      dsimp [SW,K,A] at hdiv ⊢
      nlinarith only [hdiv]
    rcases hdyadic with hg2|hg4|hg8
    · have hxe2 : x=2*t := by simpa only [hg2] using hxg
      have hlow : 2*K x y t≤E := by
        have he : E-2*K x y t=2*t^2*(y-1)+3*t-2*y-2 := by
          dsimp [E,A,B,K,C]; rw [hxe2]; ring
        have hh : 0≤2*t^2*(y-1) := by positivity
        omega
      have hm1 : m=1 := by rw [hg2] at hmcap; nlinarith only [hdiv,hRlt,hlow,hm0,hmcap,hK]
      have he : 2*m*SW x y t+2*B x y t-3*A x y-1=2*(2*t-y)*(t-1) := by
        rw [hm1,hxe2]; dsimp [SW,K,A,B,C]; ring
      rw [he]
      positivity
    · have hxe4 : x=4*t := by simpa only [hg4] using hxg
      have hlow : 6*K x y t≤E := by
        have he : E-6*K x y t=4*t*((t-4)*y-t)+7*t-6*y-6 := by
          dsimp [E,A,B,K,C]; rw [hxe4]; ring
        have hh : 3*t-16≤(t-4)*y-t := by nlinarith only [mul_nonneg (show 0≤t-4 by omega) (show 0≤y-4 by omega)]
        have hmul := mul_le_mul_of_nonneg_left hh (show 0≤4*t by omega)
        have hsign : 0≤3*t-16 := by omega
        have hh' : 0≤4*t*(3*t-16) := by positivity
        omega
      have hm3 : m=3 := by rw [hg4] at hmcap; nlinarith only [hdiv,hRlt,hlow,hm0,hmcap,hK]
      have he : 2*m*SW x y t+2*B x y t-3*A x y-1=
          2*(4*t^2*(y+1)+t*(6*y-5)+3*y+2) := by
        rw [hm3,hxe4]; dsimp [SW,K,A,B,C]; ring
      rw [he]
      have hy6 : 0≤6*y-5 := by omega
      positivity
    · rw [hid]
      have hbr : 0≤x-2*g-4*t-2 := by
        nlinarith only [hxg,mul_nonneg (show 0≤g-8 by omega) (show 0≤t-2 by omega),ht]
      have he : (x-2*g+2)*C x y-4*K x y t=
          (x-2*g-4*t-2)*C x y+4*t*(y+1) := by dsimp [K,C]; ring
      have hmul := mul_le_mul_of_nonneg_right (show 2*m≤2*g-2 by omega) hC.le
      have hp : 0≤(x-2*g-4*t-2)*C x y+4*t*(y+1) := by positivity
      nlinarith only [hRlt,hmul,he,hp]
  have hBK : 0≤B x y t-K x y t := by
    have he : B x y t-K x y t=(x+1)*(t-y) := by dsimp [B,K,C]; ring
    rw [he]; positivity
  have hSWB : 0≤SW x y t-B x y t := by
    have he : SW x y t-B x y t=t*(x*(y-1)-1)+y*(x+1) := by dsimp [SW,K,B,C]; ring
    rw [he]
    have hp : 0≤x*(y-1)-1 := by nlinarith
    positivity
  have hVB : 0≤eta*B x y t-L x t := by
    have he : eta*B x y t-L x t=(eta-1)*(x*t+1)+eta*(t-y) := by
      rw [hxe]; dsimp [B,L]; ring
    rw [he]; positivity
  have hVhead : 0≤2*SV x t+SW x y t-1-(eta+2)*SU x y t := by
    have hinner : 8≤x-y-eta := by nlinarith only [hxe,mul_nonneg (show 0≤eta-4 by omega) (show 0≤y-1 by omega),hy]
    have hex : eta+2≤x := by nlinarith only [hxe,mul_nonneg (show 0≤eta-2 by omega) (show 0≤y-1 by omega),hy]
    have hbr : 0≤x*(x-y-eta)-eta-2 := by nlinarith only [mul_le_mul_of_nonneg_left hinner (show 0≤x by omega),hex,hx]
    have he : 2*SV x t+SW x y t-1-(eta+2)*SU x y t=
        2*t*(x*(x-y-eta)-eta-2)+2*x+y*(x+1)-eta := by
      rw [hxe]; dsimp [SV,SW,SU,L,K,B,C]; ring
    have hp : 0≤2*t*(x*(x-y-eta)-eta-2) := by positivity
    have hq : 0≤y*(x+1) := by positivity
    rw [he]; omega
  refine ⟨m,hm0,hmcap,?_⟩
  intro i
  fin_cases i <;> dsimp [gates]
  · dsimp [E] at hdiv; nlinarith only [hdiv,hR0]
  · exact lambda
  · omega
  · omega
  · nlinarith only [hVB,hBK,hBpos]
  · exact hVhead

private theorem late_quotient (x y t g eta : ℤ)
    (hy : 4≤y) (ht : 4≤t) (hyt : 4*t≤y)
    (hg : 8≤g) (heta : 2≤eta) (hxg : x=g*t) (hxe : x=eta*y)
    (htdyadic : t=4 ∨ 8≤t) :
    ∃ m : ℤ, 0≤m ∧ m≤g-1 ∧ ∀ i : Fin 6, 0≤gates x y t eta m false i := by
  have hxt : 2*t≤x := by nlinarith
  have hxy : 2*y≤x := by nlinarith
  have hx : 32≤x := by nlinarith
  have hy16 : 16≤y := by omega
  have hx0 : 0≤x := by omega
  have hy0 : 0≤y := by omega
  have ht0 : 0≤t := by omega
  have hg0 : 0≤g := by omega
  have hg8 : 0≤g-8 := by omega
  have heta0 : 0≤eta := by omega
  have hetam1 : 0≤eta-1 := by omega
  have hetam2 : 0≤eta-2 := by omega
  have hym1 : 0≤y-1 := by omega
  have htm1 : 0≤t-1 := by omega
  have hym2t : 0≤y-2*t := by omega
  have hy2 : 0≤y^2-1 := by nlinarith
  have hxmt : 0≤x-t-1 := by omega
  obtain ⟨hC,hK,hKlo,hKhi,hBA,hKL⟩ := common_bounds x y t hy ht hxt hxy
  have hAK : K x y t<A x y := by
    have hh : 0≤(x-t-1)*C x y := by positivity
    dsimp [A] at *
    nlinarith only [hh,hKhi]
  have hBK : B x y t+1≤K x y t := by
    have he : K x y t-B x y t=(x+1)*(y-t) := by dsimp [K,B,C]; ring
    have hytpos : 0<y-t := by omega
    have hp : 0<(x+1)*(y-t) := by positivity
    omega
  have hgK : A x y<g*K x y t := by
    have hgap : 1≤K x y t-t*C x y := by omega
    have hm := mul_le_mul_of_nonneg_left hgap (show 0≤g by omega)
    have he : g*(t*C x y)=A x y-1 := by rw [←mul_assoc,←hxg]; dsimp [A]; ring
    nlinarith only [hm,he,hg]
  let E := 2*A x y+B x y t-1
  let h := E/(2*K x y t)
  let R := E%(2*K x y t)
  have hApos : 0<A x y := by dsimp [A]; positivity
  have hBpos : 0<B x y t := by dsimp [B]; positivity
  have hE : 0≤E := by dsimp [E]; omega
  obtain ⟨hh0,hR0,hRlt,hdiv⟩ := quotient_data E (2*K x y t) hE (by omega)
  change 0≤h at hh0
  change 0≤R at hR0
  change R<2*K x y t at hRlt
  change E=2*K x y t*h+R at hdiv
  have hh1 : 1≤h := by dsimp [E] at hdiv; nlinarith only [hdiv,hRlt,hAK,hBpos,hK]
  have hhcap : h≤g := by dsimp [E] at hdiv; nlinarith only [hdiv,hR0,hgK,hBK,hK]
  have lambda : 0≤(x-2*h)*C x y-2*R := by
    rcases htdyadic with ht4|ht8
    · have hx4 : x=4*g := by simpa only [ht4,mul_comm] using hxg
      have hsharp : h≤g-2 := by
        have he : 2*(g-1)*K x y t-E=
            2*((7*y-92)+(33*y-11)*(g-8)+4*y*(g-8)^2) := by
          dsimp [E,A,B,K,C]; rw [ht4,hx4]; ring
        have hsign : 0≤33*y-11 := by omega
        have hp : 0≤(33*y-11)*(g-8) := by positivity
        have hq : 0≤4*y*(g-8)^2 := by positivity
        have hpos : 0<2*(g-1)*K x y t-E := by omega
        nlinarith only [hpos,hdiv,hR0,hK]
      have he : (x-2*g+4)*C x y-4*K x y t+2=
          (2*g-16)*C x y+16*(y+1)+2 := by
        rw [ht4,hx4]; dsimp [K,C]; ring
      have hmul := mul_le_mul_of_nonneg_right (show 2*h≤2*g-4 by omega) hC.le
      have hsign : 0≤2*g-16 := by omega
      have hp : 0≤(2*g-16)*C x y+16*(y+1)+2 := by positivity
      nlinarith only [hRlt,hmul,he,hp]
    · have hbr : 0≤x-2*g-4*t-4 := by
        nlinarith only [hxg,mul_nonneg (show 0≤g-8 by omega) (show 0≤t-2 by omega),ht8]
      have he : (x-2*g)*C x y-4*K x y t+2=
          (x-2*g-4*t-4)*C x y+4*t*(y+1)+2 := by dsimp [K,C]; ring
      have hmul := mul_le_mul_of_nonneg_right (show 2*h≤2*g by omega) hC.le
      have hp : 0≤(x-2*g-4*t-4)*C x y+4*t*(y+1)+2 := by positivity
      nlinarith only [hRlt,hmul,he,hp]
  have hhead : 0≤2*L x t-K x y t-eta*B x y t := by
    have he : 2*L x t-K x y t-eta*B x y t=
        eta*t*(eta-2)*y*(y-1)+eta*(t-1)*(y^2-1)+2*eta*(y-1)-y+1 := by
      rw [hxe]; dsimp [L,K,B,C]; ring
    have hp : 0≤eta*t*(eta-2)*y*(y-1) := by positivity
    have hq : 0≤eta*(t-1)*(y^2-1) := by positivity
    have hr : 0≤2*eta*(y-1)-y+1 := by nlinarith
    rw [he]; omega
  have hVB : 0≤eta*B x y t-L x t := by
    have he : eta*B x y t-L x t=
        (eta-2)*x+2*eta-1+(t-1)*((eta-1)*x+eta) := by
      rw [hxe]; dsimp [B,L]; ring
    have hp : 0≤(eta-2)*x := by positivity
    have hq : 0≤(t-1)*((eta-1)*x+eta) := by positivity
    rw [he]; omega
  have hnewV : 0≤2*(eta*B x y t-L x t+K x y t)+x-y*(x+1)-eta := by
    have he : 2*K x y t+x-y*(x+1)-eta=2+y*(x+1)+2*x*y*t+x-eta := by dsimp [K,C]; ring
    have hex : eta≤x := by nlinarith only [hxe,mul_nonneg (show 0≤eta by omega) (show 0≤y-1 by omega)]
    have hp : 0≤y*(x+1) := by positivity
    have hq : 0≤2*x*y*t := by positivity
    nlinarith only [he,hVB,hex,hp,hq]
  have htwoBK : 0≤2*B x y t-K x y t := by
    have he : 2*B x y t-K x y t=2*t*(x+1)+y*(x*t-(x+1))+1 := by dsimp [B,K,C]; ring
    have hp : 0≤x*t-(x+1) := by nlinarith
    rw [he]; positivity
  have hnewW : 0≤SW x y t-SU x y t := by
    have he : SW x y t-SU x y t=(x+1)*(y-2*t) := by dsimp [SW,SU,K,B,C]; ring
    rw [he]; positivity
  refine ⟨h-1,by omega,by omega,?_⟩
  intro i
  fin_cases i <;> dsimp [gates]
  · exact hhead
  · exact hnewV
  · exact htwoBK
  · omega
  · dsimp [E] at hdiv; nlinarith only [hdiv,hR0]
  · have he : 2*A x y+B x y t-1-2*((h-1)+1)*K x y t=R := by dsimp [E] at hdiv; nlinarith only [hdiv]
    rw [he]
    convert lambda using 1 <;> ring

private theorem pow_factor (a b : ℕ) (h : b≤a) :
    (2:ℤ)^a=(2:ℤ)^(a-b)*2^b := by rw [←pow_add,Nat.sub_add_cancel h]

private theorem choose_mask (a b d : ℕ) (hb : 2≤b) (hd : 2≤d)
    (hba : b<a) (hda : d<a) (hreg : b<d ∨ d+2≤b) :
    ∃ m : ℕ, m<2^(a-1) ∧ ∀ i : Fin 6,
      0≤gates (2^a) (2^b) (2^d) (2^(a-b)) m (decide (b<d)) i := by
  let x : ℤ := 2^a
  let y : ℤ := 2^b
  let t : ℤ := 2^d
  let g : ℤ := 2^(a-d)
  let eta : ℤ := 2^(a-b)
  have hy : 4≤y := by dsimp [y]; exact_mod_cast (Nat.pow_le_pow_right (by decide : 1≤2) hb)
  have ht : 4≤t := by dsimp [t]; exact_mod_cast (Nat.pow_le_pow_right (by decide : 1≤2) hd)
  have hg : 2≤g := by dsimp [g]; exact_mod_cast (Nat.pow_le_pow_right (by decide : 1≤2) (show 1≤a-d by omega))
  have heta : 2≤eta := by dsimp [eta]; exact_mod_cast (Nat.pow_le_pow_right (by decide : 1≤2) (show 1≤a-b by omega))
  have hxg : x=g*t := pow_factor a d (by omega)
  have hxe : x=eta*y := pow_factor a b (by omega)
  have hhalf : 2*(2:ℤ)^(a-1)=x := by
    calc
      2*(2:ℤ)^(a-1)=(2:ℤ)^((a-1)+1) := by rw [pow_succ]; ring
      _ = x := by dsimp [x]; congr 1; omega
  have finish (m : ℤ) (hm0 : 0≤m) (hmcap : m≤g-1)
      (hw : ∀ i : Fin 6, 0≤gates x y t eta m (decide (b<d)) i) :
      ∃ m : ℕ, m<2^(a-1) ∧ ∀ i : Fin 6,
        0≤gates (2^a) (2^b) (2^d) (2^(a-b)) m (decide (b<d)) i := by
    have hmg : 2*m<x := by nlinarith only [hxg,hmcap,mul_nonneg (show 0≤g by omega) (show 0≤t-2 by omega)]
    refine ⟨m.toNat,?_,?_⟩
    · have hmhalf : (m.toNat:ℤ)<(2:ℤ)^(a-1) := by rw [Int.toNat_of_nonneg hm0]; omega
      exact_mod_cast hmhalf
    · simpa only [Int.toNat_of_nonneg hm0] using hw
  by_cases hbd : b<d
  · have hty : 2*y≤t := by
      have hp : (2:ℤ)^(b+1)≤2^d := by exact_mod_cast (Nat.pow_le_pow_right (by decide : 1≤2) (show b+1≤d by omega))
      simpa [pow_succ,y,t,mul_comm] using hp
    have ht8 : 8≤t := by omega
    have hdyadic : g=2 ∨ g=4 ∨ 8≤g := by
      by_cases h1 : a-d=1
      · left; simp [g,h1]
      by_cases h2 : a-d=2
      · right; left; simp [g,h2]
      right; right
      dsimp [g]
      exact_mod_cast (Nat.pow_le_pow_right (by decide : 1≤2) (show 3≤a-d by omega))
    obtain ⟨m,hm0,hmcap,hw⟩ := early_quotient x y t g eta hy ht8 hty hg hxg hxe hdyadic
    exact finish m hm0 hmcap (by simpa [hbd] using hw)
  · have hdb : d+2≤b := by rcases hreg with h|h <;> omega
    have hyt : 4*t≤y := by
      have hp : (2:ℤ)^(d+2)≤2^b := by exact_mod_cast (Nat.pow_le_pow_right (by decide : 1≤2) hdb)
      simpa [pow_add,y,t,mul_comm] using hp
    have hg8 : 8≤g := by
      dsimp [g]
      exact_mod_cast (Nat.pow_le_pow_right (by decide : 1≤2) (show 3≤a-d by omega))
    have htdyadic : t=4 ∨ 8≤t := by
      by_cases hd2 : d=2
      · left; simp [t,hd2]
      right; dsimp [t]
      exact_mod_cast (Nat.pow_le_pow_right (by decide : 1≤2) (show 3≤d by omega))
    obtain ⟨m,hm0,hmcap,hw⟩ := late_quotient x y t g eta hy ht hyt hg8 heta hxg hxe htdyadic
    exact finish m hm0 hmcap (by simpa [hbd] using hw)

end D5.S3.Combinatorics.Circle.FourNegative.OppositeFirstThirdMaximum
