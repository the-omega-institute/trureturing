/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakHighD/Parameters
   generality: I
   mirror-B: none(waiver:physical-construction-component)
   mirror-E: none(waiver:physical-construction-component)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Exact exponent dictionary binds the unbounded selector to the original paired sources. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD.Exhaustion
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD.SourceCertificate

/-! Exact HighD construction on unrestricted natural exponents. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3000000
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD
open D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm
open private dyadic_selection
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD.Exhaustion
open private source_certificate rowSeams rowHeads rowBase
  from D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD.SourceCertificate
open private charge chain_values new_base_bounds from D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source
open D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm (base newBase)

private theorem physical_selection (a b c d : ℕ)
    (ha : 3≤a) (hac : a<c) (hcd : c+2≤d) (hdb : d<b) :
    ∃ v m M : ℕ, ∃ before : Bool,
      1≤v ∧ v≤2^(d-1) ∧ M<2^(b-1) ∧ Submask m M ∧
      ∀ (side : Bool) (r : Fin 4),
        0≤rowSeams a b c d v m M before side r ∧
        rowSeams a b c d v m M before side r≤rowHeads a b c d side r-1 := by
  let x : ℤ:=2^a
  let p : ℤ:=2^(d-c)
  let q : ℤ:=2^(c-a)
  let h : ℤ:=2^(b-d-1)
  have hZ : Z x q=(2:ℤ)^c := by
    dsimp [Z,x,q]
    rw [←pow_add]
    congr 1
    omega
  have hT : T x p q=(2:ℤ)^d := by
    dsimp [T,x,p,q]
    rw [←pow_add,←pow_add]
    congr 1
    omega
  have hY : Y x p q h=(2:ℤ)^b := by
    dsimp [Y,h]
    rw [hT]
    calc
      2*2^(b-d-1)*2^d=(2:ℤ)^((b-d-1)+d+1) := by rw [pow_add,pow_add,pow_one]; ring
      _=2^b := by congr 1; omega
  have bo : base a b c d=![A x p q h,B x p q h,L x p q,K x p q h] := by
    funext r
    fin_cases r <;> dsimp [base,A,B,L,K]
    all_goals simp only [hY,hZ,hT] <;> (try dsimp [x]) <;> ring
  have bn : newBase a b c d=![2*A x p q h,SU x p q h,SV x p q,SW x p q h] := by
    funext r
    fin_cases r <;> simp [newBase,charge,bo,SU,SV,SW,hY,hZ] <;> ring
  obtain ⟨v,m,M,before,hsub,hbounds⟩:=dyadic_selection a (d-c) (c-a) (b-d-1)
    ha (by omega) (by omega)
  have hbounds' : rowBounds x p q h v m M before := hbounds
  have hv0 : 1≤v := by exact_mod_cast hbounds'.2.1
  have hdp : (2:ℤ)^d=2*2^(d-1) := by
    calc
      (2:ℤ)^d=2^((d-1)+1) := by congr 1; omega
      _=2*2^(d-1) := by rw [pow_succ]; ring
  have hbp : (2:ℤ)^b=2*2^(b-1) := by
    calc
      (2:ℤ)^b=2^((b-1)+1) := by congr 1; omega
      _=2*2^(b-1) := by rw [pow_succ]; ring
  have hv : v≤2^(d-1) := by
    have hh:=hbounds'.2.2.1
    rw [hT,hdp] at hh
    have hz : (v:ℤ)≤(2:ℤ)^(d-1) := by omega
    exact_mod_cast hz
  have hM : M<2^(b-1) := by
    have hh:=hbounds'.2.2.2.2
    rw [hY,hbp] at hh
    have hz : (M:ℤ)<(2:ℤ)^(b-1) := by omega
    exact_mod_cast hz
  have seamo : rowSeams a b c d v m M before false=oldEnds x p q h v m M := by
    funext r
    fin_cases r <;> cases before <;>
      simp [rowSeams,rowBase,bo,oldEnds] <;> ring
  have seamn : rowSeams a b c d v m M before true=newEnds x p q h v m M before := by
    funext r
    fin_cases r <;> cases before <;>
      simp [rowSeams,rowBase,bo,bn,newEnds] <;> ring
  have heado : rowHeads a b c d false=oldHeads x p q h := by simp [rowHeads,rowBase,bo,oldHeads]
  have headn : rowHeads a b c d true=newHeads x p q h := by simp [rowHeads,rowBase,bo,bn,newHeads]
  refine ⟨v,m,M,before,hv0,hv,hM,hsub,?_⟩
  intro side r
  by_cases hr : r.val<3
  · let rr : Fin 3:=⟨r.val,hr⟩
    have he : rr.castSucc=r := Fin.ext rfl
    have hh:=hbounds'.1 rr
    cases side
    · rw [seamo,heado]
      simpa only [he] using And.intro hh.1 hh.2.1
    · rw [seamn,headn]
      simpa only [he] using hh.2.2
  · have he : r=3 := Fin.ext (by omega)
    subst r
    have ho:=(chain_values a b c d (by omega) (by omega) (by omega) (by omega)).1 2
    have hn:=new_base_bounds a b c d (by omega) (by omega) (by omega) (by omega) 2
    cases side <;> simp [rowSeams,rowHeads,rowBase] <;> omega

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD
