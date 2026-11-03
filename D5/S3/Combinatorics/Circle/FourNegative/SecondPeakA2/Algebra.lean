/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/Algebra
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/SecondPeakA2/Algebra
   mirror-E: none(waiver:physical-source-family-registration)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Original a2 near-b construction: Algebra and its physical source consumer. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakHighD.LowBits
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2.IntegerCover

set_option autoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2
open D5.S3.Combinatorics.Circle.FourNegative

def z (q : ℤ) := 4*q
def t (p q : ℤ) := 4*p*q
def y (p q h : ℤ) := 8*h*p*q
abbrev A (p q h : ℤ) := SecondPeakHighD.A 4 p q h
abbrev B (p q h : ℤ) := SecondPeakHighD.B 4 p q h
abbrev L (p q : ℤ) := SecondPeakHighD.L 4 p q
abbrev K (p q h : ℤ) := SecondPeakHighD.K 4 p q h
abbrev SU (p q h : ℤ) := SecondPeakHighD.SU 4 p q h
abbrev SV (p q : ℤ) := SecondPeakHighD.SV 4 p q
abbrev SW (p q h : ℤ) := SecondPeakHighD.SW 4 p q h
def Q (q : ℤ) := 4*q+1
def D (p q h : ℤ) := 5*A p q h-8*h*L p q
def R (p q h v m : ℤ) := v*A p q h+m*L p q-K p q h

def First (p q h v m : ℤ) (before : Bool) : Prop :=
  0 ≤ 2*R p q h v m ∧ 2*R p q h v m ≤ A p q h-1 ∧
  0 ≤ 4*R p q h v m+2*((y p q h-m)*Q q+1)-(if before then 0 else 2*A p q h) ∧
  4*R p q h v m+2*((y p q h-m)*Q q+1)-(if before then 0 else 2*A p q h) ≤ A p q h-1

def Windows (p q h v m M : ℤ) (before : Bool) : Prop :=
  ∀ r : Fin 4,
    (0 ≤ SecondPeakHighD.oldEnds 4 p q h v m M r ∧
      SecondPeakHighD.oldEnds 4 p q h v m M r ≤ SecondPeakHighD.oldHeads 4 p q h r-1) ∧
    (0 ≤ SecondPeakHighD.newEnds 4 p q h v m M before r ∧
      SecondPeakHighD.newEnds 4 p q h v m M before r ≤ SecondPeakHighD.newHeads 4 p q h r-1)

def Good (p q h v m M : ℕ) (before : Bool) : Prop :=
  1 ≤ v ∧ 2*v ≤ 4*p*q ∧ m < M ∧ 2*M < 8*h*p*q ∧
    SecondPeakHighD.Submask m M ∧ Windows p q h v m M before

private theorem basic_positive (p q h : ℤ) (hp : 4 ≤ p) (hq : 2 ≤ q)
    (hh : 1 ≤ h) : 0 < A p q h ∧ 0 < L p q ∧ 0 < Q q := by
  dsimp [A,L,Q,SecondPeakHighD.A,SecondPeakHighD.L,SecondPeakHighD.Z,SecondPeakHighD.T,SecondPeakHighD.Y]
  constructor
  · positivity
  constructor <;> positivity

/-- Exact first-window arithmetic, with the late fresh charge retained. -/
theorem first_of_exact (p q h v m : ℤ) (before : Bool)
    (hp : 4 ≤ p) (hq : 2 ≤ q) (hh : 1 ≤ h)
    (hm : 0 ≤ m) (hmy : 2*m < y p q h)
    (hw : if before then
      0 ≤ 8*R p q h v m ∧ 8*R p q h v m ≤ A p q h-1+4*m*Q q
      else 3*A p q h+1+4*m*Q q ≤ 8*R p q h v m ∧
        8*R p q h v m ≤ 4*A p q h-4) : First p q h v m before := by
  obtain ⟨hA,hL,hQ⟩ := basic_positive p q h hp hq hh
  have ha : A p q h=5+4*y p q h*Q q := by
    dsimp [A,y,Q,SecondPeakHighD.A,SecondPeakHighD.Z,SecondPeakHighD.T,SecondPeakHighD.Y]; ring
  have hcharge : 0 ≤ (y p q h-2*m)*Q q := mul_nonneg (by omega) hQ.le
  have hmQ : 0 ≤ m*Q q := mul_nonneg hm hQ.le
  cases before <;> simp only [Bool.false_eq_true,ite_false,ite_true] at hw ⊢
  all_goals dsimp [First]
  all_goals try simp only [Bool.false_eq_true,ite_false,ite_true]
  all_goals rcases hw with ⟨hlo,hhi⟩
  all_goals refine ⟨?_,?_,?_,?_⟩
  all_goals nlinarith

/-- The uniform sufficient second-window interval is genuinely unbounded. -/
theorem second_windows (p q h M : ℤ) (hp : 4 ≤ p) (hq : 2 ≤ q)
    (hh : h=1 ∨ h=2)
    (hdlo : 2*h ≤ 5*M-(y p q h-8*h*p))
    (hdhi : 5*M-(y p q h-8*h*p) ≤ 4*h*p) :
    0 < M ∧ 2*M < y p q h ∧
    (0 ≤ 2*B p q h-2*K p q h+2*M*L p q ∧
      2*B p q h-2*K p q h+2*M*L p q ≤ B p q h-1) ∧
    (0 ≤ 2*SU p q h-2*SW p q h+2*M*SV p q ∧
      2*SU p q h-2*SW p q h+2*M*SV p q ≤ SU p q h-1) := by
  have hhh : 1 ≤ h := by omega
  obtain ⟨hA,hL,hQ⟩ := basic_positive p q h hp hq hhh
  let delta := 5*M-(y p q h-8*h*p)
  let Z := M*L p q-K p q h+B p q h
  have loId : 5*Z=(delta-2*h)*L p q+
      (2*h*p*(z q)^2+p*(25-16*h)*z q-8*h*p+2*h*Q q) := by
    dsimp [Z,delta,A,B,L,K,z,y,Q,SecondPeakHighD.A,SecondPeakHighD.B,SecondPeakHighD.L,SecondPeakHighD.K,SecondPeakHighD.Z,SecondPeakHighD.T,SecondPeakHighD.Y]; ring
  have hiId : 5*(B p q h-1-2*Z-(y p q h-M)*Q q)=
      (4*h*p-delta)*(Q q+10*p*(z q)^2)+
      p*(8*h*(z q)^2+(12*h-25)*z q+4*h) := by
    dsimp [Z,delta,A,B,L,K,z,y,Q,SecondPeakHighD.A,SecondPeakHighD.B,SecondPeakHighD.L,SecondPeakHighD.K,SecondPeakHighD.Z,SecondPeakHighD.T,SecondPeakHighD.Y]; ring
  have nonlo : 0 ≤ (delta-2*h)*L p q := mul_nonneg (by dsimp [delta]; omega) hL.le
  have nonhi : 0 ≤ (4*h*p-delta)*(Q q+10*p*(z q)^2) :=
    mul_nonneg (by dsimp [delta]; omega) (by dsimp [Q,z]; positivity)
  have poslo : 0 < 2*h*p*(z q)^2+p*(25-16*h)*z q-8*h*p+2*h*Q q := by
    obtain ⟨u,hu,rfl⟩ : ∃ u : ℤ, 0≤u ∧ q=u+2 := ⟨q-2,by omega,by ring⟩
    rcases hh with rfl|rfl <;> dsimp [z,Q] <;> ring_nf <;> positivity
  have poshi : 0 < p*(8*h*(z q)^2+(12*h-25)*z q+4*h) := by
    obtain ⟨u,hu,rfl⟩ : ∃ u : ℤ, 0≤u ∧ q=u+2 := ⟨q-2,by omega,by ring⟩
    rcases hh with rfl|rfl <;> dsimp [z] <;> ring_nf <;> positivity
  have hM : 0 < M ∧ 2*M < y p q h := by
    have hpq : 0 ≤ h*p*(q-2) := mul_nonneg (by positivity) (by omega)
    have hhp : 0<h*p := mul_pos (by omega) (by omega)
    dsimp [y] at hdlo hdhi ⊢
    constructor <;> nlinarith
  have hc : 0 ≤ (y p q h-M)*Q q := mul_nonneg (by omega) hQ.le
  have hZ : 0 ≤ Z ∧ 2*Z+(y p q h-M)*Q q ≤ B p q h-1 := by
    constructor <;> nlinarith
  have charge : 2*SU p q h-2*SW p q h+2*M*SV p q=
      4*Z+2*(y p q h-M)*Q q := by
    dsimp [Z,SU,SW,SV,B,L,K,y,Q,SecondPeakHighD.SU,SecondPeakHighD.SW,SecondPeakHighD.SV,SecondPeakHighD.B,SecondPeakHighD.L,SecondPeakHighD.K,SecondPeakHighD.Z,SecondPeakHighD.T,SecondPeakHighD.Y]; ring
  refine ⟨hM.1,hM.2,?_,?_⟩
  · dsimp [Z] at hZ
    constructor <;> nlinarith
  · rw [charge]
    dsimp [SU,SecondPeakHighD.SU]
    constructor <;> nlinarith

/-- Third windows; the physical K/SW heads differ from the second heads. -/
theorem third_windows (p q h : ℤ) (hp : 4 ≤ p) (hq : 2 ≤ q)
    (hh : h=1 ∨ h=2) :
    (0 ≤ 2*B p q h-2*L p q ∧ 2*B p q h-2*L p q ≤ K p q h-1) ∧
    (0 ≤ 2*SU p q h-2*SV p q ∧ 2*SU p q h-2*SV p q ≤ SW p q h-1) := by
  obtain ⟨u,hu,rfl⟩ : ∃ u : ℤ, 0≤u ∧ p=u+4 := ⟨p-4,by omega,by ring⟩
  obtain ⟨w,hw,rfl⟩ : ∃ w : ℤ, 0≤w ∧ q=w+2 := ⟨q-2,by omega,by ring⟩
  rcases hh with rfl|rfl
  all_goals constructor <;> constructor
  all_goals apply le_of_sub_nonneg
  all_goals dsimp [A,B,L,K,SU,SV,SW,SecondPeakHighD.A,SecondPeakHighD.B,
    SecondPeakHighD.L,SecondPeakHighD.K,SecondPeakHighD.SU,SecondPeakHighD.SV,
    SecondPeakHighD.SW,SecondPeakHighD.Z,SecondPeakHighD.T,SecondPeakHighD.Y]
  all_goals ring_nf
  all_goals positivity

/-- Assembly preserves the three charged pairs, including the separate zero seam. -/
theorem windows_of_first (p q h v m M : ℤ) (before : Bool)
    (hp : 4 ≤ p) (hq : 2 ≤ q) (hh : h=1 ∨ h=2)
    (hfirst : First p q h v m before)
    (hdlo : 2*h ≤ 5*M-(y p q h-8*h*p))
    (hdhi : 5*M-(y p q h-8*h*p) ≤ 4*h*p) : Windows p q h v m M before := by
  obtain ⟨_,_,h2,h2'⟩ := second_windows p q h M hp hq hh hdlo hdhi
  obtain ⟨h3,h3'⟩ := third_windows p q h hp hq hh
  have hh1 : 1≤h := by omega
  have hL : 1≤L p q := by
    apply le_of_sub_nonneg
    dsimp [L,SecondPeakHighD.L,SecondPeakHighD.Z,SecondPeakHighD.T]
    ring_nf
    positivity
  have hSV : 1≤SV p q := by
    apply le_of_sub_nonneg
    dsimp [SV,SecondPeakHighD.SV,SecondPeakHighD.L,SecondPeakHighD.Z,SecondPeakHighD.T]
    ring_nf
    positivity
  intro r
  fin_cases r
  · have eo : SecondPeakHighD.oldEnds 4 p q h v m M 0=2*R p q h v m := by
      dsimp [SecondPeakHighD.oldEnds,R]; ring
    have en : SecondPeakHighD.newEnds 4 p q h v m M before 0=
        4*R p q h v m+2*((y p q h-m)*Q q+1)-(if before then 0 else 2*A p q h) := by
      cases before <;> dsimp [SecondPeakHighD.newEnds,R,A,L,K,SW,SV,y,Q,
        SecondPeakHighD.A,SecondPeakHighD.L,SecondPeakHighD.K,SecondPeakHighD.SW,
        SecondPeakHighD.SV,SecondPeakHighD.Z,SecondPeakHighD.T,SecondPeakHighD.Y] <;> ring
    change (0≤SecondPeakHighD.oldEnds 4 p q h v m M 0 ∧
      SecondPeakHighD.oldEnds 4 p q h v m M 0≤A p q h-1) ∧
      (0≤SecondPeakHighD.newEnds 4 p q h v m M before 0 ∧
      SecondPeakHighD.newEnds 4 p q h v m M before 0≤A p q h-1)
    rw [eo,en]
    exact ⟨⟨hfirst.1,hfirst.2.1⟩,hfirst.2.2⟩
  · exact ⟨h2,h2'⟩
  · exact ⟨h3,h3'⟩
  · simpa [SecondPeakHighD.oldEnds,SecondPeakHighD.newEnds,SecondPeakHighD.oldHeads,SecondPeakHighD.newHeads] using
      (show (0≤(0:ℤ) ∧ 0≤L p q-1) ∧ (0≤(0:ℤ) ∧ 0≤SV p q-1) by omega)

end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakA2
