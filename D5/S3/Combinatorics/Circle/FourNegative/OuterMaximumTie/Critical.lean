/- GID: D5/S3/Combinatorics/Circle/FourNegative/OuterMaximumTie/Critical
   generality: I
   mirror-B: none(waiver:consumed-critical-construction)
   mirror-E: none(waiver:consumed-critical-construction)
   anchors: [mathlib/module/Mathlib.Data.List.FinRange]
   utility: none
   digest: Two translates cover the entire critical remainder interval. -/
import D5.S3.Combinatorics.Circle.FourNegative.OuterMaximumTie.Arithmetic

/-! The second choice moves the physical W bit 0 and reduces the U MASK by 2.
It does not remove two U occurrences. Both charged rows are retained. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.OuterMaximumTie
open private D A B L M eps oldSeam newSeam oldHead newHead Gates Stock
  first_gates positive_heads dyadic_split dyadic_four
  from D5.S3.Combinatorics.Circle.FourNegative.OuterMaximumTie.Arithmetic

private theorem critical_margins (y z : ℤ) (hz : 4≤z) (hy : 4*z≤y) :
    let t := 2*y
    let delta := 2*A t y z-L t z
    let C4 := 2*L t z+z-2*D y z-2
    let J := B t y-L t z-eps t y z
    0<delta ∧ 0≤C4-4*delta ∧ 0≤4*delta-4*A t y z+C4 ∧
    0<J-A t y z ∧ 0<(y-1)*A t y z-J ∧
    0<L t z-M t y z ∧
    0<B t y-1-(4*L t z-2*M t y z+D y z-2*(z+1)) ∧
    0<D y z-2*(z+1) ∧ 0<D y z-2*z-1 := by
  let U := y-4*z
  let Z := z-4
  have hU : 0≤U := by dsimp [U]; omega
  have hZ : 0≤Z := by dsimp [Z]; omega
  have ey : y=U+4*(Z+4) := by dsimp [U,Z]; ring
  have ez : z=Z+4 := by dsimp [Z]; ring
  dsimp only
  rw [ey,ez]
  dsimp [A,B,L,M,D,eps]
  repeat' constructor
  all_goals first | (ring_nf; positivity) | (apply sub_nonneg.mp; ring_nf; positivity)

/- Ceiling arithmetic and a full closed/open threshold split. There is no
feasible-window premise: all its margins are proved by critical_margins. -/
private theorem remainder_switch (AA JJ delta C4 yy : ℤ)
    (hA : 0<AA) (hJ : AA<JJ) (hstock : JJ<(yy-1)*AA)
    (hd : 0<delta) (hc : 4*delta≤C4) (hcover : 4*AA≤4*delta+C4) :
    let v0 := (JJ+AA-1)/AA
    let R := v0*AA-JJ
    2≤v0 ∧ v0≤yy-1 ∧ 0≤R ∧ R<AA ∧
    ∃ v w : ℤ,
      (v=(if 4*R≤C4 then v0 else v0-2)) ∧
      (w=(if 4*R≤C4 then 0 else 1)) ∧
      0≤v ∧ v≤yy-1 ∧ (w=0 ∨ w=1) ∧
      0≤R-w*delta ∧ 4*(R-w*delta)≤C4 := by
  dsimp only
  let v0 := (JJ+AA-1)/AA
  let R := v0*AA-JJ
  have rem0 := Int.emod_nonneg (JJ+AA-1) (ne_of_gt hA)
  have rem1 := Int.emod_lt_of_pos (JJ+AA-1) hA
  have eqn := Int.emod_add_mul_ediv (JJ+AA-1) AA
  change (JJ+AA-1)%AA+AA*v0=JJ+AA-1 at eqn
  have hReq : R = AA - 1 - ((JJ+AA-1)%AA) := by
    dsimp [R]
    calc
      v0 * AA - JJ = AA * v0 - JJ := by ring
      _ = AA - 1 - ((JJ+AA-1)%AA) := by omega
  have hR : 0≤R ∧ R<AA := by
    rw [hReq]
    constructor <;> omega
  have hv0 : 2≤v0 := by
    by_contra h
    have hm := mul_le_mul_of_nonneg_right (show v0≤1 by omega) hA.le
    dsimp [R] at hR
    nlinarith
  have hv1 : v0≤yy-1 := by
    by_contra h
    have hm := mul_le_mul_of_nonneg_right (show yy≤v0 by omega) hA.le
    dsimp [R] at hR
    nlinarith
  refine ⟨hv0,hv1,hR.1,hR.2,?_⟩
  by_cases h : 4*R≤C4
  · refine ⟨v0, 0, ?_, ?_, by omega, hv1, Or.inl rfl, ?_, ?_⟩
    · change v0 = (if 4 * R ≤ C4 then v0 else v0 - 2)
      simp [h]
    · change (0:ℤ) = (if 4 * R ≤ C4 then 0 else 1)
      simp [h]
    · dsimp [R,v0] at hR ⊢
      simpa using hR.1
    · dsimp [R,v0] at h ⊢
      simpa using h
  · refine ⟨v0 - 2, 1, ?_, ?_, by omega, by omega, Or.inr rfl, ?_, ?_⟩
    · change v0 - 2 = (if 4 * R ≤ C4 then v0 else v0 - 2)
      simp [h]
    · change (1:ℤ) = (if 4 * R ≤ C4 then 0 else 1)
      simp [h]
    · dsimp [R,v0] at hR ⊢
      nlinarith [hR.1, hd, h]
    · dsimp [R,v0] at h ⊢
      nlinarith [h]

set_option maxHeartbeats 2400000 in
private theorem critical_far (y z : ℤ) (hz : 4≤z) (hy : 4*z≤y) :
    ∃ v w : ℤ, Stock false (2*y) y z v w ∧ Gates false (2*y) y z v w := by
  let t := 2*y
  let AA := A t y z
  let BB := B t y
  let LL := L t z
  let MM := M t y z
  let DD := D y z
  let delta := 2*AA-LL
  let C4 := 2*LL+z-2*DD-2
  let J := BB-LL-eps t y z
  have hy4 : 4≤y := by omega
  have hp := positive_heads t y z (by dsimp [t]; omega) hy4 hz
  obtain ⟨hd,hc,hcover,hJ,hstock,hLM,hthird,hDQ,hDzz⟩ := critical_margins y z hz hy
  change 0<delta at hd
  change 0≤C4-4*delta at hc
  change 0≤4*delta-4*AA+C4 at hcover
  change 0<J-AA at hJ
  change 0<(y-1)*AA-J at hstock
  obtain ⟨hv0,hv1,hR0,hR1,v,w,ev,ew,hv,hvc,hw,hE,hEc⟩ :=
    remainder_switch AA J delta C4 y hp.1 (by omega) (by omega) hd (by omega) (by omega)
  let v0 := (J+AA-1)/AA
  let R := v0*AA-J
  change 2≤v0 at hv0
  change v0≤y-1 at hv1
  change 0≤R at hR0
  change R<AA at hR1
  change v=(if 4*R≤C4 then v0 else v0-2) at ev
  change w=(if 4*R≤C4 then 0 else 1) at ew
  change 0≤R-w*delta at hE
  change 4*(R-w*delta)≤C4 at hEc
  have hrel : v=v0-2*w := by
    by_cases h : 4*R≤C4 <;> simp only [h,ite_true,ite_false] at ev ew <;> omega
  have shifts :
      oldSeam false t y z (v0-2) 1 1-oldSeam false t y z v0 0 1= -delta ∧
      newSeam false t y z (v0-2) 1 1-newSeam false t y z v0 0 1= -2*delta-(z+1) := by
    dsimp [oldSeam,newSeam,delta,AA,LL]
    constructor <;> ring
  have baseOld : oldSeam false t y z v0 0 1=R := by
    dsimp [oldSeam,R,J,eps,AA,BB,LL,MM]
    ring
  have baseNew : newSeam false t y z v0 0 1=2*R+DD-z := by
    dsimp [newSeam]
    rw [baseOld]
    simp [DD]
  have hseam : oldSeam false t y z v w 1=R-w*delta := by
    rcases hw with hw|hw
    · have ev0 : v=v0 := by omega
      rw [hw,ev0]; simpa using baseOld
    · have ev1 : v=v0-2 := by omega
      rw [hw,ev1]
      nlinarith only [shifts.1,baseOld]
  have hnewexact : newSeam false t y z v w 1=
      2*(R-w*delta)+DD-z-w*(z+1) := by
    rcases hw with hw|hw
    · have ev0 : v=v0 := by omega
      rw [hw,ev0]; simpa using baseNew
    · have ev1 : v=v0-2 := by omega
      rw [hw,ev1]
      nlinarith only [shifts.2,baseNew]
  have hfirst := first_gates t y z hy4 hz (by dsimp [t]; omega) (by dsimp [t]; omega)
  have hD : z+1≤DD := hp.2.2.2.2.2
  refine ⟨v,w,?_,?_⟩
  · dsimp [Stock,t]
    rcases hw with rfl|rfl <;> simp <;> omega
  · intro j
    fin_cases j
    · simpa [Gates,oldSeam,newSeam,oldHead,newHead] using
        And.intro (And.intro hfirst.1 hfirst.2.1)
          (And.intro hfirst.2.2.1 hfirst.2.2.2)
    · rcases hw with hw|hw
      all_goals change
        (0 ≤ oldSeam false t y z v w 1 ∧
          2 * oldSeam false t y z v w 1 ≤ oldHead false t y z 1 - 1) ∧
        (0 ≤ newSeam false t y z v w 1 ∧
          2 * newSeam false t y z v w 1 ≤ newHead false t y z 1 - 1)
      all_goals rw [hseam, hnewexact]
      all_goals dsimp [oldHead,newHead,C4,DD] at *
      all_goals subst w
      all_goals constructor <;> constructor <;> nlinarith
    · rcases hw with hw|hw <;> subst w
      all_goals dsimp [oldSeam,newSeam,oldHead,newHead]
      all_goals dsimp [AA,BB,LL,MM,DD,t] at *
      all_goals constructor <;> constructor <;> nlinarith [hp.2.1,hp.2.2.1]
    · dsimp [oldSeam,newSeam,oldHead,newHead]
      constructor <;> constructor <;> nlinarith [hp.2.2.2.1,hp.2.2.2.2.1]

private theorem critical_adjacent (z : ℤ) (hz : 4≤z) :
    Stock false (4*z) (2*z) z 2 0 ∧ Gates false (4*z) (2*z) z 2 0 := by
  have first := first_gates (4*z) (2*z) z (by omega) hz (by omega) (by omega)
  have hp := positive_heads (4*z) (2*z) z (by omega) (by omega) hz
  let Z := z-4
  have hZ : 0≤Z := by dsimp [Z]; omega
  have ez : z=Z+4 := by dsimp [Z]; ring
  constructor
  · dsimp [Stock]; omega
  · intro j; fin_cases j
    · simpa [oldSeam,newSeam,oldHead,newHead] using
        And.intro (And.intro first.1 first.2.1)
          (And.intro first.2.2.1 first.2.2.2)
    · dsimp [oldSeam,newSeam,oldHead,newHead,eps,A,B,L,M,D]
      rw [ez]
      repeat' constructor
      all_goals first | (ring_nf; positivity) | (apply sub_nonneg.mp; ring_nf; positivity)
    · dsimp [oldSeam,newSeam,oldHead,newHead,eps,A,B,L,M,D]
      rw [ez]
      repeat' constructor
      all_goals first | (ring_nf; positivity) | (apply sub_nonneg.mp; ring_nf; positivity)
    · dsimp [oldSeam,newSeam,oldHead,newHead]
      constructor <;> constructor <;> nlinarith [hp.2.2.2.1,hp.2.2.2.2.1]

private theorem critical_allocate (a b c : ℕ) (hc : 2≤c)
    (hba : b+1=a) (hcb : c<b) :
    ∃ v w : ℤ, Stock false (2^a) (2^b) (2^c) v w ∧
      Gates false (2^a) (2^b) (2^c) v w := by
  have et : (2:ℤ)^a=2*2^b := by rw [←hba,pow_succ]; ring
  rw [et]
  by_cases he : b=c+1
  · have ey : (2:ℤ)^b=2*2^c := by rw [he,pow_succ]; ring
    rw [ey]
    have h := critical_adjacent (2^c) (dyadic_four c hc)
    exact ⟨2, 0, by convert h.1 using 1 <;> ring, by convert h.2 using 1 <;> ring⟩
  · have hpow := pow_le_pow_right₀ (by norm_num : (1:ℤ)≤2) (show c+2≤b by omega)
    have hy : (4:ℤ)*2^c≤2^b := by
      calc
        (4:ℤ)*2^c = 2^(c+2) := by rw [pow_add]; norm_num; ring
        _ ≤ 2^b := hpow
    exact critical_far (2^b) (2^c) (dyadic_four c hc) hy

end D5.S3.Combinatorics.Circle.FourNegative.OuterMaximumTie
