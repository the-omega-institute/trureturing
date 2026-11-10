/- GID: D5/S3/Combinatorics/SpectralGraph/ArithmeticCurves/A6DyadicInfiniteOrder
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/ArithmeticCurves/A6DyadicInfiniteOrder
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Actual a6 elliptic infinite-order witnesses via dyadic doubling -/
import D5.S3.Combinatorics.SpectralGraph.ArithmeticCurves.A6GaloisCoset
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.LinearAlgebra.Dimension.Basic
/-! Received S.nontorsion, blob01edb67a7e6753c17ecae77e581d4957fe6b94cc,
PR9 revision6d491f77b35dec808fc777b69939c56cdae5dc02. Original
Nikandish problem and Ma/Nikandish/Zhang conclusions/attribution remain.
The supplied written Nagell-Lutz proof remains part of original evidence.
This native proof uses exact dyadic doubling of the same actual points;
no nontorsion assumption, rank oracle or point-list oracle is introduced. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
open scoped Classical QuadraticAlgebra
namespace D5.S3.Combinatorics.SpectralGraph.ArithmeticCurves.A6DyadicInfiniteOrder
open A6EllipticModels A6GaloisCoset WeierstrassCurve.Affine
private instance : Fact (Nat.Prime 2):=⟨by decide⟩

private theorem dominant_add (q r : ℚ) (hq : q≠0)
    (hv : padicValRat 2 q<padicValRat 2 r) :
    q+r≠0 ∧ padicValRat 2 (q+r)=padicValRat 2 q := by
  have hn : q+r≠0 := by
    intro h
    have hr : r= -q:=by linarith
    rw [hr,padicValRat.neg] at hv
    omega
  refine ⟨hn,?_⟩
  by_cases hr : r=0
  · simp [hr]
  · exact padicValRat.add_eq_of_lt hn hq hr hv

private theorem weighted_power_val (c : ℚ) (hc : c≠0)
    (hcv : 0≤padicValRat 2 c) (x : ℚ) (hx : x≠0) (n : ℕ) :
    (n:ℤ)*padicValRat 2 x≤padicValRat 2 (c*x^n) := by
  rw [padicValRat.mul hc (pow_ne_zero n hx),padicValRat.pow x]
  omega

private def cubic (x : ℚ) : ℚ:=
  x^3+6640150*x^2+5047497487500*x+1053718156603125000
private def numerator (x : ℚ) : ℚ:=
  x^4-2*5047497487500*x^2-8*1053718156603125000*x+
    5047497487500^2-4*6640150*1053718156603125000
private def doubledX (x : ℚ) : ℚ:=numerator x/(4*cubic x)

private theorem cubic_val (x : ℚ) (hv : padicValRat 2 x<0) :
    cubic x≠0 ∧ padicValRat 2 (cubic x)=3*padicValRat 2 x := by
  have hx : x≠0:=by intro h;simpa [h] using hv
  have h2:=weighted_power_val 6640150 (by norm_num) (zero_le_padicValRat_of_nat 6640150) x hx 2
  have h1:=weighted_power_val 5047497487500 (by norm_num) (zero_le_padicValRat_of_nat 5047497487500) x hx 1
  have h0 : 0≤padicValRat 2 (1053718156603125000:ℚ):=zero_le_padicValRat_of_nat 1053718156603125000
  have h3 : padicValRat 2 (x^3)=3*padicValRat 2 x:=by rw [padicValRat.pow x];norm_num
  obtain ⟨hn2,hv2⟩:=dominant_add (x^3) (6640150*x^2) (pow_ne_zero 3 hx) (by omega)
  obtain ⟨hn1,hv1⟩:=dominant_add (x^3+6640150*x^2) (5047497487500*x) hn2 (by simpa only [pow_one] using (show padicValRat 2 (x^3+6640150*x^2)<padicValRat 2 (5047497487500*x^1) by omega))
  obtain ⟨hn0,hv0⟩:=dominant_add (x^3+6640150*x^2+5047497487500*x) 1053718156603125000 hn1 (by omega)
  exact ⟨hn0,by dsimp [cubic];omega⟩

private theorem numerator_val (x : ℚ) (hv : padicValRat 2 x<0) :
    numerator x≠0 ∧ padicValRat 2 (numerator x)=4*padicValRat 2 x := by
  have hx : x≠0:=by intro h;simpa [h] using hv
  have h2:=weighted_power_val (-2*5047497487500) (by norm_num) (by norm_num [padicValRat_def]) x hx 2
  have h1:=weighted_power_val (-8*1053718156603125000) (by norm_num) (by norm_num [padicValRat_def]) x hx 1
  have h0 : 0≤padicValRat 2 (5047497487500^2-4*6640150*1053718156603125000:ℚ):=by norm_num [padicValRat_def]
  have h4 : padicValRat 2 (x^4)=4*padicValRat 2 x:=by rw [padicValRat.pow x];norm_num
  obtain ⟨hn2,hv2⟩:=dominant_add (x^4) ((-2*5047497487500)*x^2) (pow_ne_zero 4 hx) (by omega)
  obtain ⟨hn1,hv1⟩:=dominant_add (x^4+(-2*5047497487500)*x^2) ((-8*1053718156603125000)*x) hn2 (by simpa only [pow_one] using (show padicValRat 2 (x^4+(-2*5047497487500)*x^2)<padicValRat 2 ((-8*1053718156603125000)*x^1) by omega))
  obtain ⟨hn0,hv0⟩:=dominant_add (x^4+(-2*5047497487500)*x^2+(-8*1053718156603125000)*x)
    (5047497487500^2-4*6640150*1053718156603125000) hn1 (by omega)
  have he : numerator x=x^4+(-2*5047497487500)*x^2+(-8*1053718156603125000)*x+
      (5047497487500^2-4*6640150*1053718156603125000):=by dsimp [numerator];ring
  rw [he]
  exact ⟨hn0,by omega⟩

private theorem doubledX_val (x : ℚ) (hv : padicValRat 2 x<0) :
    padicValRat 2 (doubledX x)=padicValRat 2 x-2 := by
  obtain ⟨hc,hcv⟩:=cubic_val x hv
  obtain ⟨hn,hnv⟩:=numerator_val x hv
  dsimp [doubledX]
  rw [padicValRat.div hn (mul_ne_zero (by norm_num) hc),
    padicValRat.mul (by norm_num : (4:ℚ)≠0) hc,hnv,hcv]
  have h4 : padicValRat 2 (4:ℚ)=2:=by
    have h2 : padicValRat 2 (2:ℚ)=1 := by
      simpa only [Nat.cast_ofNat] using (padicValRat.self (p:=2) (by decide))
    rw [show (4:ℚ)=(2:ℚ)^2 by norm_num,padicValRat.pow,h2]
    norm_num
  omega

private theorem rational_double (P : KPoint)
    (hi : (P.xRep 0).im=0) (hv : padicValRat 2 (P.xRep 0).re<0) :
    ((P+P).xRep 0).im=0 ∧
      ((P+P).xRep 0).re=doubledX (P.xRep 0).re := by
  cases P with
  | zero =>
    change padicValRat 2 (1:ℚ)<0 at hv
    norm_num at hv
  | some U V h =>
    change U.im=0 at hi
    change padicValRat 2 U.re<0 at hv
    have hU : U=algebraMap ℚ K U.re:=by
      ext <;> simp [QuadraticAlgebra.algebraMap_eq,hi]
    have hden : 4*U^3+(E0.toAffine.baseChange K).b₂*U^2+
        2*(E0.toAffine.baseChange K).b₄*U+(E0.toAffine.baseChange K).b₆≠0 := by
      have he : 4*U^3+(E0.toAffine.baseChange K).b₂*U^2+
          2*(E0.toAffine.baseChange K).b₄*U+(E0.toAffine.baseChange K).b₆=
          algebraMap ℚ K (4*cubic U.re) := by
        rw [hU]
        simp only [map_mul,map_add,map_pow,map_ofNat,cubic]
        simp [E0,WeierstrassCurve.Affine.baseChange,WeierstrassCurve.map,
          WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆]
        ring
      rw [he]
      exact (map_ne_zero (algebraMap ℚ K)).mpr (mul_ne_zero (by norm_num) (cubic_val U.re hv).1)
    have hy : V≠(E0.toAffine.baseChange K).negY U V :=
      (den_duplication_eq_zero_iff h.1).not.mp hden
    rw [Point.xRep_add_self_of_Y_ne h hy]
    simp only [Matrix.cons_val_zero]
    have he : (U^4-(E0.toAffine.baseChange K).b₄*U^2-
          2*(E0.toAffine.baseChange K).b₆*U-(E0.toAffine.baseChange K).b₈)/
          (4*U^3+(E0.toAffine.baseChange K).b₂*U^2+
          2*(E0.toAffine.baseChange K).b₄*U+(E0.toAffine.baseChange K).b₆)=
          algebraMap ℚ K (doubledX U.re) := by
      rw [hU]
      simp only [doubledX,numerator,cubic,map_div,map_sub,map_mul,map_add,map_pow,map_ofNat]
      congr 1 <;>
        simp [E0,WeierstrassCurve.Affine.baseChange,WeierstrassCurve.map,
          WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈] <;> ring
    rw [he]
    simp [QuadraticAlgebra.algebraMap_eq]

private theorem doubling_valuation (P : KPoint)
    (hi : (P.xRep 0).im=0) (hv : padicValRat 2 (P.xRep 0).re<0) :
    ((P+P).xRep 0).im=0 ∧
      padicValRat 2 ((P+P).xRep 0).re=padicValRat 2 (P.xRep 0).re-2 := by
  obtain ⟨hi',he⟩:=rational_double P hi hv
  exact ⟨hi',by rw [he,doubledX_val _ hv]⟩

/-- Actual full point group: negative dyadic horizontal valuation forces
an infinite doubling orbit, hence infinite additive order. -/
theorem infinite_order_of_negative_dyadic (P : KPoint)
    (hi : (P.xRep 0).im=0) (hv : padicValRat 2 (P.xRep 0).re<0) :
    ¬IsOfFinAddOrder P := by
  intro hfin
  have hiter (n : ℕ) : (((2^n:ℕ)•P).xRep 0).im=0 ∧
      padicValRat 2 (((2^n:ℕ)•P).xRep 0).re=padicValRat 2 (P.xRep 0).re-2*n := by
    induction n with
    | zero =>
      simp only [pow_zero,one_nsmul,Nat.cast_zero,mul_zero,sub_zero]
      exact ⟨hi,trivial⟩
    | succ n hn =>
      have hneg : padicValRat 2 (((2^n:ℕ)•P).xRep 0).re<0 := by rw [hn.2];omega
      have hh:=doubling_valuation ((2^n:ℕ)•P) hn.1 hneg
      rw [pow_succ,mul_nsmul,two_nsmul]
      refine ⟨hh.1,?_⟩
      rw [hh.2,hn.2]
      push_cast
      ring
  have hf : (Set.range (fun n : ℕ=>(2^n:ℕ)•P)).Finite := by
    apply hfin.finite_multiples.subset
    rintro Q ⟨n,rfl⟩
    exact ⟨2^n,rfl⟩
  obtain ⟨m,n,hmn,he⟩:=hf.exists_lt_map_eq_of_forall_mem
    (f:=fun n : ℕ=>(2^n:ℕ)•P) (fun n=>Set.mem_range_self n)
  have hvEq:=congrArg (fun Q : KPoint=>padicValRat 2 (Q.xRep 0).re) he
  rw [(hiter m).2,(hiter n).2] at hvEq
  have hmnZ : (m:ℤ)<n:=by exact_mod_cast hmn
  omega

private theorem T_double_x : (T+T).xRep 0=
    (⟨-92771180831058519/251814366580,0⟩ : K) := by
  have hy : ty≠(E0.toAffine.baseChange K).negY tx ty := by
    intro he
    have hh:=congrArg QuadraticAlgebra.im he
    norm_num [ty,tx,negY,E0,WeierstrassCurve.Affine.baseChange,WeierstrassCurve.map] at hh
  change (Point.some tx ty _+Point.some tx ty _).xRep 0=_
  rw [Point.xRep_add_self_of_Y_ne _ hy]
  ext <;>
    norm_num [E0,WeierstrassCurve.Affine.baseChange,WeierstrassCurve.map,
      WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈,
      tx,pow_succ,QuadraticAlgebra.div_def,QuadraticAlgebra.inv_def,
      QuadraticAlgebra.norm_def,QuadraticAlgebra.re_ofNat,QuadraticAlgebra.im_ofNat]

private theorem negative_odd_even (n : ℤ) (d : ℕ)
    (hn : ¬(2:ℤ)∣n) (hd : 2∣d) (hd0 : d≠0) :
    padicValRat 2 ((n:ℚ)/(d:ℚ))<0 := by
  have hn0 : n≠0:=by rintro rfl;simp at hn
  rw [padicValRat.div (by exact_mod_cast hn0) (by exact_mod_cast hd0),
    padicValRat.of_int,padicValRat.of_nat,padicValInt.eq_zero_of_not_dvd hn]
  have hh:=one_le_padicValNat_of_dvd (p:=2) hd0 hd
  omega

/-- The original full Galois-difference point has infinite additive order. -/
theorem T_infinite_order : ¬IsOfFinAddOrder T := by
  intro hfin
  apply infinite_order_of_negative_dyadic (T+T) _ _ (hfin.add hfin)
  · rw [T_double_x]
  · rw [T_double_x]
    exact negative_odd_even (-92771180831058519) 251814366580
      (by norm_num) (by norm_num) (by norm_num)

private def mkRational (u v : ℚ)
    (h : v^2=u^3+6640150*u^2+5047497487500*u+1053718156603125000) : QPoint :=
  .mk (by apply (equation_iff _ _).mpr;simpa [E0] using h)

/-- The exact original rational chart control; it is not a graph example. -/
def S : QPoint := mkRational (-50963250/121) (234393705000/1331) (by norm_num)
theorem S_received_chart : S=rationalPoint
    ⟨(55,-781950),by norm_num [f]⟩ := by
  unfold S mkRational rationalPoint Point.mk
  simp only [Point.some.injEq]
  constructor <;> norm_num [rationalU,rationalV,modelL]

private def S2 : QPoint := mkRational (-666233275601273250/114942018961)
  (-15047694119623614750405000/38968907630366791) (by norm_num)

private theorem S_double : S+S=S2 := by
  have hy : (234393705000/1331:ℚ)≠E0.toAffine.negY
      (-50963250/121) (234393705000/1331) := by norm_num [negY,E0]
  unfold S S2 mkRational Point.mk
  rw [Point.add_self_of_Y_ne hy]
  simp only [Point.some.injEq]
  constructor <;> norm_num [addX,addY,negAddY,negY,slope_of_Y_ne rfl hy,E0]

private theorem S_triple_x : ((S+S)+S).xRep 0=
    (-82206618201204652343709758199/199642521780828906626704:ℚ) := by
  rw [S_double]
  have hx : (-666233275601273250/114942018961:ℚ)≠ -50963250/121 := by norm_num
  unfold S S2 mkRational Point.mk
  rw [Point.xRep_add_of_X_ne _ _ hx]
  norm_num [E0,WeierstrassCurve.b₂,WeierstrassCurve.b₄,WeierstrassCurve.b₆,
    WeierstrassCurve.b₈]

private theorem embed_x (Q : QPoint) :
    (embed Q).xRep 0=algebraMap ℚ K (Q.xRep 0) := by
  cases Q <;> rfl

/-- The original rational witness has infinite order on the actual E0(Q). -/
theorem S_infinite_order : ¬IsOfFinAddOrder S := by
  intro hfin
  have hefin : IsOfFinAddOrder (embed ((S+S)+S)) := by
    obtain ⟨n,hn,he⟩:=isOfFinAddOrder_iff_nsmul_eq_zero.mp ((hfin.add hfin).add hfin)
    apply isOfFinAddOrder_iff_nsmul_eq_zero.mpr
    exact ⟨n,hn,by rw [←map_nsmul,he,map_zero]⟩
  apply infinite_order_of_negative_dyadic (embed ((S+S)+S)) _ _ hefin
  · rw [embed_x,S_triple_x]
    simp [QuadraticAlgebra.algebraMap_eq]
  · rw [embed_x,S_triple_x]
    change padicValRat 2 (-82206618201204652343709758199/199642521780828906626704:ℚ)<0
    exact negative_odd_even (-82206618201204652343709758199) 199642521780828906626704
      (by norm_num) (by norm_num) (by norm_num)

theorem embedded_S_infinite_order : ¬IsOfFinAddOrder (embed S) := by
  intro h
  obtain ⟨n,hn,he⟩:=isOfFinAddOrder_iff_nsmul_eq_zero.mp h
  apply S_infinite_order
  apply isOfFinAddOrder_iff_nsmul_eq_zero.mpr
  refine ⟨n,hn,?_⟩
  apply Point.map_injective (W':=E0.toAffine) (Algebra.ofId ℚ K)
  change embed (n•S)=embed 0
  simpa only [map_nsmul,map_zero] using he

/-- Every nonzero integer multiple of every point in the entire received
Galois-difference fiber is nonrational. -/
theorem nonzero_multiple_nonrational (P : KPoint) (hP : P-sigma P=T)
    (n : ℤ) (hn : n≠0) : ¬∃ Q : QPoint, embed Q=n•P := by
  rintro ⟨Q,hQ⟩
  have he : n•T=0 := by
    rw [←hP,smul_sub,←map_zsmul,←hQ,sigma_embed,sub_self]
  exact T_infinite_order (isOfFinAddOrder_iff_zsmul_eq_zero.mpr ⟨n,hn,he⟩)

theorem sigma_T : sigma T= -T := by
  change Point.some (conjugation tx) (conjugation ty) _=
    Point.some tx ((E0.toAffine.baseChange K).negY tx ty) _
  simp only [Point.some.injEq]
  constructor <;> ext <;>
    norm_num [tx,ty,conjugation,negY,E0,WeierstrassCurve.Affine.baseChange,
      WeierstrassCurve.map]

/-- Complete integer-coefficient independence of the received two witnesses. -/
theorem independent_witnesses (m n : ℤ)
    (h : m•embed S+n•T=0) : m=0 ∧ n=0 := by
  have hconj : m•embed S-n•T=0 := by
    have hh:=congrArg sigma h
    simpa only [map_add,map_zsmul,sigma_embed,sigma_T,smul_neg,map_zero,
      sub_eq_add_neg] using hh
  have htwice : (2*n)•T=0 := by
    calc
      (2*n)•T=(m•embed S+n•T)-(m•embed S-n•T) := by
        rw [mul_smul,two_smul]
        abel
      _ =0:=by rw [h,hconj];simp
  have hn : n=0 := by
    by_contra hn
    exact T_infinite_order (isOfFinAddOrder_iff_zsmul_eq_zero.mpr
      ⟨2*n,mul_ne_zero (by norm_num) hn,htwice⟩)
  refine ⟨?_,hn⟩
  by_contra hm
  have hmS : m•embed S=0:=by simpa [hn] using h
  exact embedded_S_infinite_order
    (isOfFinAddOrder_iff_zsmul_eq_zero.mpr ⟨m,hm,hmS⟩)

theorem two_witnesses_linearIndependent :
    LinearIndependent ℤ (![embed S,T] : Fin 2→KPoint) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hh : c 0•embed S+c 1•T=0:=by simpa [Fin.sum_univ_two] using hc
  obtain ⟨h0,h1⟩:=independent_witnesses (c 0) (c 1) hh
  intro i
  fin_cases i <;> assumption

/-- Rank lower bound only; no exact rank, full basis or saturation. -/
theorem quadratic_group_rank_lower : (2:Cardinal)≤Module.rank ℤ KPoint := by
  simpa using two_witnesses_linearIndependent.cardinal_le_rank

/-- Rational rank lower bound only, without an exact rank or full basis. -/
theorem rational_group_rank_lower : (1:Cardinal)≤Module.rank ℤ QPoint := by
  have hli : LinearIndependent ℤ (fun _ : Fin 1=>S) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc i
    have he : c 0•S=0 := by simpa [Fin.sum_univ_one] using hc
    have h0 : c 0=0 := by
      by_contra hn
      exact S_infinite_order (isOfFinAddOrder_iff_zsmul_eq_zero.mpr ⟨c 0,hn,he⟩)
    fin_cases i
    exact h0
  simpa using hli.cardinal_le_rank

end D5.S3.Combinatorics.SpectralGraph.ArithmeticCurves.A6DyadicInfiniteOrder
