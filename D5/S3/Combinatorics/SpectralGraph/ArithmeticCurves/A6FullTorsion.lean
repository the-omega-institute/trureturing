/- GID: D5/S3/Combinatorics/SpectralGraph/ArithmeticCurves/A6FullTorsion
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/ArithmeticCurves/A6FullTorsion
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Full received rational and quadratic elliptic torsion conclusions -/
import D5.S3.Combinatorics.SpectralGraph.ArithmeticCurves.A6TorsionDyadicAlgebra
/-! Source: complete original S.torsion of Ma/Nikandish/Zhang, PR9
revision6d491f77b35dec808fc777b69939c56cdae5dc02. The original reduction
counts and prime-to-p-reduction method remain attributed source evidence.
This is an alternative proof through exact duplication/triplication,
dyadic infinite order and the full actual quadratic descent. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
open scoped Classical QuadraticAlgebra
namespace D5.S3.Combinatorics.SpectralGraph.ArithmeticCurves.A6FullTorsion
open WeierstrassCurve.Affine A6TorsionDyadicAlgebra A6QuadraticDescent
open A6EllipticModels A6GaloisCoset A6DyadicInfiniteOrder A6ModelEquivalences A6TorsionArithmetic
private instance : Fact (Nat.Prime 2):=⟨by decide⟩
private def short (A B : ℚ) : WeierstrassCurve ℚ:=⟨0,0,0,A,B⟩

private theorem double_some (A B x y : ℚ) [(short A B).IsElliptic]
    (h : (short A B).toAffine.Nonsingular x y) (hy : y≠0) :
    ∃ h',Point.some x y h+Point.some x y h=
      Point.some (doubleX A B x) (((3*x^2+A)/(2*y))*(x-doubleX A B x)-y) h' := by
  have hn : y≠(short A B).toAffine.negY x y := by
    intro he
    apply hy
    simp [negY,short] at he
    linarith
  have hf : y^2=cubic A B x := by
    have hh:=(equation_iff _ _).mp h.1
    simpa [short,cubic] using hh
  have hfn : cubic A B x≠0 := by rw [←hf];exact pow_ne_zero 2 hy
  have hx : (short A B).toAffine.addX x x ((short A B).toAffine.slope x x y y)=doubleX A B x := by
    rw [addX_self_of_Y_ne h.1 hn]
    dsimp [doubleX,numerator,cubic,short,WeierstrassCurve.b₂,
      WeierstrassCurve.b₄,WeierstrassCurve.b₆,WeierstrassCurve.b₈]
    congr 1 <;> ring
  have hy' : (short A B).toAffine.addY x x y ((short A B).toAffine.slope x x y y)=
      ((3*x^2+A)/(2*y))*(x-doubleX A B x)-y := by
    simp only [addY,negY,negAddY,hx]
    rw [slope_of_Y_ne rfl hn]
    simp only [short,negY]
    ring
  have hns:=nonsingular_add h h (fun hxy=>hn hxy.2)
  rw [hx,hy'] at hns
  refine ⟨hns,?_⟩
  rw [Point.add_self_of_Y_ne hn]
  simp only [Point.some.injEq]
  exact ⟨hx,hy'⟩

private theorem double_sub (A B x : ℚ) (hf : cubic A B x≠0) :
    doubleX A B x-x= -(psi3 A B x)/(4*cubic A B x) := by
  have hden : 4*cubic A B x≠0 := mul_ne_zero (by norm_num) hf
  apply (eq_div_iff hden).mpr
  dsimp [doubleX]
  rw [sub_mul,div_mul_cancel₀ _ hden]
  dsimp [numerator,psi3,cubic]
  ring

private theorem triple_some (A B x y : ℚ) [(short A B).IsElliptic]
    (h : (short A B).toAffine.Nonsingular x y) (hy : y≠0) (hD : psi3 A B x≠0) :
    ∃ y' h', (Point.some x y h+Point.some x y h)+Point.some x y h=
      Point.some (tripleX A B x) y' h' := by
  obtain ⟨h2,h2e⟩:=double_some A B x y h hy
  have hf : y^2=cubic A B x := by
    have hh:=(equation_iff _ _).mp h.1
    simpa [short,cubic] using hh
  have hfn : cubic A B x≠0 := by rw [←hf];exact pow_ne_zero 2 hy
  have hdiff : doubleX A B x-x≠0 := by
    rw [double_sub A B x hfn]
    exact div_ne_zero (neg_ne_zero.mpr hD) (mul_ne_zero (by norm_num) hfn)
  have hxne : doubleX A B x≠x := sub_ne_zero.mp hdiff
  have hx : (short A B).toAffine.addX (doubleX A B x) x
      ((short A B).toAffine.slope (doubleX A B x) x
        (((3*x^2+A)/(2*y))*(x-doubleX A B x)-y) y)=tripleX A B x := by
    rw [slope_of_X_ne hxne]
    simp only [addX,short,zero_mul,zero_add,sub_zero]
    have hs : (((3*x^2+A)/(2*y))*(x-doubleX A B x)-y-y)/(doubleX A B x-x)=
        -((3*x^2+A)/(2*y))-2*y/(doubleX A B x-x) := by
      field_simp [hdiff]
      <;> ring
    rw [hs,double_sub A B x hfn]
    dsimp [tripleX,doubleX]
    field_simp [hy,hD,hfn]
    dsimp [numerator,psi3,cubic,quartic4] at *
    linear_combination 4*(256*(x^3+A*x+B)^3*y^2-(3*x^2+A)^2*
      (3*x^4+6*A*x^2+12*B*x-A^2)^2)*hf
  have hns:=nonsingular_add h2 h (fun hxy=>hxne hxy.1)
  rw [hx] at hns
  refine ⟨_,hns,?_⟩
  rw [h2e,Point.add_of_X_ne hxne]
  simp only [Point.some.injEq]
  exact ⟨hx,trivial⟩

private theorem low_shift (q : ℚ) (hq : padicValRat 2 q < -2) :
    padicValRat 2 ((100*q-19920450)/9)<0 := by
  have hqn : q≠0 := by intro h;simp [h] at hq
  have han : 100*q≠0 := mul_ne_zero (by norm_num) hqn
  have hv100 : padicValRat 2 (100:ℚ)=2 := by
    rw [show (100:ℚ)=4*25 by norm_num,padicValRat.mul (by norm_num) (by norm_num)]
    have h4 : padicValRat 2 (4:ℚ)=2 := by
      rw [show (4:ℚ)=(2:ℚ)^2 by norm_num,padicValRat.pow]
      have hv2 : padicValRat 2 (2:ℚ)=1 := by
        simpa only [Nat.cast_ofNat] using (padicValRat.self (p:=2) (by decide))
      rw [hv2]
      norm_num
    rw [h4]
    norm_num [padicValRat_def]
  have ha : padicValRat 2 (100*q)=2+padicValRat 2 q := by
    rw [padicValRat.mul (by norm_num : (100:ℚ)≠0) hqn,hv100]
  have hb : 0≤padicValRat 2 (-19920450:ℚ) := by
    rw [padicValRat.neg]
    exact zero_le_padicValRat_of_nat 19920450
  have hab : 100*q+(-19920450)≠0 := by
    intro h
    have he : 100*q=(19920450:ℚ) := by linarith
    have hb' : 0≤padicValRat 2 (19920450:ℚ):=zero_le_padicValRat_of_nat _
    rw [he] at ha
    omega
  have habv:=padicValRat.add_eq_of_lt (p:=2) hab han (by norm_num : (-19920450:ℚ)≠0) (by omega)
  rw [sub_eq_add_neg,padicValRat.div hab (by norm_num : (9:ℚ)≠0),habv]
  have h9 : padicValRat 2 (9:ℚ)=0 := by norm_num [padicValRat_def]
  omega

private theorem low_short_lift (R : KPoint) (q : ℚ)
    (he : (shortKEquiv R).xRep 0=algebraMap ℚ K q)
    (hq : padicValRat 2 q < -2) : ¬IsOfFinAddOrder R := by
  cases R with
  | zero =>
    have hq1 : q=1 := by
      apply (algebraMap ℚ K).injective
      change algebraMap ℚ K q=algebraMap ℚ K 1
      have hh : shortKEquiv (0:KPoint)=0 := map_zero shortKEquiv
      change shortKEquiv (0:KPoint)=0 at hh
      rw [show (Point.zero:KPoint)=(0:KPoint) by rfl,hh] at he
      change (1:K)=algebraMap ℚ K q at he
      simpa only [map_one] using he.symm
    simp [hq1] at hq
  | some U V h =>
    obtain ⟨h',hh⟩:=shortK_some U V h
    rw [hh] at he
    change (9*U+19920450)/100=algebraMap ℚ K q at he
    have hu : U=algebraMap ℚ K ((100*q-19920450)/9) := by
      simp only [map_div₀,map_sub,map_mul,map_ofNat]
      linear_combination (100/9:K)*he
    apply infinite_order_of_negative_dyadic (.some U V h)
    · change U.im=0
      rw [hu]
      simp [QuadraticAlgebra.algebraMap_eq]
    · change padicValRat 2 U.re<0
      rw [hu]
      change padicValRat 2 (((100*q-19920450)/9):ℚ)<0
      exact low_shift q hq

private def embedShort : E.toAffine.Point →+ (E.baseChange K).toAffine.Point :=
  Point.baseChange (W':=E.toAffine) ℚ K

private theorem E_low (P : E.toAffine.Point)
    (hp : padicValRat 2 (P.xRep 0)< -2) : ¬IsOfFinAddOrder P := by
  intro hf
  let Q : (E.baseChange K).toAffine.Point := embedShort P
  let R:=shortKEquiv.symm Q
  have hR : IsOfFinAddOrder R := by
    obtain ⟨n,hn,he⟩:=isOfFinAddOrder_iff_nsmul_eq_zero.mp hf
    apply isOfFinAddOrder_iff_nsmul_eq_zero.mpr
    refine ⟨n,hn,?_⟩
    change n•shortKEquiv.symm Q=0
    rw [←map_nsmul]
    have hQ : n•Q=0 := by
      change n•embedShort P=0
      rw [←map_nsmul,he,map_zero]
    rw [hQ,map_zero]
  apply low_short_lift R (P.xRep 0) _ hp hR
  simp only [R,AddEquiv.apply_symm_apply]
  cases P <;> rfl

private theorem twist_low (P : Ed.toAffine.Point)
    (hp : padicValRat 2 (P.xRep 0)< -2) : ¬IsOfFinAddOrder P := by
  intro hf
  let Q:=twistKEquiv.symm (embedTwist P)
  let R:=shortKEquiv.symm Q
  have hR : IsOfFinAddOrder R := by
    obtain ⟨n,hn,he⟩:=isOfFinAddOrder_iff_nsmul_eq_zero.mp hf
    apply isOfFinAddOrder_iff_nsmul_eq_zero.mpr
    refine ⟨n,hn,?_⟩
    change n•shortKEquiv.symm (twistKEquiv.symm (embedTwist P))=0
    rw [←map_nsmul,←map_nsmul,←map_nsmul,he,map_zero,map_zero,map_zero]
  have hp0 : P≠0 := by
    intro he
    simp [he] at hp
  have hQ0 : Q≠0 := by
    intro hq
    have he:=congrArg twistKEquiv hq
    simp only [Q,AddEquiv.apply_symm_apply,map_zero] at he
    have hmap:=Point.map_injective (W':=Ed.toAffine) (Algebra.ofId ℚ K)
    apply hp0
    apply hmap
    change embedTwist P=embedTwist 0
    simpa only [map_zero] using he
  have hx : Q.xRep 0=algebraMap ℚ K (P.xRep 0/43645) := by
    have hE : twistKEquiv Q=embedTwist P := by simp [Q]
    cases hcase : Q with
    | zero => exact False.elim (hQ0 hcase)
    | some X Y h =>
      obtain ⟨h',hh⟩:=twistK_some X Y h
      rw [hcase,hh] at hE
      cases P with
      | zero => exact False.elim (hp0 rfl)
      | some x y g =>
        change Point.some (43645*X) (43645*sqrtD*Y) _=
          Point.some ((Algebra.ofId ℚ K) x) ((Algebra.ofId ℚ K) y) _ at hE
        have hX:=(Point.some.inj hE).1
        change X=algebraMap ℚ K (x/43645)
        simp only [map_div₀,map_ofNat]
        change X=(Algebra.ofId ℚ K) x/43645
        linear_combination (1/43645:K)*hX
  have hpv : padicValRat 2 (P.xRep 0/43645)< -2 := by
    have hpn : P.xRep 0≠0 := by intro h;simp [h] at hp
    rw [padicValRat.div hpn (by norm_num : (43645:ℚ)≠0)]
    have hvd : padicValRat 2 (43645:ℚ)=0 := by norm_num [padicValRat_def]
    omega
  apply low_short_lift R (P.xRep 0/43645) _ hpv hR
  simpa [R] using hx


private theorem full_torsion (A B : ℚ) [(short A B).IsElliptic]
    (hA : padicValRat 2 A=2) (hB : padicValRat 2 B=0) (hBn : B≠0)
    (h2 : ∀ P : (short A B).toAffine.Point,P+P=0→P=0)
    (h3 : ∀ x : ℚ,psi3 A B x≠0)
    (hlow : ∀ P : (short A B).toAffine.Point,
      padicValRat 2 (P.xRep 0)< -2→¬IsOfFinAddOrder P)
    (P : (short A B).toAffine.Point) (hfin : IsOfFinAddOrder P) : P=0 := by
  have ynz (x y : ℚ) (h : (short A B).toAffine.Nonsingular x y) : y≠0 := by
    intro hy
    have hh : Point.some x y h+Point.some x y h=0 := by
      apply Point.add_self_of_Y_eq
      simp [negY,short,hy]
    exact Point.some_ne_zero _ (h2 _ hh)
  have hfn (x y : ℚ) (h : (short A B).toAffine.Nonsingular x y) : cubic A B x≠0 := by
    have hh:=(equation_iff _ _).mp h.1
    have he : y^2=cubic A B x := by simpa [short,cubic] using hh
    rw [←he]
    exact pow_ne_zero _ (ynz x y h)
  have hnegative (Q : (short A B).toAffine.Point) (hf : IsOfFinAddOrder Q)
      (hv : padicValRat 2 (Q.xRep 0)<0) : False := by
    cases Q with
    | zero =>
      change padicValRat 2 (1:ℚ)<0 at hv
      norm_num at hv
    | some x y h =>
      obtain ⟨hd,he⟩:=double_some A B x y h (ynz x y h)
      have hdf : IsOfFinAddOrder (Point.some (doubleX A B x) _ hd) := by
        rw [←he]
        exact hf.add hf
      have hval:=double_negative A B x hA hB hv
      apply hlow _ _ hdf
      change padicValRat 2 (doubleX A B x)< -2
      change doubleX A B x≠0 ∧ padicValRat 2 (doubleX A B x)=padicValRat 2 x-2 at hval
      rw [hval.2]
      change padicValRat 2 x<0 at hv
      omega
  have hnonpositive (Q : (short A B).toAffine.Point) (hf : IsOfFinAddOrder Q)
      (hQ : Q≠0) (hn : Q.xRep 0≠0) (hv : padicValRat 2 (Q.xRep 0)≤0) : False := by
    by_cases hlt : padicValRat 2 (Q.xRep 0)<0
    · exact hnegative Q hf hlt
    have heq : padicValRat 2 (Q.xRep 0)=0 := by omega
    cases Q with
    | zero => exact hQ rfl
    | some x y h =>
      obtain ⟨hd,he⟩:=double_some A B x y h (ynz x y h)
      have hdf : IsOfFinAddOrder (Point.some (doubleX A B x) _ hd) := by
        rw [←he]
        exact hf.add hf
      have hval:=double_unit A B x hA hB hn heq (hfn x y h)
      exact hnegative _ hdf hval.2
  cases P with
  | zero => rfl
  | some x y h =>
    exfalso
    by_cases hx : x=0
    · obtain ⟨z,ht,he⟩:=triple_some A B x y h (ynz x y h) (h3 x)
      have htf : IsOfFinAddOrder (Point.some (tripleX A B x) z ht) := by
        rw [←he]
        exact (hfin.add hfin).add hfin
      obtain ⟨hn,hv⟩:=even_triple_nonpositive A B x hA hB hBn (Or.inl hx) (h3 x)
      exact hnonpositive _ htf (Point.some_ne_zero _) hn hv
    by_cases hv : padicValRat 2 x≤0
    · exact hnonpositive _ hfin (Point.some_ne_zero _) hx hv
    · obtain ⟨z,ht,he⟩:=triple_some A B x y h (ynz x y h) (h3 x)
      have htf : IsOfFinAddOrder (Point.some (tripleX A B x) z ht) := by
        rw [←he]
        exact (hfin.add hfin).add hfin
      obtain ⟨hn,hv⟩:=even_triple_nonpositive A B x hA hB hBn (Or.inr (show 0<padicValRat 2 x by omega)) (h3 x)
      exact hnonpositive _ htf (Point.some_ne_zero _) hn hv

private theorem coefficient_A_val : padicValRat 2 (-78162568812:ℚ)=2 := by
  rw [show (-78162568812:ℚ)=4*(-19540642203) by norm_num,
    padicValRat.mul (by norm_num) (by norm_num)]
  have h4 : padicValRat 2 (4:ℚ)=2 := by
    rw [show (4:ℚ)=(2:ℚ)^2 by norm_num,padicValRat.pow]
    have hv2 : padicValRat 2 (2:ℚ)=1 := by
      simpa only [Nat.cast_ofNat] using (padicValRat.self (p:=2) (by decide))
    rw [hv2]
    norm_num
  rw [h4]
  norm_num [padicValRat_def]

/-- Every finite-order point on the entire received rational short curve is zero. -/
theorem E_torsion_trivial (P : E.toAffine.Point) (hf : IsOfFinAddOrder P) : P=0 := by
  letI : (short (-78162568812) 8433576786332241).IsElliptic := by
    change E.IsElliptic
    infer_instance
  exact full_torsion (-78162568812) 8433576786332241
    coefficient_A_val
    (by norm_num [padicValRat_def]) (by norm_num)
    E_no_two_torsion E_psi3_no_root E_low P hf

/-- Every finite-order point on the entire received rational twist is zero. -/
theorem twist_torsion_trivial (P : Ed.toAffine.Point) (hf : IsOfFinAddOrder P) : P=0 := by
  have heq : Ed=short (43645^2*(-78162568812)) (43645^3*8433576786332241) := by
    ext <;> norm_num [Ed,integerTwist,short,WeierstrassCurve.map]
  have htwo:=twist_no_two_torsion
  have hlow:=twist_low
  have hell : Ed.IsElliptic:=inferInstance
  rw [heq] at htwo hlow hell
  letI := hell
  have hd : padicValRat 2 (43645:ℚ)=0 := by norm_num [padicValRat_def]
  have hb : padicValRat 2 (8433576786332241:ℚ)=0 := by norm_num [padicValRat_def]
  have hmain : ∀ Q : (short (43645^2*(-78162568812))
      (43645^3*8433576786332241)).toAffine.Point, IsOfFinAddOrder Q→Q=0 := full_torsion (43645^2*(-78162568812)) (43645^3*8433576786332241)
    (by
      rw [padicValRat.mul (pow_ne_zero _ (by norm_num)) (by norm_num),padicValRat.pow,
        coefficient_A_val,hd]
      norm_num)
    (by
      rw [padicValRat.mul (pow_ne_zero _ (by norm_num)) (by norm_num),padicValRat.pow,hd,hb]
      norm_num) (by norm_num)
    htwo twist_psi3_no_root hlow
  have hall : ∀ Q : Ed.toAffine.Point,IsOfFinAddOrder Q→Q=0 := by
    exact Eq.mp (congrArg (fun C : WeierstrassCurve ℚ =>
      ∀ Q : C.toAffine.Point, IsOfFinAddOrder Q→Q=0) heq.symm) hmain
  exact hall P hf

/-- Full rational E0 group, via the actual original model equivalence. -/
theorem E0Q_torsion_trivial (P : QPoint) (hf : IsOfFinAddOrder P) : P=0 := by
  apply shortQEquiv.injective
  rw [map_zero]
  apply E_torsion_trivial
  obtain ⟨n,hn,he⟩:=isOfFinAddOrder_iff_nsmul_eq_zero.mp hf
  apply isOfFinAddOrder_iff_nsmul_eq_zero.mpr
  exact ⟨n,hn,by rw [←map_nsmul,he,map_zero]⟩

/-- Full quadratic-field E0 group; no point list or reduction injection is assumed. -/
theorem E0K_torsion_trivial (P : KPoint) (hf : IsOfFinAddOrder P) : P=0 := by
  apply descent_injective
  rw [map_zero]
  apply Prod.ext
  · apply E0Q_torsion_trivial
    obtain ⟨n,hn,he⟩:=isOfFinAddOrder_iff_nsmul_eq_zero.mp hf
    apply isOfFinAddOrder_iff_nsmul_eq_zero.mpr
    exact ⟨n,hn,by change n•traceHom P=0;rw [←map_nsmul,he,map_zero]⟩
  · apply twist_torsion_trivial
    obtain ⟨n,hn,he⟩:=isOfFinAddOrder_iff_nsmul_eq_zero.mp hf
    apply isOfFinAddOrder_iff_nsmul_eq_zero.mpr
    exact ⟨n,hn,by change n•antiHom P=0;rw [←map_nsmul,he,map_zero]⟩

/-- Full quadratic-field group on the original short model E. -/
theorem EK_torsion_trivial (P : (E.baseChange K).toAffine.Point)
    (hf : IsOfFinAddOrder P) : P=0 := by
  have h := E0K_torsion_trivial (shortKEquiv.symm P) ?_
  · have he:=congrArg shortKEquiv h
    simpa using he
  obtain ⟨n,hn,he⟩:=isOfFinAddOrder_iff_nsmul_eq_zero.mp hf
  apply isOfFinAddOrder_iff_nsmul_eq_zero.mpr
  exact ⟨n,hn,by rw [←map_nsmul,he,map_zero]⟩

end D5.S3.Combinatorics.SpectralGraph.ArithmeticCurves.A6FullTorsion
