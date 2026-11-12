/- GID: D5/S3/Quantum/Recovery/FourPathNegativeFloor
   generality: G
   mirror-B: D5/B/S3/Quantum/Recovery/FourPathNegativeFloor
   mirror-E: none(waiver:original-negative-triangle-bound)
   anchors: []
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Recovery/FourPathNegativeFloor.negative_floor; premises=D5/S3/Quantum/Recovery/FourPathFloorCertificate.segment_majorants_lt_floor
   digest: A strict lower bound for the original negative four-path defect on the closed population interval. -/

import D5.S3.Quantum.Recovery.FourPathTriangleFibre
import D5.S3.Quantum.Recovery.FourPathFloorCertificate
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-! The fixed negative row of Definition 57.1, with its original nonnegative radicals. -/
set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.style.whitespace false

noncomputable section
namespace D5.S3.Quantum.Recovery.FourPathNegativeFloor
open FourPathTriangleFibre
set_option autoImplicit false
set_option maxHeartbeats 1400000

def h : ℝ := 1/Real.sqrt 2
def c : ℝ := Real.cos (Real.pi/8)
def s : ℝ := Real.sin (Real.pi/8)
def L (q : ℝ) : ℝ := 19/16+q/2
def R (q X Y : ℝ) : ℝ := Real.sqrt (s^2*X+h^2*Y+s*h*((L q)^2-X-Y))
def C (q X Y : ℝ) : ℝ := Real.sqrt (c^2*(1-X)+h^2*(1-Y)+2*c*h*F (L q) X Y)
def Gamma (q X Y : ℝ) : ℝ := Real.sqrt (1-q)*R q X Y+Real.sqrt q*C q X Y
def E (q : ℝ) : ℝ := (2*(h+s))^2*(1-q)+(2*(h+c))^2*q
def G (q X Y : ℝ) : ℝ := E q-4*(Gamma q X Y)^2

private lemma constants :
    7071/10000 < h ∧ h < 7072/10000 ∧
    3826/10000 < s ∧ s < 3827/10000 ∧
    4619/5000 < c ∧ c < 231/250 ∧
    h^2=1/2 ∧ h^2-s^2=h/2 ∧ c^2-h^2=h/2 ∧
    s*h < 271/1000 ∧ (h-s)^2 < 27/256 ∧
    c^2+h^2 < 677/500 ∧ c^2*h^2 < 427/1000 ∧
    1187/1000 < (h+s)^2 ∧ 5319/2000 < (h+c)^2 := by
  have r2 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  have rn := Real.sqrt_nonneg (2:ℝ)
  have rl : (1414213/1000000:ℝ) < Real.sqrt 2 := by nlinarith
  have ru : Real.sqrt 2 < (1414214/1000000:ℝ) := by nlinarith
  have hp : 0 < h := by unfold h; positivity
  have hh : h^2=1/2 := by unfold h; rw [div_pow,r2]; norm_num
  have hrh : Real.sqrt 2=2*h := by
    unfold h
    field_simp
    nlinarith only [r2]
  have cp : 0 < c := by unfold c; rw [Real.cos_pi_div_eight]; positivity
  have sp : 0 < s := by
    unfold s
    rw [Real.sin_pi_div_eight]
    exact div_pos (Real.sqrt_pos.mpr (by linarith)) (by norm_num)
  have cc : c^2=(2+Real.sqrt 2)/4 := by
    unfold c
    rw [Real.cos_pi_div_eight,div_pow,Real.sq_sqrt (by positivity)]
    norm_num
  have ss : s^2=(2-Real.sqrt 2)/4 := by
    unfold s
    rw [Real.sin_pi_div_eight,div_pow,Real.sq_sqrt (by linarith)]
    norm_num
  have hl : (7071/10000:ℝ) < h := by nlinarith only [hh,hp]
  have hu : h < (7072/10000:ℝ) := by nlinarith only [hh,hp]
  have sl : (3826/10000:ℝ) < s := by nlinarith only [ss,ru,sp]
  have su : s < (3827/10000:ℝ) := by nlinarith only [ss,rl,sp]
  have cl : (4619/5000:ℝ) < c := by nlinarith only [cc,rl,cp]
  have cu : c < (231/250:ℝ) := by nlinarith only [cc,ru,cp]
  refine ⟨hl,hu,sl,su,cl,cu,hh,by nlinarith only [hh,ss,hrh],
    by nlinarith only [hh,cc,hrh],?_,?_,?_,?_,?_,?_⟩
  · nlinarith only [mul_lt_mul su hu hp (by norm_num : (0:ℝ) ≤ 3827/10000)]
  · have ht : (h-s)^2 ≤ (3246/10000:ℝ)^2 :=
      (sq_le_sq₀ (by linarith : 0 ≤ h-s) (by norm_num)).mpr (by linarith)
    nlinarith only [ht]
  · nlinarith only [cc,hh,ru]
  · nlinarith only [congrArg (fun t : ℝ => c^2*t) hh,cc,ru]
  · have ht : (10897/10000:ℝ)^2 < (h+s)^2 :=
      (sq_lt_sq₀ (by norm_num) (by positivity)).mpr (by linarith)
    nlinarith only [ht]
  · have ht : (16309/10000:ℝ)^2 < (h+c)^2 :=
      (sq_lt_sq₀ (by norm_num) (by positivity)).mpr (by linarith)
    nlinarith only [ht]

private lemma parameter_bounds (q : ℝ) (hq : 11/100 ≤ q) (hq' : q ≤ 23/200) :
    1 < L q ∧ 77/50 < (L q)^2 ∧ (L q)^2 < 311/200 ∧
    0 ≤ Real.sqrt ((1-q)*q) ∧ Real.sqrt ((1-q)*q) < 8/25 := by
  have qn : 0 ≤ q := by linarith
  have pn : 0 ≤ 1-q := by linarith
  have sq := Real.sq_sqrt (show 0 ≤ (1-q)*q by positivity)
  have sn := Real.sqrt_nonneg ((1-q)*q)
  dsimp [L]
  refine ⟨by linarith,by nlinarith,by nlinarith,sn,?_⟩
  nlinarith [mul_nonneg (by linarith : 0 ≤ 23/200-q) (by linarith : 0 ≤ 177/200-q)]

private lemma energy_threshold (q : ℝ) (hq : 11/100 ≤ q) (hq' : q ≤ 23/200) :
    (49359:ℝ)/40000 < (E q-23/50)/4 := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,he,hd⟩ := constants
  have hp : 0 < 1-q := by linarith
  have qp : 0 < q := by linarith
  have he' := mul_lt_mul_of_pos_right he hp
  have hd' := mul_lt_mul_of_pos_right hd qp
  dsimp [E]
  nlinarith only [he',hd',hq]

private lemma original_radicals (q X Y : ℝ) (hq : 11/100 ≤ q) (hq' : q ≤ 23/200)
    (ht : Triangle (L q) X Y) :
    (R q X Y)^2=s^2*X+h^2*Y+s*h*((L q)^2-X-Y) ∧
    (C q X Y)^2=c^2*(1-X)+h^2*(1-Y)+2*c*h*F (L q) X Y := by
  obtain ⟨hl,hu,sl,su,cl,cu,hh,hs,hc,rest⟩ := constants
  obtain ⟨l1,al,au,rest'⟩ := parameter_bounds q hq hq'
  obtain ⟨hX,hX1,hY,hY1,htri⟩ := ht
  have fp : 0 ≤ F (L q) X Y := Real.sqrt_nonneg _
  have an : 0 ≤ (L q)^2-1 := by linarith
  have ds : 0 ≤ h-s := by linarith
  have xn : 0 ≤ 1-X := by linarith
  constructor
  · unfold R
    apply Real.sq_sqrt
    have nn : 0 ≤ s^2+s*h*((L q)^2-1)+s*(h-s)*(1-X)+h*(h-s)*Y := by positivity
    nlinarith only [nn]
  · unfold C
    apply Real.sq_sqrt
    positivity

private lemma gamma_support (q X Y : ℝ) (hq : 11/100 ≤ q) (hq' : q ≤ 23/200)
    (ht : Triangle (L q) X Y) :
    (Gamma q X Y)^2 ≤
      (131/100:ℝ)*(271/1000*(L q)^2+27/256*(X+Y)/2)+
      (37/100:ℝ)*(677/500)*(1-(X+Y)/2)+
      Real.sqrt ((185961:ℝ)/1250000*T ((L q)^2) (X+Y)) := by
  obtain ⟨hl,hu,sl,su,cl,cu,hh,hs,hc,sh,k2,S,ch2,he,hd⟩ := constants
  obtain ⟨l1,al,au,rn,ru⟩ := parameter_bounds q hq hq'
  have qn : 0 ≤ q := by linarith
  have pn : 0 ≤ 1-q := by linarith
  have hX := ht.1
  have hX1 := ht.2.1
  have hY := ht.2.2.1
  have hY1 := ht.2.2.2.1
  let r := Real.sqrt ((1-q)*q)
  let α := 1-q+13/10*r
  let β := q+10/13*r
  have an : 0 ≤ α := by dsimp [α,r]; positivity
  have bn : 0 ≤ β := by dsimp [β,r]; positivity
  have ab : α < 131/100 := by dsimp [α,r]; linarith
  have bb : β < 37/100 := by dsimp [β,r]; linarith
  have abb : α+β < 17/10 := by dsimp [α,β,r]; linarith
  obtain ⟨R2,C2⟩ := original_radicals q X Y hq hq' ht
  have gp : (Gamma q X Y)^2 ≤ α*(R q X Y)^2+β*(C q X Y)^2 := by
    have ps := Real.sq_sqrt pn
    have qs := Real.sq_sqrt qn
    have roots : Real.sqrt (1-q)*Real.sqrt q=r := (Real.sqrt_mul pn q).symm
    have id : (Gamma q X Y)^2=(1-q)*(R q X Y)^2+q*(C q X Y)^2+2*r*R q X Y*C q X Y := by
      unfold Gamma
      nlinarith only [congrArg (fun t : ℝ => t*(R q X Y)^2) ps,
        congrArg (fun t : ℝ => t*(C q X Y)^2) qs,
        congrArg (fun t : ℝ => 2*t*R q X Y*C q X Y) roots]
    dsimp [α,β]
    nlinarith only [id,mul_nonneg rn (sq_nonneg (13*R q X Y-10*C q X Y))]
  have ball := closed_triangle_ball (L q) X Y l1 (by linarith) ht
  have tn : 0 ≤ T ((L q)^2) (X+Y) := (by positivity : 0 ≤ (Y-X)^2+(2*F (L q) X Y)^2).trans ball
  let A := (α+β)*h/4
  let Q := β*c*h
  have coeff : A^2+Q^2 ≤ 185961/1250000 := by
    have ab2 : (α+β)^2 ≤ (17/10:ℝ)^2 :=
      (sq_le_sq₀ (by positivity) (by norm_num)).mpr abb.le
    have b2 : β^2 ≤ (37/100:ℝ)^2 := (sq_le_sq₀ bn (by norm_num)).mpr bb.le
    have x := mul_le_mul_of_nonneg_right ab2 (by norm_num : (0:ℝ) ≤ 1/32)
    have y := mul_le_mul b2 ch2.le (by positivity : 0 ≤ c^2*h^2) (by norm_num : (0:ℝ) ≤ (37/100)^2)
    dsimp [A,Q]
    nlinarith only [x,y,congrArg (fun t : ℝ => (α+β)^2/16*t) hh]
  have linear : A*(Y-X)+Q*(2*F (L q) X Y) ≤
      Real.sqrt ((185961:ℝ)/1250000*T ((L q)^2) (X+Y)) := by
    apply Real.le_sqrt_of_sq_le
    have hcauchy := sq_nonneg (A*(2*F (L q) X Y)-Q*(Y-X))
    have hb := mul_le_mul_of_nonneg_left ball (by positivity : 0 ≤ A^2+Q^2)
    have hc' := mul_le_mul_of_nonneg_right coeff tn
    nlinarith only [hcauchy,hb,hc']
  have identity : α*(R q X Y)^2+β*(C q X Y)^2 =
      α*(s*h*(L q)^2+(h-s)^2*(X+Y)/2)+
      β*(c^2+h^2)*(1-(X+Y)/2)+A*(Y-X)+Q*(2*F (L q) X Y) := by
    rw [R2,C2]
    dsimp [A,Q]
    nlinarith only [congrArg (fun t : ℝ => α*(Y-X)/2*t) hs,
      congrArg (fun t : ℝ => β*(Y-X)/2*t) hc]
  have x : α*(s*h*(L q)^2+(h-s)^2*(X+Y)/2) ≤
      (131/100:ℝ)*(271/1000*(L q)^2+27/256*(X+Y)/2) := by
    apply mul_le_mul ab.le _ (by positivity) (by norm_num)
    nlinarith only [mul_le_mul_of_nonneg_right sh.le (sq_nonneg (L q)),
      mul_le_mul_of_nonneg_right k2.le (show 0 ≤ (X+Y)/2 by positivity)]
  have y : β*(c^2+h^2)*(1-(X+Y)/2) ≤ (37/100:ℝ)*(677/500)*(1-(X+Y)/2) := by
    apply mul_le_mul_of_nonneg_right _ (by linarith)
    exact mul_le_mul bb.le S.le (by positivity) (by norm_num)
  linarith only [gp,identity,x,y,linear]

private lemma low_width_cap (a u v b : ℝ) (hu : 0 < u) (huv : u ≤ v)
    (hv : v ≤ 1) (ha : 77/50 ≤ a)
    (h₀ : 0 ≤ b*v^2-B v*D (77/50) v)
    (h₁ : 0 ≤ 6*(77/50)*v^2-2*(b+(77/50)*(8+77/50))*v+(77/50)*(8+4*(77/50)))
    (h₂ : 0 ≤ -6*(77/50)*v+b+(77/50)*(8+77/50)) : W a u ≤ b := by
  have dcap : D a u ≤ D (77/50) u := by
    dsimp [D]
    nlinarith only [mul_nonneg (sub_nonneg.mpr ha)
      (show 0 ≤ a+77/50-2*u by linarith)]
  have δ : 0 ≤ v-u := sub_nonneg.mpr huv
  have δ2 := sq_nonneg (v-u)
  have δ3 := mul_nonneg δ δ2
  have certificate : 0 ≤ b*u^2-B u*D (77/50) u := by
    have p₁ := mul_nonneg h₁ δ
    have p₂ := mul_nonneg h₂ δ2
    dsimp [B,D] at h₀ ⊢
    nlinarith only [h₀,p₁,p₂,δ3]
  unfold W
  apply (div_le_iff₀ (sq_pos_of_pos hu)).mpr
  calc
    B u*D a u ≤ B u*D (77/50) u := mul_le_mul_of_nonneg_left dcap (sq_nonneg _)
    _ ≤ b*u^2 := by linarith only [certificate]

/-- The full negative-row bound on every point of the original closed triangle. -/
theorem negative_floor (q X Y : ℝ) (hq : 11/100 ≤ q) (hq' : q ≤ 23/200)
    (hX : 0 ≤ X) (hX1 : X ≤ 1) (hY : 0 ≤ Y) (hY1 : Y ≤ 1)
    (htri : 19/16+q/2 ≤ Real.sqrt X+Real.sqrt Y) :
    (23:ℝ)/50 < G q X Y := by
  have ht : Triangle (L q) X Y := ⟨hX,hX1,hY,hY1,htri⟩
  obtain ⟨l1,al,au,rn,ru⟩ := parameter_bounds q hq hq'
  obtain ⟨Xp,Yp,up,tru,tB,tD,zle,fi⟩ := triangle_geometry (L q) X Y l1 (by linarith) ht
  let a := (L q)^2
  let u := X+Y
  let N := fun a u : ℝ =>
    (131/100:ℝ)*(271/1000*a+27/256*u/2)+(37/100:ℝ)*(677/500)*(1-u/2)
  have u2 : u ≤ 2 := by dsimp [u]; linarith
  have ul : a/2 ≤ u := by
    have dn : 0 ≤ D a u := (sq_nonneg (Y-X)).trans tD
    have ap : 0 < a := by dsimp [a]; positivity
    have : 0 ≤ 2*u-a := nonneg_of_mul_nonneg_right dn ap
    linarith
  have support := gamma_support q X Y hq hq' ht
  change (Gamma q X Y)^2 ≤ N a u+Real.sqrt ((185961:ℝ)/1250000*T a u) at support
  have row (i : Fin 7) (hn : N a u ≤ FourPathFloorCertificate.segmentNonroot i)
      (hr : (185961:ℝ)/1250000*T a u ≤ (FourPathFloorCertificate.segmentRadical i)^2) :
      (Gamma q X Y)^2 < (49359:ℝ)/40000 := by
    have rp : 0 ≤ FourPathFloorCertificate.segmentRadical i := by
      fin_cases i <;> norm_num [FourPathFloorCertificate.segmentRadical]
    have bound := Real.sqrt_le_iff.mpr ⟨rp,hr⟩
    have finite := FourPathFloorCertificate.segment_majorants_lt_floor i
    linarith only [support,hn,bound,finite]
  have lo (v b : ℝ) (huv : u ≤ v) (hv : v ≤ 1)
      (h₀ : 0 ≤ b*v^2-B v*D (77/50) v)
      (h₁ : 0 ≤ 6*(77/50)*v^2-2*(b+(77/50)*(8+77/50))*v+(77/50)*(8+4*(77/50)))
      (h₂ : 0 ≤ -6*(77/50)*v+b+(77/50)*(8+77/50)) : T a u ≤ b := by
    rw [T,ite_eq_left (huv.trans hv)]
    exact low_width_cap a u v b up huv hv al.le h₀ h₁ h₂
  have highB (hu1 : 1 < u) : T a u ≤ B u := by
    rw [T,ite_eq_right (not_le.mpr hu1)]
    exact min_le_left _ _
  have bcap (v : ℝ) (hvu : v ≤ u) : B u ≤ (2-v)^2 := by
    dsimp [B]
    nlinarith only [mul_nonneg (sub_nonneg.mpr hvu) (show 0 ≤ 4-u-v by linarith)]
  have result : (Gamma q X Y)^2 < (49359:ℝ)/40000 := by
    by_cases hu₀ : u ≤ 4/5
    · refine row 0 ?_ ?_
      · norm_num [FourPathFloorCertificate.segmentNonroot,N]
        dsimp [a] at ul ⊢
        nlinarith only [al,au,ul]
      · have cap := lo (4/5) (1/4) hu₀ (by norm_num)
          (by norm_num [B,D]) (by norm_num) (by norm_num)
        norm_num [FourPathFloorCertificate.segmentRadical]
        linarith only [cap]
    by_cases hu₁ : u ≤ 9/10
    · refine row 1 ?_ ?_
      · norm_num [FourPathFloorCertificate.segmentNonroot,N]
        dsimp [a]
        nlinarith only [au,hu₀]
      · have cap := lo (9/10) (2/3) hu₁ (by norm_num)
          (by norm_num [B,D]) (by norm_num) (by norm_num)
        norm_num [FourPathFloorCertificate.segmentRadical]
        linarith only [cap]
    by_cases hu₂ : u ≤ 1
    · refine row 2 ?_ ?_
      · norm_num [FourPathFloorCertificate.segmentNonroot,N]
        dsimp [a]
        nlinarith only [au,hu₁]
      · have cap := lo 1 (3/4) hu₂ (by norm_num)
          (by norm_num [B,D]) (by norm_num) (by norm_num)
        norm_num [FourPathFloorCertificate.segmentRadical]
        linarith only [cap]
    have u1 : 1 < u := not_le.mp hu₂
    by_cases hu₃ : u ≤ 21/20
    · refine row 3 ?_ ?_
      · norm_num [FourPathFloorCertificate.segmentNonroot,N]
        dsimp [a]
        nlinarith only [au,u1]
      · have td : T a u ≤ D a u := by
          rw [T,ite_eq_right hu₂]
          exact min_le_right _ _
        have dcap : D a u ≤ (539:ℝ)/625 := by
          dsimp [D]
          nlinarith only [mul_nonneg (show 0 ≤ a-77/50 by linarith only [al])
            (show 0 ≤ a+77/50-2*u by linarith only [al,hu₃]),hu₃]
        norm_num [FourPathFloorCertificate.segmentRadical]
        linarith only [td,dcap]
    by_cases hu₄ : u ≤ 11/10
    · have cap := (highB u1).trans (bcap (21/20) (by linarith))
      have root : Real.sqrt ((185961:ℝ)/1250000*T a u) ≤ 367/1000 := by
        apply Real.sqrt_le_iff.mpr
        constructor
        · norm_num
        · nlinarith only [cap]
      have nonroot : N a u ≤ (552026997:ℝ)/640000000 := by
        dsimp [N,a]
        nlinarith only [au,hu₃]
      linarith only [support,root,nonroot]
    by_cases hu₅ : u ≤ 6/5
    · refine row 4 ?_ ?_
      · norm_num [FourPathFloorCertificate.segmentNonroot,N]
        dsimp [a]
        nlinarith only [au,hu₄]
      · have cap := (highB u1).trans (bcap (11/10) (by linarith))
        norm_num [FourPathFloorCertificate.segmentRadical]
        nlinarith only [cap]
    by_cases hu₆ : u ≤ 13/10
    · refine row 5 ?_ ?_
      · norm_num [FourPathFloorCertificate.segmentNonroot,N]
        dsimp [a]
        nlinarith only [au,hu₅]
      · have cap := (highB u1).trans (bcap (6/5) (by linarith))
        norm_num [FourPathFloorCertificate.segmentRadical]
        nlinarith only [cap]
    · refine row 6 ?_ ?_
      · norm_num [FourPathFloorCertificate.segmentNonroot,N]
        dsimp [a]
        nlinarith only [au,hu₆]
      · have cap := (highB u1).trans (bcap (13/10) (by linarith))
        norm_num [FourPathFloorCertificate.segmentRadical]
        nlinarith only [cap]
  have energy := energy_threshold q hq hq'
  unfold G
  linarith only [result,energy]

end D5.S3.Quantum.Recovery.FourPathNegativeFloor
