/- GID: D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSecondMaximum/DescendingArithmetic
   generality: I
   mirror-B: none(waiver:private-consumed-construction)
   mirror-E: none(waiver:private-consumed-construction)
   anchors: [mathlib/module/Mathlib.Data.Int.ModEq]
   utility: none
   digest: Descending arithmetic for the physical first-peak joint lift. -/
import D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source

/-! DescendingArithmetic for the paired physical source construction. -/

set_option autoImplicit false
set_option relaxedAutoImplicit false
namespace D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSecondMaximum.Descending

private def D (y z : ℤ) : ℤ := y * z + y + 1
private def A (n y z t : ℤ) : ℤ := n * t * D y z + 1
private def B (n y t : ℤ) : ℤ := n * t ^ 2 * (y + 1) + t + 1
private def L (n z t : ℤ) : ℤ := n * z * t ^ 2 + z * t + z + 1
private def M (y z t : ℤ) : ℤ := t * y * z + D y z
private def E (n y z : ℤ) : ℤ := n * D y z
private def delta (n y z t : ℤ) : ℤ := A n y z t-n * M y z t
private def eps (n y z t R : ℤ) : ℤ := A n y z t-R * M y z t
private def width (n y z t R : ℤ) : ℤ := eps n y z t R + M y z t
private def cap (n y z t : ℤ) : ℤ :=
  (4 * B n y t-2 * L n z t + z-2 * E n y z-2)/4
private def reverseV (n y z t R : ℤ) : ℤ :=
  (cap n y z t-eps n y z t R)/A n y z t
-- Integer ceiling; its numerator may be NEGATIVE. No toNat before clamping.
private def reverseR (n y z t R : ℤ) : ℤ :=
  max 1 (-((-((reverseV n y z t R + 1) * A n y z t-cap n y z t))/M y z t))
private def oldSeam (corner : Bool) (n y z t r v : ℤ) : Fin 4 → ℤ :=
  let AA := A n y z t; let BB := B n y t; let LL := L n z t; let MM := M y z t
  if corner then ![AA-n * MM,BB-r * MM-v * AA,LL-r * MM,0]
  else ![AA-n * MM,LL-BB + (v + 1) * AA-r * MM,LL-r * MM,0]
private def newSeam (corner : Bool) (n y z t r v : ℤ) : Fin 4 → ℤ :=
  let AA := A n y z t; let BB := 2 * B n y t-1
  let LL := 2 * L n z t-z-1; let MM := 2 * M y z t-D y z
  if corner then ![2 * AA-n * MM,BB-r * MM-2 * v * AA,LL-r * MM,0]
  else ![2 * AA-n * MM,LL-BB + 2 * (v + 1) * AA-r * MM,LL-r * MM,0]
private def oldNext (corner : Bool) (n y z t : ℤ) : Fin 4 → ℤ :=
  if corner then ![A n y z t,B n y t,L n z t,M y z t]
  else ![A n y z t,L n z t,B n y t,M y z t]
private def newNext (corner : Bool) (n y z t : ℤ) : Fin 4 → ℤ :=
  if corner then ![A n y z t,2 * B n y t-1,2 * L n z t-z-1,2 * M y z t-D y z]
  else ![A n y z t,2 * L n z t-z-1,2 * B n y t-1,2 * M y z t-D y z]
private def Gates (corner : Bool) (n y z t r v : ℤ) : Prop :=
  ∀ j : Fin 4,
    (0 ≤ oldSeam corner n y z t r v j ∧ 
      2 * oldSeam corner n y z t r v j ≤ oldNext corner n y z t j-1) ∧ 
    (0 ≤ newSeam corner n y z t r v j ∧ 
      2 * newSeam corner n y z t r v j ≤ newNext corner n y z t j-1)

/- The first seam and its matching successor A in BOTH source rows. -/
private theorem first_gates (n y z t : ℤ)
    (hn : 2 ≤ n) (hz : 4 ≤ z) (hy : 2 * z ≤ y) (ht : y ≤ t) :
    0 ≤ delta n y z t ∧ 2 * delta n y z t ≤ A n y z t-1 ∧ 
    0 ≤ 2 * delta n y z t + E n y z ∧ 
    2 * (2 * delta n y z t + E n y z) ≤ A n y z t-1 := by
  have hn0 : 0<n := by omega
  have hy8 : 8 ≤ y := by omega
  have ht8 : 8 ≤ t := by omega
  have hD : 0 ≤ D y z := by dsimp [D]; positivity
  have hE : 0 ≤ E n y z := mul_nonneg (by omega) hD
  have hdiff : 0 ≤ y * (t-z) + (t-y)-1 := by
    have htz : 4 ≤ t-z := by omega
    have hm := mul_le_mul_of_nonneg_left htz (show 0 ≤ y by omega)
    nlinarith only [hm,hy8,ht]
  have hdid : delta n y z t=n * (y * (t-z) + (t-y)-1) + 1 := by
    dsimp [delta,A,M,D]; ring
  have hd : 0 ≤ delta n y z t := by rw [hdid]; positivity
  have hinner : 5 ≤ y * (z-3)-3 := by
    have hm := mul_le_mul_of_nonneg_left (show 1 ≤ z-3 by omega) (show 0 ≤ y by omega)
    nlinarith only [hm,hy8]
  have hprod : 40 ≤ t * (y * (z-3)-3) := by
    have h := mul_le_mul_of_nonneg_left hinner (show 0 ≤ t by omega)
    nlinarith only [h,ht8]
  have hslack : 0 ≤ n * (t * (y * (z-3)-3) + 2 * D y z)-4 := by
    have hQ : 40 ≤ t * (y * (z-3)-3) + 2 * D y z := by omega
    have h := mul_le_mul_of_nonneg_left hQ hn0.le
    nlinarith only [h,hn]
  have hid : A n y z t-1-2 * (2 * delta n y z t + E n y z)=
      n * (t * (y * (z-3)-3) + 2 * D y z)-4 := by
    dsimp [A,delta,E,M,D]; ring
  rw [←hid] at hslack
  exact ⟨hd,by omega,by omega,by omega⟩

/- Reverse discrete grid, including the negative-ceiling branch. -/
set_option maxHeartbeats 1600000 in
private theorem reverse_grid (AA BB LL MM EE zz tt RR : ℤ)
    (hA : 0<AA) (hM : 0<MM) (hR : 1 ≤ RR)
    (he : 0<AA-RR * MM) (hz : 2 ≤ zz)
    (hBL : 2 * LL + 1 ≤ BB) (hL : zz ≤ LL)
    (hE : 0 ≤ EE) (hwidth : 2 * (AA-(RR-1) * MM) ≤ LL-EE)
    (hcapacity : 2 * BB<tt * AA) :
    let epsilon := AA-RR * MM
    let G := epsilon + MM
    let C := (4 * BB-2 * LL + zz-2 * EE-2)/4
    let v := (C-epsilon)/AA
    let ceil := -((-((v + 1) * AA-C))/MM)
    let r := max 1 ceil
    let H := (v + 1) * AA-r * MM
    0 ≤ v ∧ 1 ≤ r ∧ r ≤ RR ∧ 0 ≤ C-H ∧ C-H<G ∧ 
      BB-LL<H ∧ H ≤ C ∧ 2 * v<tt ∧ 
      4 * C ≤ 4 * BB-2 * LL + zz-2 * EE-2 := by
  dsimp only
  let epsilon := AA-RR * MM
  let G := epsilon + MM
  let numerator := 4 * BB-2 * LL + zz-2 * EE-2
  let C := numerator/4
  let v := (C-epsilon)/AA
  let q := -((-((v + 1) * AA-C))/MM)
  let r := max 1 q
  let H := (v + 1) * AA-r * MM
  change 0 ≤ v ∧ 1 ≤ r ∧ r ≤ RR ∧ 0 ≤ C-H ∧ C-H<G ∧ 
    BB-LL<H ∧ H ≤ C ∧ 2 * v<tt ∧ 4 * C ≤ 4 * BB-2 * LL + zz-2 * EE-2
  have c0 := Int.emod_nonneg numerator (by norm_num : (4:ℤ) ≠ 0)
  have c1 := Int.emod_lt_of_pos numerator (by norm_num : (0:ℤ)<4)
  have ce := Int.emod_add_mul_ediv numerator 4
  change numerator%4 + 4 * C=numerator at ce
  have hcLower : BB-LL + G ≤ C := by dsimp [numerator,G,epsilon] at * ; nlinarith
  have hcUpper : C<BB := by dsimp [numerator] at * ; omega
  have hcEpsilon : epsilon ≤ C := by dsimp [G,epsilon] at * ; nlinarith
  have v0 := Int.emod_nonneg (C-epsilon) (ne_of_gt hA)
  have v1 := Int.emod_lt_of_pos (C-epsilon) hA
  have ve := Int.emod_add_mul_ediv (C-epsilon) AA
  change (C-epsilon)%AA + AA * v=C-epsilon at ve
  have hv : 0 ≤ v := by
    by_contra hneg
    have hv1 : v ≤ -1 := by omega
    have hm := mul_le_mul_of_nonneg_right hv1 hA.le
    nlinarith only [hm,ve,v1,hcEpsilon]
  have hvA : v * AA<C := by dsimp [epsilon] at * ; nlinarith
  have numeratorBound : (v + 1) * AA-C ≤ RR * MM := by dsimp [epsilon] at * ; nlinarith
  have q0 := Int.emod_nonneg (-((v + 1) * AA-C)) (ne_of_gt hM)
  have q1 := Int.emod_lt_of_pos (-((v + 1) * AA-C)) hM
  have qe := Int.emod_add_mul_ediv (-((v + 1) * AA-C)) MM
  have qeq : (-((v + 1) * AA-C))%MM-MM * q= -((v + 1) * AA-C) := by
    dsimp [q]; nlinarith only [qe]
  have qlo : (q-1) * MM<(v + 1) * AA-C := by nlinarith
  have qhi : (v + 1) * AA-C ≤ q * MM := by nlinarith
  have hqR : q ≤ RR := by
    by_contra hq
    have hle : RR ≤ q-1 := by omega
    have hm := mul_le_mul_of_nonneg_right hle hM.le
    nlinarith only [hm,qlo,numeratorBound]
  have hr : 1 ≤ r := le_max_left _ _
  have hrR : r ≤ RR := max_le hR hqR
  have hG : 0<G := by dsimp [G,epsilon]; omega
  have gap : 0 ≤ C-H ∧ C-H<G := by
    by_cases hq : 1 ≤ q
    · have er : r=q := max_eq_right hq
      dsimp [H]; rw [er]
      constructor <;> dsimp [G,epsilon] at * <;> nlinarith
    · have er : r=1 := max_eq_left (by omega)
      have hqM : q * MM ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (by omega) hM.le
      have hnum : (v + 1) * AA-C ≤ 0 := by omega
      dsimp [H]; rw [er]
      constructor <;> dsimp [G,epsilon] at * <;> nlinarith
  have hH : BB-LL<H := by omega
  have hvCap : 2 * v<tt := by
    have hm : (2 * v) * AA<tt * AA := by nlinarith only [hvA,hcUpper,hcapacity]
    exact (mul_lt_mul_iff_left₀ hA).mp hm
  exact ⟨hv,hr,hrR,gap.1,gap.2,hH,by omega,hvCap,by omega⟩

end D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSecondMaximum.Descending
