/- GID: D5/S3/Combinatorics/Circle/FourNegative/SecondPeakResidualTails/C2Gates
   generality: I
   mirror-B: D5/B/S3/Combinatorics/Circle/FourNegative/SecondPeakResidualTails/C2Gates
   mirror-E: none(waiver:physical-dependent-source-registration)
   anchors: [lake/module/D5.S3.Combinatorics.Circle.FourNegative.PacketNormalForm.Source]
   utility: none
   digest: Universal doubled gates for all five c2 bank charts. -/
import D5.S3.Combinatorics.Circle.FourNegative.SecondPeakResidualTails.C2Arithmetic

/-! Universal doubled gates for all five c2 bank charts. Original source owners supply the reused proofs. -/
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace D5.S3.Combinatorics.Circle.FourNegative.SecondPeakResidualTails
open scoped BigOperators

/-- With x=8,z=4,w=8h,y=16ht, these are exactly [A,B,L,K]. -/
def c2OldHead (h t : ℤ) : Fin 4 → ℤ :=
  ![9+640*h*t, 1+72*h+1024*h^2*t, 5+288*h, 1+80*h*t+512*h^2*t]

def c2NewHead (h t : ℤ) : Fin 4 → ℤ :=
  ![2*c2OldHead h t 0, 2*c2OldHead h t 1-1,
    2*c2OldHead h t 2-5, 2*c2OldHead h t 3-80*h*t-1]

def c2N (h t : ℤ) : ℤ := 4096*h^2*t-1
def c2Q (h t : ℤ) : ℤ := 2*c2N h t+1

def c2OldSuccessor (h t : ℤ) : Fin 4 → ℤ :=
  ![c2OldHead h t 1, c2OldHead h t 2, c2OldHead h t 3, c2OldHead h t 0]

/-- The last new successor is OLD A, including in the e=4 chart. -/
def c2NewSuccessor (h t : ℤ) : Fin 4 → ℤ :=
  ![c2NewHead h t 1, c2NewHead h t 2, c2NewHead h t 3, c2OldHead h t 0]

def c2OldDrop (h t : ℤ) : Fin 4 → ℤ :=
  ![1+36*h-1536*h^2*t, 3+144*h-2048*h^2*t,
    1+40*h*t-1792*h^2*t, 5+320*h*t-2048*h^2*t]

def c2NewDrop (h t : ℤ) : Fin 4 → ℤ :=
  ![1+72*h-3072*h^2*t, 3+288*h-4096*h^2*t,
    1+40*h*t-3584*h^2*t, 5+320*h*t-4096*h^2*t]

/-- Exact integer halves in the scalar model, with no division premise. -/
theorem c2_scalar_drops (h t : ℤ) (r : Fin 4) :
    2*c2OldDrop h t r = c2OldSuccessor h t r-c2N h t ∧
    2*c2NewDrop h t r = c2NewSuccessor h t r-c2Q h t ∧
    (c2OldSuccessor h t r-c2N h t)/2 = c2OldDrop h t r ∧
    (c2NewSuccessor h t r-c2Q h t)/2 = c2NewDrop h t r := by
  have ho : 2*c2OldDrop h t r = c2OldSuccessor h t r-c2N h t := by
    fin_cases r <;>
      norm_num [c2OldDrop,c2OldHead,c2OldSuccessor,c2N] <;> ring
  have hn : 2*c2NewDrop h t r = c2NewSuccessor h t r-c2Q h t := by
    fin_cases r <;>
      norm_num [c2NewDrop,c2NewHead,c2OldHead,c2NewSuccessor,c2Q,c2N] <;> ring
  exact ⟨ho,hn,by omega,by omega⟩

private def scalarMass (head : Fin 4 → ℤ) (M : Fin 4 → Fin 4 → ℤ)
    (row : Fin 4) : ℤ :=
  M row 0*head 0+M row 1*head 1+M row 2*head 2+M row 3*head 3

private def boundary2 (start : ℤ) (step : Fin 4 → ℤ) : Fin 5 → ℤ :=
  ![start, start+step 0, start+step 0+step 1,
    start+step 0+step 1+step 2, start+step 0+step 1+step 2+step 3]

private def oldBoundary2 (h t : ℤ) (M : Fin 4 → Fin 4 → ℤ)
    (order : Fin 4 → Fin 4) : Fin 5 → ℤ :=
  boundary2 0 (fun row =>
    2*scalarMass (c2OldHead h t) M row+c2OldSuccessor h t (order row)-c2N h t)

private def newBoundary2 (h t : ℤ) (M : Fin 4 → Fin 4 → ℤ)
    (order : Fin 4 → Fin 4) : Fin 5 → ℤ :=
  boundary2 (2*c2OldHead h t 0) (fun row =>
    2*scalarMass (c2NewHead h t) M row+c2NewSuccessor h t (order row)-c2Q h t)

/-- Exact four-column mask sums, with rows in physical bank order. -/
def c2OldMass (e ell : ℕ) (row : Fin 4) : ℤ :=
  scalarMass (c2OldHead (2^e) (2^ell)) (fun i j => (c2Banks e ell i j : ℤ)) row

def c2NewMass (e ell : ℕ) (row : Fin 4) : ℤ :=
  scalarMass (c2NewHead (2^e) (2^ell)) (fun i j => (c2Banks e ell i j : ℤ)) row

/-- H2_i = sum_{j<i}(2 oldMass_j+oldSuccessor(order_j)-N). -/
def c2OldBoundary2 (e ell : ℕ) : Fin 5 → ℤ :=
  oldBoundary2 (2^e) (2^ell) (fun i j => (c2Banks e ell i j : ℤ)) (c2Order e)

/-- G2_i = 2A+sum_{j<i}(2 newMass_j+newSuccessor(order_j)-Q). -/
def c2NewBoundary2 (e ell : ℕ) : Fin 5 → ℤ :=
  newBoundary2 (2^e) (2^ell) (fun i j => (c2Banks e ell i j : ℤ)) (c2Order e)

private def chart_one (h t a : ℤ) : Fin 4 → Fin 4 → ℤ :=
  ![![a,0,4*h*t,0], ![0,0,0,3], ![4*h-1-a,0,h*t,0], ![0,1,3*h*t-1,0]]
private def chart_two (h t a : ℤ) : Fin 4 → Fin 4 → ℤ :=
  ![![a,0,5*h*t,0], ![0,0,0,3], ![4*h-1-a,0,0,0], ![0,1,3*h*t-1,0]]
private def chart_three (h t a : ℤ) : Fin 4 → Fin 4 → ℤ :=
  ![![a,0,5*h*t,0], ![0,0,2*h*t,2], ![4*h-1-a,0,0,0], ![0,1,h*t-1,1]]
private def chart_high (h t a : ℤ) : Fin 4 → Fin 4 → ℤ :=
  ![![a,0,5*h*t,0], ![0,0,2*h*t+4*t,2], ![4*h-1-a,0,0,0],
    ![0,1,h*t-1-4*t,1]]
private def chart_sixteen (t : ℤ) : Fin 4 → Fin 4 → ℤ :=
  ![![45,0,0,0], ![0,0,112*t,0], ![18,1,0,0], ![0,0,16*t-1,3]]

private theorem gates_one (h t a : ℤ) (hh : 2 ≤ h) (ht : 1 ≤ t)
    (ha : 5*a+4 = 7*h) :
    (∀ row : Fin 4,
      0 ≤ oldBoundary2 h t (chart_one h t a) normalOrder row.succ ∧
      0 ≤ 2*c2N h t-(newBoundary2 h t (chart_one h t a) normalOrder row.castSucc+
        2*scalarMass (c2NewHead h t) (chart_one h t a) row)) ∧
    oldBoundary2 h t (chart_one h t a) normalOrder 4 = 0 ∧
    newBoundary2 h t (chart_one h t a) normalOrder 4 = 0 := by
  have hH : 0 ≤ h-2 := by omega
  have hz : 5*a+4-7*h = 0 := by linarith only [ha]
  have hT : 0 ≤ t-1 := by omega
  have hs0 : (0:ℤ) ≤ 1280 * a * h * t + 18 * a - 768 * h^2 * t + 40 * h * t + 72 * h + 2 := by
    have hp : 0 ≤ 5120 * (h - 2)^2 * (t - 1) + 5120 * (h - 2)^2 + 15560 * (h - 2) * (t - 1) + 16046 * (h - 2) + 10640 * (t - 1) + 11550 := by positivity
    have hi : 5*(1280 * a * h * t + 18 * a - 768 * h^2 * t + 40 * h * t + 72 * h + 2) = 5120 * (h - 2)^2 * (t - 1) + 5120 * (h - 2)^2 + 15560 * (h - 2) * (t - 1) + 16046 * (h - 2) + 10640 * (t - 1) + 11550 := by
      calc
        _ = 5120 * (h - 2)^2 * (t - 1) + 5120 * (h - 2)^2 + 15560 * (h - 2) * (t - 1) + 16046 * (h - 2) + 10640 * (t - 1) + 11550+(5*a+4-7*h)*(1280 * h * t + 18) := by ring
        _ = _ := by rw [hz]; ring
    linarith only [hi,hp]
  have hs1 : (0:ℤ) ≤ 1280 * a * h * t + 18 * a - 1792 * h^2 * t + 1160 * h * t + 72 * h + 18 := by
    have hp : 0 ≤ 680 * (h - 2) * (t - 1) + 1166 * (h - 2) + 1360 * (t - 1) + 2350 := by positivity
    have hi : 5*(1280 * a * h * t + 18 * a - 1792 * h^2 * t + 1160 * h * t + 72 * h + 18) = 680 * (h - 2) * (t - 1) + 1166 * (h - 2) + 1360 * (t - 1) + 2350 := by
      calc
        _ = 680 * (h - 2) * (t - 1) + 1166 * (h - 2) + 1360 * (t - 1) + 2350+(5*a+4-7*h)*(1280 * h * t + 18) := by ring
        _ = _ := by rw [hz]; ring
    linarith only [hi,hp]
  have hs2 : (0:ℤ) ≤ 320 * h^2 * t - 30 * h * t + 144 * h + 2 := by
    have hp : 0 ≤ 1600 * (h - 2)^2 * (t - 1) + 1600 * (h - 2)^2 + 6250 * (h - 2) * (t - 1) + 6970 * (h - 2) + 6100 * (t - 1) + 7550 := by positivity
    have hi : 5*(320 * h^2 * t - 30 * h * t + 144 * h + 2) = 1600 * (h - 2)^2 * (t - 1) + 1600 * (h - 2)^2 + 6250 * (h - 2) * (t - 1) + 6970 * (h - 2) + 6100 * (t - 1) + 7550 := by
      calc
        _ = 1600 * (h - 2)^2 * (t - 1) + 1600 * (h - 2)^2 + 6250 * (h - 2) * (t - 1) + 6970 * (h - 2) + 6100 * (t - 1) + 7550+(5*a+4-7*h)*(0) := by ring
        _ = _ := by rw [hz]; ring
    linarith only [hi,hp]
  have hp0 : (0:ℤ) ≤ -2560 * a * h * t - 36 * a + 3584 * h^2 * t - 1320 * h * t - 20 := by
    have hp : 0 ≤ 3640 * (h - 2) * (t - 1) + 3388 * (h - 2) + 7280 * (t - 1) + 6820 := by positivity
    have hi : 5*(-2560 * a * h * t - 36 * a + 3584 * h^2 * t - 1320 * h * t - 20) = 3640 * (h - 2) * (t - 1) + 3388 * (h - 2) + 7280 * (t - 1) + 6820 := by
      calc
        _ = 3640 * (h - 2) * (t - 1) + 3388 * (h - 2) + 7280 * (t - 1) + 6820+(5*a+4-7*h)*(-2560 * h * t - 36) := by ring
        _ = _ := by rw [hz]; ring
    linarith only [hi,hp]
  have hp1 : (0:ℤ) ≤ -2560 * a * h * t - 36 * a + 3584 * h^2 * t - 1800 * h * t - 144 * h - 28 := by
    have hp : 0 ≤ 1240 * (h - 2) * (t - 1) + 268 * (h - 2) + 2480 * (t - 1) + 540 := by positivity
    have hi : 5*(-2560 * a * h * t - 36 * a + 3584 * h^2 * t - 1800 * h * t - 144 * h - 28) = 1240 * (h - 2) * (t - 1) + 268 * (h - 2) + 2480 * (t - 1) + 540 := by
      calc
        _ = 1240 * (h - 2) * (t - 1) + 268 * (h - 2) + 2480 * (t - 1) + 540+(5*a+4-7*h)*(-2560 * h * t - 36) := by ring
        _ = _ := by rw [hz]; ring
    linarith only [hi,hp]
  have hp2 : (0:ℤ) ≤ 384 * h^2 * t + 110 * h * t - 288 * h - 2 := by
    have hp : 0 ≤ 1920 * (h - 2)^2 * (t - 1) + 1920 * (h - 2)^2 + 8230 * (h - 2) * (t - 1) + 6790 * (h - 2) + 8780 * (t - 1) + 5890 := by positivity
    have hi : 5*(384 * h^2 * t + 110 * h * t - 288 * h - 2) = 1920 * (h - 2)^2 * (t - 1) + 1920 * (h - 2)^2 + 8230 * (h - 2) * (t - 1) + 6790 * (h - 2) + 8780 * (t - 1) + 5890 := by
      calc
        _ = 1920 * (h - 2)^2 * (t - 1) + 1920 * (h - 2)^2 + 8230 * (h - 2) * (t - 1) + 6790 * (h - 2) + 8780 * (t - 1) + 5890+(5*a+4-7*h)*(0) := by ring
        _ = _ := by rw [hz]; ring
    linarith only [hi,hp]
  have hp3 : (0:ℤ) ≤ 576 * h + 4 := by
    have hp : 0 ≤ 2880 * (h - 2) + 5780 := by positivity
    have hi : 5*(576 * h + 4) = 2880 * (h - 2) + 5780 := by
      calc
        _ = 2880 * (h - 2) + 5780+(5*a+4-7*h)*(0) := by ring
        _ = _ := by rw [hz]; ring
    linarith only [hi,hp]
  refine ⟨?_,?_,?_⟩
  · intro row
    fin_cases row
    · constructor
      · convert hs0 using 1 <;> norm_num [oldBoundary2,newBoundary2,boundary2,scalarMass,c2OldHead,c2NewHead,
          c2OldSuccessor,c2NewSuccessor,c2N,c2Q,chart_one,normalOrder] <;> ring
      · convert hp0 using 1 <;> norm_num [oldBoundary2,newBoundary2,boundary2,scalarMass,c2OldHead,c2NewHead,
          c2OldSuccessor,c2NewSuccessor,c2N,c2Q,chart_one,normalOrder] <;> ring
    · constructor
      · convert hs1 using 1 <;> norm_num [oldBoundary2,newBoundary2,boundary2,scalarMass,c2OldHead,c2NewHead,
          c2OldSuccessor,c2NewSuccessor,c2N,c2Q,chart_one,normalOrder] <;> ring
      · convert hp1 using 1 <;> norm_num [oldBoundary2,newBoundary2,boundary2,scalarMass,c2OldHead,c2NewHead,
          c2OldSuccessor,c2NewSuccessor,c2N,c2Q,chart_one,normalOrder] <;> ring
    · constructor
      · convert hs2 using 1 <;> norm_num [oldBoundary2,newBoundary2,boundary2,scalarMass,c2OldHead,c2NewHead,
          c2OldSuccessor,c2NewSuccessor,c2N,c2Q,chart_one,normalOrder] <;> ring
      · convert hp2 using 1 <;> norm_num [oldBoundary2,newBoundary2,boundary2,scalarMass,c2OldHead,c2NewHead,
          c2OldSuccessor,c2NewSuccessor,c2N,c2Q,chart_one,normalOrder] <;> ring
    · constructor
      · convert (show (0:ℤ) ≤ 0 from le_rfl) using 1 <;>
          norm_num [oldBoundary2,newBoundary2,boundary2,scalarMass,c2OldHead,c2NewHead,
          c2OldSuccessor,c2NewSuccessor,c2N,c2Q,chart_one,normalOrder] <;> ring
      · convert hp3 using 1 <;> norm_num [oldBoundary2,newBoundary2,boundary2,scalarMass,c2OldHead,c2NewHead,
          c2OldSuccessor,c2NewSuccessor,c2N,c2Q,chart_one,normalOrder] <;> ring
  · norm_num [oldBoundary2,newBoundary2,boundary2,scalarMass,c2OldHead,c2NewHead,
          c2OldSuccessor,c2NewSuccessor,c2N,c2Q,chart_one,normalOrder] <;> ring
  · norm_num [oldBoundary2,newBoundary2,boundary2,scalarMass,c2OldHead,c2NewHead,
          c2OldSuccessor,c2NewSuccessor,c2N,c2Q,chart_one,normalOrder] <;> ring

private theorem gates_two (h t a : ℤ) (hh : 4 ≤ h) (ht : 1 ≤ t)
    (ha : 20*a+16 = 19*h) :
    (∀ row : Fin 4,
      0 ≤ oldBoundary2 h t (chart_two h t a) normalOrder row.succ ∧
      0 ≤ 2*c2N h t-(newBoundary2 h t (chart_two h t a) normalOrder row.castSucc+
        2*scalarMass (c2NewHead h t) (chart_two h t a) row)) ∧
    oldBoundary2 h t (chart_two h t a) normalOrder 4 = 0 ∧
    newBoundary2 h t (chart_two h t a) normalOrder 4 = 0 := by
  have hH : 0 ≤ h-4 := by omega
  have hz : 20*a+16-19*h = 0 := by linarith only [ha]
  have hT : 0 ≤ t-1 := by omega
  have hs0 : (0:ℤ) ≤ 1280 * a * h * t + 18 * a - 192 * h^2 * t + 50 * h * t + 72 * h + 2 := by
    have hp : 0 ≤ 20480 * (h - 4)^2 * (t - 1) + 20480 * (h - 4)^2 + 144360 * (h - 4) * (t - 1) + 146142 * (h - 4) + 249760 * (t - 1) + 256640 := by positivity
    have hi : 20*(1280 * a * h * t + 18 * a - 192 * h^2 * t + 50 * h * t + 72 * h + 2) = 20480 * (h - 4)^2 * (t - 1) + 20480 * (h - 4)^2 + 144360 * (h - 4) * (t - 1) + 146142 * (h - 4) + 249760 * (t - 1) + 256640 := by
      calc
        _ = 20480 * (h - 4)^2 * (t - 1) + 20480 * (h - 4)^2 + 144360 * (h - 4) * (t - 1) + 146142 * (h - 4) + 249760 * (t - 1) + 256640+(20*a+16-19*h)*(1280 * h * t + 18) := by ring
        _ = _ := by rw [hz]; ring
    linarith only [hi,hp]
  have hs1 : (0:ℤ) ≤ 1280 * a * h * t + 18 * a - 1216 * h^2 * t + 1170 * h * t + 72 * h + 18 := by
    have hp : 0 ≤ 2920 * (h - 4) * (t - 1) + 4702 * (h - 4) + 11680 * (t - 1) + 18880 := by positivity
    have hi : 20*(1280 * a * h * t + 18 * a - 1216 * h^2 * t + 1170 * h * t + 72 * h + 18) = 2920 * (h - 4) * (t - 1) + 4702 * (h - 4) + 11680 * (t - 1) + 18880 := by
      calc
        _ = 2920 * (h - 4) * (t - 1) + 4702 * (h - 4) + 11680 * (t - 1) + 18880+(20*a+16-19*h)*(1280 * h * t + 18) := by ring
        _ = _ := by rw [hz]; ring
    linarith only [hi,hp]
  have hs2 : (0:ℤ) ≤ 320 * h^2 * t - 30 * h * t + 144 * h + 2 := by
    have hp : 0 ≤ 6400 * (h - 4)^2 * (t - 1) + 6400 * (h - 4)^2 + 50600 * (h - 4) * (t - 1) + 53480 * (h - 4) + 100000 * (t - 1) + 111560 := by positivity
    have hi : 20*(320 * h^2 * t - 30 * h * t + 144 * h + 2) = 6400 * (h - 4)^2 * (t - 1) + 6400 * (h - 4)^2 + 50600 * (h - 4) * (t - 1) + 53480 * (h - 4) + 100000 * (t - 1) + 111560 := by
      calc
        _ = 6400 * (h - 4)^2 * (t - 1) + 6400 * (h - 4)^2 + 50600 * (h - 4) * (t - 1) + 53480 * (h - 4) + 100000 * (t - 1) + 111560+(20*a+16-19*h)*(0) := by ring
        _ = _ := by rw [hz]; ring
    linarith only [hi,hp]
  have hp0 : (0:ℤ) ≤ -2560 * a * h * t - 36 * a + 2432 * h^2 * t - 1330 * h * t - 20 := by
    have hp : 0 ≤ 14360 * (h - 4) * (t - 1) + 13676 * (h - 4) + 57440 * (t - 1) + 54880 := by positivity
    have hi : 20*(-2560 * a * h * t - 36 * a + 2432 * h^2 * t - 1330 * h * t - 20) = 14360 * (h - 4) * (t - 1) + 13676 * (h - 4) + 57440 * (t - 1) + 54880 := by
      calc
        _ = 14360 * (h - 4) * (t - 1) + 13676 * (h - 4) + 57440 * (t - 1) + 54880+(20*a+16-19*h)*(-2560 * h * t - 36) := by ring
        _ = _ := by rw [hz]; ring
    linarith only [hi,hp]
  have hp1 : (0:ℤ) ≤ -2560 * a * h * t - 36 * a + 2432 * h^2 * t - 1810 * h * t - 144 * h - 28 := by
    have hp : 0 ≤ 4760 * (h - 4) * (t - 1) + 1196 * (h - 4) + 19040 * (t - 1) + 4800 := by positivity
    have hi : 20*(-2560 * a * h * t - 36 * a + 2432 * h^2 * t - 1810 * h * t - 144 * h - 28) = 4760 * (h - 4) * (t - 1) + 1196 * (h - 4) + 19040 * (t - 1) + 4800 := by
      calc
        _ = 4760 * (h - 4) * (t - 1) + 1196 * (h - 4) + 19040 * (t - 1) + 4800+(20*a+16-19*h)*(-2560 * h * t - 36) := by ring
        _ = _ := by rw [hz]; ring
    linarith only [hi,hp]
  have hp2 : (0:ℤ) ≤ 384 * h^2 * t + 110 * h * t - 288 * h - 2 := by
    have hp : 0 ≤ 7680 * (h - 4)^2 * (t - 1) + 7680 * (h - 4)^2 + 63640 * (h - 4) * (t - 1) + 57880 * (h - 4) + 131680 * (t - 1) + 108600 := by positivity
    have hi : 20*(384 * h^2 * t + 110 * h * t - 288 * h - 2) = 7680 * (h - 4)^2 * (t - 1) + 7680 * (h - 4)^2 + 63640 * (h - 4) * (t - 1) + 57880 * (h - 4) + 131680 * (t - 1) + 108600 := by
      calc
        _ = 7680 * (h - 4)^2 * (t - 1) + 7680 * (h - 4)^2 + 63640 * (h - 4) * (t - 1) + 57880 * (h - 4) + 131680 * (t - 1) + 108600+(20*a+16-19*h)*(0) := by ring
        _ = _ := by rw [hz]; ring
    linarith only [hi,hp]
  have hp3 : (0:ℤ) ≤ 576 * h + 4 := by
    have hp : 0 ≤ 11520 * (h - 4) + 46160 := by positivity
    have hi : 20*(576 * h + 4) = 11520 * (h - 4) + 46160 := by
      calc
        _ = 11520 * (h - 4) + 46160+(20*a+16-19*h)*(0) := by ring
        _ = _ := by rw [hz]; ring
    linarith only [hi,hp]
  refine ⟨?_,?_,?_⟩
  · intro row
    fin_cases row
    · constructor
      · convert hs0 using 1 <;> norm_num [oldBoundary2,newBoundary2,boundary2,scalarMass,c2OldHead,c2NewHead,
          c2OldSuccessor,c2NewSuccessor,c2N,c2Q,chart_two,normalOrder] <;> ring
      · convert hp0 using 1 <;> norm_num [oldBoundary2,newBoundary2,boundary2,scalarMass,c2OldHead,c2NewHead,
          c2OldSuccessor,c2NewSuccessor,c2N,c2Q,chart_two,normalOrder] <;> ring
    · constructor
      · convert hs1 using 1 <;> norm_num [oldBoundary2,newBoundary2,boundary2,scalarMass,c2OldHead,c2NewHead,
          c2OldSuccessor,c2NewSuccessor,c2N,c2Q,chart_two,normalOrder] <;> ring
      · convert hp1 using 1 <;> norm_num [oldBoundary2,newBoundary2,boundary2,scalarMass,c2OldHead,c2NewHead,
          c2OldSuccessor,c2NewSuccessor,c2N,c2Q,chart_two,normalOrder] <;> ring
    · constructor
      · convert hs2 using 1 <;> norm_num [oldBoundary2,newBoundary2,boundary2,scalarMass,c2OldHead,c2NewHead,
          c2OldSuccessor,c2NewSuccessor,c2N,c2Q,chart_two,normalOrder] <;> ring
      · convert hp2 using 1 <;> norm_num [oldBoundary2,newBoundary2,boundary2,scalarMass,c2OldHead,c2NewHead,
          c2OldSuccessor,c2NewSuccessor,c2N,c2Q,chart_two,normalOrder] <;> ring
    · constructor
      · convert (show (0:ℤ) ≤ 0 from le_rfl) using 1 <;>
          norm_num [oldBoundary2,newBoundary2,boundary2,scalarMass,c2OldHead,c2NewHead,
          c2OldSuccessor,c2NewSuccessor,c2N,c2Q,chart_two,normalOrder] <;> ring
      · convert hp3 using 1 <;> norm_num [oldBoundary2,newBoundary2,boundary2,scalarMass,c2OldHead,c2NewHead,
          c2OldSuccessor,c2NewSuccessor,c2N,c2Q,chart_two,normalOrder] <;> ring
  · norm_num [oldBoundary2,newBoundary2,boundary2,scalarMass,c2OldHead,c2NewHead,
          c2OldSuccessor,c2NewSuccessor,c2N,c2Q,chart_two,normalOrder] <;> ring
  · norm_num [oldBoundary2,newBoundary2,boundary2,scalarMass,c2OldHead,c2NewHead,
          c2OldSuccessor,c2NewSuccessor,c2N,c2Q,chart_two,normalOrder] <;> ring

private theorem gates_three (h t a : ℤ) (hh : 8 ≤ h) (ht : 1 ≤ t)
    (ha : 20*a+16 = 17*h) :
    (∀ row : Fin 4,
      0 ≤ oldBoundary2 h t (chart_three h t a) normalOrder row.succ ∧
      0 ≤ 2*c2N h t-(newBoundary2 h t (chart_three h t a) normalOrder row.castSucc+
        2*scalarMass (c2NewHead h t) (chart_three h t a) row)) ∧
    oldBoundary2 h t (chart_three h t a) normalOrder 4 = 0 ∧
    newBoundary2 h t (chart_three h t a) normalOrder 4 = 0 := by
  have hH : 0 ≤ h-8 := by omega
  have hz : 20*a+16-17*h = 0 := by linarith only [ha]
  have hT : 0 ≤ t-1 := by omega
  have hs0 : (0:ℤ) ≤ 1280 * a * h * t + 18 * a - 192 * h^2 * t + 50 * h * t + 72 * h + 2 := by
    have hp : 0 ≤ 17920 * (h - 8)^2 * (t - 1) + 17920 * (h - 8)^2 + 267240 * (h - 8) * (t - 1) + 268986 * (h - 8) + 991040 * (t - 1) + 1004760 := by positivity
    have hi : 20*(1280 * a * h * t + 18 * a - 192 * h^2 * t + 50 * h * t + 72 * h + 2) = 17920 * (h - 8)^2 * (t - 1) + 17920 * (h - 8)^2 + 267240 * (h - 8) * (t - 1) + 268986 * (h - 8) + 991040 * (t - 1) + 1004760 := by
      calc
        _ = 17920 * (h - 8)^2 * (t - 1) + 17920 * (h - 8)^2 + 267240 * (h - 8) * (t - 1) + 268986 * (h - 8) + 991040 * (t - 1) + 1004760+(20*a+16-17*h)*(1280 * h * t + 18) := by ring
        _ = _ := by rw [hz]; ring
    linarith only [hi,hp]
  have hs1 : (0:ℤ) ≤ 1280 * a * h * t + 18 * a - 1088 * h^2 * t + 1030 * h * t + 72 * h + 16 := by
    have hp : 0 ≤ 120 * (h - 8) * (t - 1) + 1866 * (h - 8) + 960 * (t - 1) + 14960 := by positivity
    have hi : 20*(1280 * a * h * t + 18 * a - 1088 * h^2 * t + 1030 * h * t + 72 * h + 16) = 120 * (h - 8) * (t - 1) + 1866 * (h - 8) + 960 * (t - 1) + 14960 := by
      calc
        _ = 120 * (h - 8) * (t - 1) + 1866 * (h - 8) + 960 * (t - 1) + 14960+(20*a+16-17*h)*(1280 * h * t + 18) := by ring
        _ = _ := by rw [hz]; ring
    linarith only [hi,hp]
  have hs2 : (0:ℤ) ≤ 448 * h^2 * t - 170 * h * t + 144 * h := by
    have hp : 0 ≤ 8960 * (h - 8)^2 * (t - 1) + 8960 * (h - 8)^2 + 139960 * (h - 8) * (t - 1) + 142840 * (h - 8) + 546240 * (t - 1) + 569280 := by positivity
    have hi : 20*(448 * h^2 * t - 170 * h * t + 144 * h) = 8960 * (h - 8)^2 * (t - 1) + 8960 * (h - 8)^2 + 139960 * (h - 8) * (t - 1) + 142840 * (h - 8) + 546240 * (t - 1) + 569280 := by
      calc
        _ = 8960 * (h - 8)^2 * (t - 1) + 8960 * (h - 8)^2 + 139960 * (h - 8) * (t - 1) + 142840 * (h - 8) + 546240 * (t - 1) + 569280+(20*a+16-17*h)*(0) := by ring
        _ = _ := by rw [hz]; ring
    linarith only [hi,hp]
  have hp0 : (0:ℤ) ≤ -2560 * a * h * t - 36 * a + 2432 * h^2 * t - 1330 * h * t - 20 := by
    have hp : 0 ≤ 5120 * (h - 8)^2 * (t - 1) + 5120 * (h - 8)^2 + 96280 * (h - 8) * (t - 1) + 95668 * (h - 8) + 442560 * (t - 1) + 437840 := by positivity
    have hi : 20*(-2560 * a * h * t - 36 * a + 2432 * h^2 * t - 1330 * h * t - 20) = 5120 * (h - 8)^2 * (t - 1) + 5120 * (h - 8)^2 + 96280 * (h - 8) * (t - 1) + 95668 * (h - 8) + 442560 * (t - 1) + 437840 := by
      calc
        _ = 5120 * (h - 8)^2 * (t - 1) + 5120 * (h - 8)^2 + 96280 * (h - 8) * (t - 1) + 95668 * (h - 8) + 442560 * (t - 1) + 437840+(20*a+16-17*h)*(-2560 * h * t - 36) := by ring
        _ = _ := by rw [hz]; ring
    linarith only [hi,hp]
  have hp1 : (0:ℤ) ≤ -2560 * a * h * t - 36 * a + 2176 * h^2 * t - 1670 * h * t - 144 * h - 26 := by
    have hp : 0 ≤ 7560 * (h - 8) * (t - 1) + 4068 * (h - 8) + 60480 * (t - 1) + 32600 := by positivity
    have hi : 20*(-2560 * a * h * t - 36 * a + 2176 * h^2 * t - 1670 * h * t - 144 * h - 26) = 7560 * (h - 8) * (t - 1) + 4068 * (h - 8) + 60480 * (t - 1) + 32600 := by
      calc
        _ = 7560 * (h - 8) * (t - 1) + 4068 * (h - 8) + 60480 * (t - 1) + 32600+(20*a+16-17*h)*(-2560 * h * t - 36) := by ring
        _ = _ := by rw [hz]; ring
    linarith only [hi,hp]
  have hp2 : (0:ℤ) ≤ 128 * h^2 * t + 250 * h * t - 288 * h := by
    have hp : 0 ≤ 2560 * (h - 8)^2 * (t - 1) + 2560 * (h - 8)^2 + 45960 * (h - 8) * (t - 1) + 40200 * (h - 8) + 203840 * (t - 1) + 157760 := by positivity
    have hi : 20*(128 * h^2 * t + 250 * h * t - 288 * h) = 2560 * (h - 8)^2 * (t - 1) + 2560 * (h - 8)^2 + 45960 * (h - 8) * (t - 1) + 40200 * (h - 8) + 203840 * (t - 1) + 157760 := by
      calc
        _ = 2560 * (h - 8)^2 * (t - 1) + 2560 * (h - 8)^2 + 45960 * (h - 8) * (t - 1) + 40200 * (h - 8) + 203840 * (t - 1) + 157760+(20*a+16-17*h)*(0) := by ring
        _ = _ := by rw [hz]; ring
    linarith only [hi,hp]
  have hp3 : (0:ℤ) ≤ 576 * h + 4 := by
    have hp : 0 ≤ 11520 * (h - 8) + 92240 := by positivity
    have hi : 20*(576 * h + 4) = 11520 * (h - 8) + 92240 := by
      calc
        _ = 11520 * (h - 8) + 92240+(20*a+16-17*h)*(0) := by ring
        _ = _ := by rw [hz]; ring
    linarith only [hi,hp]
  refine ⟨?_,?_,?_⟩
  · intro row
    fin_cases row
    · constructor
      · convert hs0 using 1 <;> norm_num [oldBoundary2,newBoundary2,boundary2,scalarMass,c2OldHead,c2NewHead,
          c2OldSuccessor,c2NewSuccessor,c2N,c2Q,chart_three,normalOrder] <;> ring
      · convert hp0 using 1 <;> norm_num [oldBoundary2,newBoundary2,boundary2,scalarMass,c2OldHead,c2NewHead,
          c2OldSuccessor,c2NewSuccessor,c2N,c2Q,chart_three,normalOrder] <;> ring
    · constructor
      · convert hs1 using 1 <;> norm_num [oldBoundary2,newBoundary2,boundary2,scalarMass,c2OldHead,c2NewHead,
          c2OldSuccessor,c2NewSuccessor,c2N,c2Q,chart_three,normalOrder] <;> ring
      · convert hp1 using 1 <;> norm_num [oldBoundary2,newBoundary2,boundary2,scalarMass,c2OldHead,c2NewHead,
          c2OldSuccessor,c2NewSuccessor,c2N,c2Q,chart_three,normalOrder] <;> ring
    · constructor
      · convert hs2 using 1 <;> norm_num [oldBoundary2,newBoundary2,boundary2,scalarMass,c2OldHead,c2NewHead,
          c2OldSuccessor,c2NewSuccessor,c2N,c2Q,chart_three,normalOrder] <;> ring
      · convert hp2 using 1 <;> norm_num [oldBoundary2,newBoundary2,boundary2,scalarMass,c2OldHead,c2NewHead,
          c2OldSuccessor,c2NewSuccessor,c2N,c2Q,chart_three,normalOrder] <;> ring
    · constructor
      · convert (show (0:ℤ) ≤ 0 from le_rfl) using 1 <;>
          norm_num [oldBoundary2,newBoundary2,boundary2,scalarMass,c2OldHead,c2NewHead,
          c2OldSuccessor,c2NewSuccessor,c2N,c2Q,chart_three,normalOrder] <;> ring
      · convert hp3 using 1 <;> norm_num [oldBoundary2,newBoundary2,boundary2,scalarMass,c2OldHead,c2NewHead,
          c2OldSuccessor,c2NewSuccessor,c2N,c2Q,chart_three,normalOrder] <;> ring
  · norm_num [oldBoundary2,newBoundary2,boundary2,scalarMass,c2OldHead,c2NewHead,
          c2OldSuccessor,c2NewSuccessor,c2N,c2Q,chart_three,normalOrder] <;> ring
  · norm_num [oldBoundary2,newBoundary2,boundary2,scalarMass,c2OldHead,c2NewHead,
          c2OldSuccessor,c2NewSuccessor,c2N,c2Q,chart_three,normalOrder] <;> ring

private theorem gates_high (h t a : ℤ) (hh : 256 ≤ h) (ht : 1 ≤ t)
    (ha : 20*a+52 = 17*h) :
    (∀ row : Fin 4,
      0 ≤ oldBoundary2 h t (chart_high h t a) normalOrder row.succ ∧
      0 ≤ 2*c2N h t-(newBoundary2 h t (chart_high h t a) normalOrder row.castSucc+
        2*scalarMass (c2NewHead h t) (chart_high h t a) row)) ∧
    oldBoundary2 h t (chart_high h t a) normalOrder 4 = 0 ∧
    newBoundary2 h t (chart_high h t a) normalOrder 4 = 0 := by
  have hH : 0 ≤ h-256 := by omega
  have hz : 20*a+52-17*h = 0 := by linarith only [ha]
  have hT : 0 ≤ t-1 := by omega
  have hs0 : (0:ℤ) ≤ 1280 * a * h * t + 18 * a - 192 * h^2 * t + 50 * h * t + 72 * h + 2 := by
    have hp : 0 ≤ 17920 * (h - 256)^2 * (t - 1) + 17920 * (h - 256)^2 + 9109480 * (h - 256) * (t - 1) + 9111226 * (h - 256) + 1157621760 * (t - 1) + 1158067840 := by positivity
    have hi : 20*(1280 * a * h * t + 18 * a - 192 * h^2 * t + 50 * h * t + 72 * h + 2) = 17920 * (h - 256)^2 * (t - 1) + 17920 * (h - 256)^2 + 9109480 * (h - 256) * (t - 1) + 9111226 * (h - 256) + 1157621760 * (t - 1) + 1158067840 := by
      calc
        _ = 17920 * (h - 256)^2 * (t - 1) + 17920 * (h - 256)^2 + 9109480 * (h - 256) * (t - 1) + 9111226 * (h - 256) + 1157621760 * (t - 1) + 1158067840+(20*a+52-17*h)*(1280 * h * t + 18) := by ring
        _ = _ := by rw [hz]; ring
    linarith only [hi,hp]
  have hs1 : (0:ℤ) ≤ 1280 * a * h * t + 18 * a - 1088 * h^2 * t + 3334 * h * t + 72 * h + 40 * t + 16 := by
    have hp : 0 ≤ 120 * (h - 256) * (t - 1) + 1866 * (h - 256) + 31520 * (t - 1) + 477880 := by positivity
    have hi : 20*(1280 * a * h * t + 18 * a - 1088 * h^2 * t + 3334 * h * t + 72 * h + 40 * t + 16) = 120 * (h - 256) * (t - 1) + 1866 * (h - 256) + 31520 * (t - 1) + 477880 := by
      calc
        _ = 120 * (h - 256) * (t - 1) + 1866 * (h - 256) + 31520 * (t - 1) + 477880+(20*a+52-17*h)*(1280 * h * t + 18) := by ring
        _ = _ := by rw [hz]; ring
    linarith only [hi,hp]
  have hs2 : (0:ℤ) ≤ 448 * h^2 * t + 2134 * h * t + 144 * h + 40 * t := by
    have hp : 0 ≤ 8960 * (h - 256)^2 * (t - 1) + 8960 * (h - 256)^2 + 4630200 * (h - 256) * (t - 1) + 4633080 * (h - 256) + 598129440 * (t - 1) + 598866720 := by positivity
    have hi : 20*(448 * h^2 * t + 2134 * h * t + 144 * h + 40 * t) = 8960 * (h - 256)^2 * (t - 1) + 8960 * (h - 256)^2 + 4630200 * (h - 256) * (t - 1) + 4633080 * (h - 256) + 598129440 * (t - 1) + 598866720 := by
      calc
        _ = 8960 * (h - 256)^2 * (t - 1) + 8960 * (h - 256)^2 + 4630200 * (h - 256) * (t - 1) + 4633080 * (h - 256) + 598129440 * (t - 1) + 598866720+(20*a+52-17*h)*(0) := by ring
        _ = _ := by rw [hz]; ring
    linarith only [hi,hp]
  have hp0 : (0:ℤ) ≤ -2560 * a * h * t - 36 * a + 2432 * h^2 * t - 1330 * h * t - 20 := by
    have hp : 0 ≤ 5120 * (h - 256)^2 * (t - 1) + 5120 * (h - 256)^2 + 2727960 * (h - 256) * (t - 1) + 2727348 * (h - 256) + 362813440 * (t - 1) + 362658240 := by positivity
    have hi : 20*(-2560 * a * h * t - 36 * a + 2432 * h^2 * t - 1330 * h * t - 20) = 5120 * (h - 256)^2 * (t - 1) + 5120 * (h - 256)^2 + 2727960 * (h - 256) * (t - 1) + 2727348 * (h - 256) + 362813440 * (t - 1) + 362658240 := by
      calc
        _ = 5120 * (h - 256)^2 * (t - 1) + 5120 * (h - 256)^2 + 2727960 * (h - 256) * (t - 1) + 2727348 * (h - 256) + 362813440 * (t - 1) + 362658240+(20*a+52-17*h)*(-2560 * h * t - 36) := by ring
        _ = _ := by rw [hz]; ring
    linarith only [hi,hp]
  have hp1 : (0:ℤ) ≤ -2560 * a * h * t - 36 * a + 2176 * h^2 * t - 6278 * h * t - 144 * h - 40 * t - 26 := by
    have hp : 0 ≤ 7560 * (h - 256) * (t - 1) + 4068 * (h - 256) + 1934560 * (t - 1) + 1041960 := by positivity
    have hi : 20*(-2560 * a * h * t - 36 * a + 2176 * h^2 * t - 6278 * h * t - 144 * h - 40 * t - 26) = 7560 * (h - 256) * (t - 1) + 4068 * (h - 256) + 1934560 * (t - 1) + 1041960 := by
      calc
        _ = 7560 * (h - 256) * (t - 1) + 4068 * (h - 256) + 1934560 * (t - 1) + 1041960+(20*a+52-17*h)*(-2560 * h * t - 36) := by ring
        _ = _ := by rw [hz]; ring
    linarith only [hi,hp]
  have hp2 : (0:ℤ) ≤ 128 * h^2 * t - 4358 * h * t - 288 * h - 40 * t := by
    have hp : 0 ≤ 2560 * (h - 256)^2 * (t - 1) + 2560 * (h - 256)^2 + 1223560 * (h - 256) * (t - 1) + 1217800 * (h - 256) + 145458400 * (t - 1) + 143983840 := by positivity
    have hi : 20*(128 * h^2 * t - 4358 * h * t - 288 * h - 40 * t) = 2560 * (h - 256)^2 * (t - 1) + 2560 * (h - 256)^2 + 1223560 * (h - 256) * (t - 1) + 1217800 * (h - 256) + 145458400 * (t - 1) + 143983840 := by
      calc
        _ = 2560 * (h - 256)^2 * (t - 1) + 2560 * (h - 256)^2 + 1223560 * (h - 256) * (t - 1) + 1217800 * (h - 256) + 145458400 * (t - 1) + 143983840+(20*a+52-17*h)*(0) := by ring
        _ = _ := by rw [hz]; ring
    linarith only [hi,hp]
  have hp3 : (0:ℤ) ≤ 576 * h + 4 := by
    have hp : 0 ≤ 11520 * (h - 256) + 2949200 := by positivity
    have hi : 20*(576 * h + 4) = 11520 * (h - 256) + 2949200 := by
      calc
        _ = 11520 * (h - 256) + 2949200+(20*a+52-17*h)*(0) := by ring
        _ = _ := by rw [hz]; ring
    linarith only [hi,hp]
  refine ⟨?_,?_,?_⟩
  · intro row
    fin_cases row
    · constructor
      · convert hs0 using 1 <;> norm_num [oldBoundary2,newBoundary2,boundary2,scalarMass,c2OldHead,c2NewHead,
          c2OldSuccessor,c2NewSuccessor,c2N,c2Q,chart_high,normalOrder] <;> ring
      · convert hp0 using 1 <;> norm_num [oldBoundary2,newBoundary2,boundary2,scalarMass,c2OldHead,c2NewHead,
          c2OldSuccessor,c2NewSuccessor,c2N,c2Q,chart_high,normalOrder] <;> ring
    · constructor
      · convert hs1 using 1 <;> norm_num [oldBoundary2,newBoundary2,boundary2,scalarMass,c2OldHead,c2NewHead,
          c2OldSuccessor,c2NewSuccessor,c2N,c2Q,chart_high,normalOrder] <;> ring
      · convert hp1 using 1 <;> norm_num [oldBoundary2,newBoundary2,boundary2,scalarMass,c2OldHead,c2NewHead,
          c2OldSuccessor,c2NewSuccessor,c2N,c2Q,chart_high,normalOrder] <;> ring
    · constructor
      · convert hs2 using 1 <;> norm_num [oldBoundary2,newBoundary2,boundary2,scalarMass,c2OldHead,c2NewHead,
          c2OldSuccessor,c2NewSuccessor,c2N,c2Q,chart_high,normalOrder] <;> ring
      · convert hp2 using 1 <;> norm_num [oldBoundary2,newBoundary2,boundary2,scalarMass,c2OldHead,c2NewHead,
          c2OldSuccessor,c2NewSuccessor,c2N,c2Q,chart_high,normalOrder] <;> ring
    · constructor
      · convert (show (0:ℤ) ≤ 0 from le_rfl) using 1 <;>
          norm_num [oldBoundary2,newBoundary2,boundary2,scalarMass,c2OldHead,c2NewHead,
          c2OldSuccessor,c2NewSuccessor,c2N,c2Q,chart_high,normalOrder] <;> ring
      · convert hp3 using 1 <;> norm_num [oldBoundary2,newBoundary2,boundary2,scalarMass,c2OldHead,c2NewHead,
          c2OldSuccessor,c2NewSuccessor,c2N,c2Q,chart_high,normalOrder] <;> ring
  · norm_num [oldBoundary2,newBoundary2,boundary2,scalarMass,c2OldHead,c2NewHead,
          c2OldSuccessor,c2NewSuccessor,c2N,c2Q,chart_high,normalOrder] <;> ring
  · norm_num [oldBoundary2,newBoundary2,boundary2,scalarMass,c2OldHead,c2NewHead,
          c2OldSuccessor,c2NewSuccessor,c2N,c2Q,chart_high,normalOrder] <;> ring

private theorem gates_sixteen (t : ℤ) (ht : 1 ≤ t) :
    (∀ row : Fin 4,
      0 ≤ oldBoundary2 16 t (chart_sixteen t) (![2,3,0,1] : Fin 4 → Fin 4) row.succ ∧
      0 ≤ 2*c2N 16 t-(newBoundary2 16 t (chart_sixteen t) (![2,3,0,1] : Fin 4 → Fin 4) row.castSucc+
        2*scalarMass (c2NewHead 16 t) (chart_sixteen t) row)) ∧
    oldBoundary2 16 t (chart_sixteen t) (![2,3,0,1] : Fin 4 → Fin 4) 4 = 0 ∧
    newBoundary2 16 t (chart_sixteen t) (![2,3,0,1] : Fin 4 → Fin 4) 4 = 0 := by
  have hT : 0 ≤ t-1 := by omega
  have hs0 : (0:ℤ) ≤ 5376 * t + 812 := by
    have hi : (5376 * t + 812 : ℤ) = 5376 * (t - 1) + 6188 := by ring
    rw [hi]
    positivity
  have hs1 : (0:ℤ) ≤ 352 * t + 822 := by
    have hi : (352 * t + 822 : ℤ) = 352 * (t - 1) + 1174 := by ring
    rw [hi]
    positivity
  have hs2 : (0:ℤ) ≤ 106848 * t + 4606 := by
    have hi : (106848 * t + 4606 : ℤ) = 106848 * (t - 1) + 111454 := by ring
    rw [hi]
    positivity
  have hp0 : (0:ℤ) ≤ 233472 * t - 1640 := by
    have hi : (233472 * t - 1640 : ℤ) = 233472 * (t - 1) + 231832 := by ring
    rw [hi]
    positivity
  have hp1 : (0:ℤ) ≤ 1696 * t - 1642 := by
    have hi : (1696 * t - 1642 : ℤ) = 1696 * (t - 1) + 54 := by ring
    rw [hi]
    positivity
  have hp2 : (0:ℤ) ≤ 302752 * t - 6910 := by
    have hi : (302752 * t - 6910 : ℤ) = 302752 * (t - 1) + 295842 := by ring
    rw [hi]
    positivity
  have hp3 : (0:ℤ) ≤ 9220 := by
    norm_num
  refine ⟨?_,?_,?_⟩
  · intro row
    fin_cases row
    · constructor
      · convert hs0 using 1 <;> norm_num [oldBoundary2,newBoundary2,boundary2,scalarMass,c2OldHead,c2NewHead,
          c2OldSuccessor,c2NewSuccessor,c2N,c2Q,chart_sixteen,normalOrder] <;> ring
      · convert hp0 using 1 <;> norm_num [oldBoundary2,newBoundary2,boundary2,scalarMass,c2OldHead,c2NewHead,
          c2OldSuccessor,c2NewSuccessor,c2N,c2Q,chart_sixteen,normalOrder] <;> ring
    · constructor
      · convert hs1 using 1 <;> norm_num [oldBoundary2,newBoundary2,boundary2,scalarMass,c2OldHead,c2NewHead,
          c2OldSuccessor,c2NewSuccessor,c2N,c2Q,chart_sixteen,normalOrder] <;> ring
      · convert hp1 using 1 <;> norm_num [oldBoundary2,newBoundary2,boundary2,scalarMass,c2OldHead,c2NewHead,
          c2OldSuccessor,c2NewSuccessor,c2N,c2Q,chart_sixteen,normalOrder] <;> ring
    · constructor
      · convert hs2 using 1 <;> norm_num [oldBoundary2,newBoundary2,boundary2,scalarMass,c2OldHead,c2NewHead,
          c2OldSuccessor,c2NewSuccessor,c2N,c2Q,chart_sixteen,normalOrder] <;> ring
      · convert hp2 using 1 <;> norm_num [oldBoundary2,newBoundary2,boundary2,scalarMass,c2OldHead,c2NewHead,
          c2OldSuccessor,c2NewSuccessor,c2N,c2Q,chart_sixteen,normalOrder] <;> ring
    · constructor
      · convert (show (0:ℤ) ≤ 0 from le_rfl) using 1 <;>
          norm_num [oldBoundary2,newBoundary2,boundary2,scalarMass,c2OldHead,c2NewHead,
          c2OldSuccessor,c2NewSuccessor,c2N,c2Q,chart_sixteen,normalOrder] <;> ring
      · convert hp3 using 1 <;> norm_num [oldBoundary2,newBoundary2,boundary2,scalarMass,c2OldHead,c2NewHead,
          c2OldSuccessor,c2NewSuccessor,c2N,c2Q,chart_sixteen,normalOrder] <;> ring
  · norm_num [oldBoundary2,newBoundary2,boundary2,scalarMass,c2OldHead,c2NewHead,
          c2OldSuccessor,c2NewSuccessor,c2N,c2Q,chart_sixteen,normalOrder] <;> ring
  · norm_num [oldBoundary2,newBoundary2,boundary2,scalarMass,c2OldHead,c2NewHead,
          c2OldSuccessor,c2NewSuccessor,c2N,c2Q,chart_sixteen,normalOrder] <;> ring

/-- Natural subtractions are transported only after capacity, positivity
    and the exact high-tail transfer bound have been supplied. -/
private theorem c2_banks_cast (e ell : ℕ) (he : 1 ≤ e) :
    (fun i j => (c2Banks e ell i j : ℤ)) =
      if e = 4 then chart_sixteen (2^ell)
      else if e % 4 = 1 then chart_one (2^e) (2^ell) (c2Alpha e)
      else if e % 4 = 2 then chart_two (2^e) (2^ell) (c2Alpha e)
      else if e % 4 = 3 then chart_three (2^e) (2^ell) (c2Alpha e)
      else chart_high (2^e) (2^ell) (c2Alpha e) := by
  have hp := Nat.two_pow_pos e
  have ht := Nat.two_pow_pos ell
  have hq : 1 ≤ (2:ℕ)^e*2^ell := by
    have hpos : 0 < (2:ℕ)^e*2^ell := by positivity
    omega
  have h3q : 1 ≤ 3*((2:ℕ)^e*2^ell) := by omega
  have hu : 1 ≤ 4*(2:ℕ)^e := by omega
  have ha : c2Alpha e ≤ 4*(2:ℕ)^e-1 := by have := c2_alpha_capacity e he; omega
  have castU : ((4*(2:ℕ)^e-1-c2Alpha e : ℕ) : ℤ) =
      4*(2:ℤ)^e-1-(c2Alpha e : ℤ) := by
    rw [Nat.cast_sub ha,Nat.cast_sub hu]
    push_cast
    ring
  have castQ : (((2:ℕ)^e*2^ell-1 : ℕ) : ℤ) = (2:ℤ)^e*2^ell-1 := by
    rw [Nat.cast_sub hq]
    push_cast
    ring
  have cast3Q : ((3*((2:ℕ)^e*2^ell)-1 : ℕ) : ℤ) = 3*((2:ℤ)^e*2^ell)-1 := by
    rw [Nat.cast_sub h3q]
    push_cast
    ring
  by_cases h4 : e = 4
  · subst e
    funext i j
    fin_cases i <;> fin_cases j <;>
      simp [c2Banks,chart_sixteen,castQ] <;> ring
  · by_cases h1 : e % 4 = 1
    · funext i j
      fin_cases i <;> fin_cases j <;>
        simp [c2Banks,h4,h1,chart_one,castU,cast3Q] <;> ring
    · by_cases h2 : e % 4 = 2
      · funext i j
        fin_cases i <;> fin_cases j <;>
          simp [c2Banks,h4,h1,h2,chart_two,castU,cast3Q] <;> ring
      · by_cases h3 : e % 4 = 3
        · funext i j
          fin_cases i <;> fin_cases j <;>
            simp [c2Banks,h4,h1,h2,h3,chart_three,castU,castQ] <;> ring
        · have hx := c2_alpha_exact e he
          simp only [h4,h1,h2,h3,ite_false] at hx
          have htransfer := (c2_transfer e ell hx.1).2.1
          have hbit : 4*(2:ℕ)^ell ≤ (2:ℕ)^e*2^ell-1 := by omega
          have castHigh : (((2:ℕ)^e*2^ell-1-4*2^ell : ℕ) : ℤ) =
              (2:ℤ)^e*2^ell-1-4*2^ell := by
            rw [Nat.cast_sub hbit,castQ]
            push_cast
            ring
          funext i j
          fin_cases i <;> fin_cases j <;>
            simp [c2Banks,h4,h1,h2,h3,chart_high,castU,castHigh] <;> ring

/-- Every old lower seam and new upper peak, with no gate assumptions.
    row.succ indexes H2_(i+1); row.castSucc indexes G2_i.
    This is NOT a DataCertificate or an OriginalOrder statement. -/
theorem c2_doubled_gates (e ell : ℕ) (he : 1 ≤ e) :
    (∀ row : Fin 4, 0 ≤ c2OldBoundary2 e ell row.succ ∧
      c2NewBoundary2 e ell row.castSucc+2*c2NewMass e ell row ≤ 2*c2N (2^e) (2^ell)) ∧
    c2OldBoundary2 e ell 4 = 0 ∧ c2NewBoundary2 e ell 4 = 0 := by
  have htN : 1 ≤ (2:ℕ)^ell := by have := Nat.two_pow_pos ell; omega
  have ht : (1:ℤ) ≤ 2^ell := by exact_mod_cast htN
  have hx := c2_alpha_exact e he
  have margins :
      (∀ row : Fin 4,
        0 ≤ oldBoundary2 (2^e) (2^ell) (fun i j => (c2Banks e ell i j : ℤ)) (c2Order e) row.succ ∧
        0 ≤ 2*c2N (2^e) (2^ell)-
          (newBoundary2 (2^e) (2^ell) (fun i j => (c2Banks e ell i j : ℤ)) (c2Order e) row.castSucc+
            2*scalarMass (c2NewHead (2^e) (2^ell)) (fun i j => (c2Banks e ell i j : ℤ)) row)) ∧
      oldBoundary2 (2^e) (2^ell) (fun i j => (c2Banks e ell i j : ℤ)) (c2Order e) 4 = 0 ∧
      newBoundary2 (2^e) (2^ell) (fun i j => (c2Banks e ell i j : ℤ)) (c2Order e) 4 = 0 := by
    simp only [c2_banks_cast e ell he]
    by_cases h4 : e = 4
    · subst e
      simpa [c2Order] using gates_sixteen (2^ell) ht
    · simp only [h4,ite_false] at hx ⊢
      by_cases h1 : e % 4 = 1
      · simp only [h1,ite_true] at hx ⊢
        have hhN : 2 ≤ (2:ℕ)^e := by
          simpa using Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) he
        have hh : (2:ℤ) ≤ 2^e := by exact_mod_cast hhN
        have ha : 5*(c2Alpha e : ℤ)+4 = 7*(2:ℤ)^e := by exact_mod_cast hx
        simpa only [c2Order,h4,ite_false] using gates_one (2^e) (2^ell) (c2Alpha e) hh ht ha
      · simp only [h1,ite_false] at hx ⊢
        by_cases h2 : e % 4 = 2
        · simp only [h2,ite_true] at hx ⊢
          have hhN : 4 ≤ (2:ℕ)^e := by
            simpa using Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) (show 2 ≤ e by omega)
          have hh : (4:ℤ) ≤ 2^e := by exact_mod_cast hhN
          have ha : 20*(c2Alpha e : ℤ)+16 = 19*(2:ℤ)^e := by exact_mod_cast hx
          simpa only [c2Order,h4,ite_false] using gates_two (2^e) (2^ell) (c2Alpha e) hh ht ha
        · simp only [h2,ite_false] at hx ⊢
          by_cases h3 : e % 4 = 3
          · simp only [h3,ite_true] at hx ⊢
            have hhN : 8 ≤ (2:ℕ)^e := by
              simpa using Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) (show 3 ≤ e by omega)
            have hh : (8:ℤ) ≤ 2^e := by exact_mod_cast hhN
            have ha : 20*(c2Alpha e : ℤ)+16 = 17*(2:ℤ)^e := by exact_mod_cast hx
            simpa only [c2Order,h4,ite_false] using gates_three (2^e) (2^ell) (c2Alpha e) hh ht ha
          · simp only [h3,ite_false] at hx ⊢
            have hhN : 256 ≤ (2:ℕ)^e := by
              simpa using Nat.pow_le_pow_right (by decide : 0 < (2:ℕ)) hx.1
            have hh : (256:ℤ) ≤ 2^e := by exact_mod_cast hhN
            have ha : 20*(c2Alpha e : ℤ)+52 = 17*(2:ℤ)^e := by exact_mod_cast hx.2
            simpa only [c2Order,h4,ite_false] using gates_high (2^e) (2^ell) (c2Alpha e) hh ht ha
  refine ⟨?_,margins.2.1,margins.2.2⟩
  intro row
  refine ⟨(margins.1 row).1,?_⟩
  have hp := (margins.1 row).2
  change newBoundary2 (2^e) (2^ell) (fun i j => (c2Banks e ell i j : ℤ)) (c2Order e) row.castSucc+
    2*scalarMass (c2NewHead (2^e) (2^ell)) (fun i j => (c2Banks e ell i j : ℤ)) row ≤ _
  linarith only [hp]


end D5.S3.Combinatorics.Circle.FourNegative.SecondPeakResidualTails
