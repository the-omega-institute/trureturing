import D5.S0.Certificates.BoxCover.QuadraticCorner
set_option autoImplicit false
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1Algebra
open D5.S0.Certificates.BoxCover.QuadraticCorner
abbrev P := Fin 15 → ℚ
abbrev A := Fin 5 → ℚ
abbrev X := Fin 4 → ℝ
private def two (c u v d e f : ℚ) : Poly 2 :=
  .step (.step (.scalar c) (.scalar v) f)
    (.step (.scalar u) (.scalar e) 0) d
def toPoly (p : P) : Poly 4 :=
  .step (.step (two (p 0) (p 3) (p 4) (p 12) (p 13) (p 14))
      (two (p 2) (p 10) (p 11) 0 0 0) (p 9))
    (.step (two (p 1) (p 7) (p 8) 0 0 0)
      (two (p 6) 0 0 0 0 0) 0) (p 5)
noncomputable def ev (p : P) (x : X) : ℝ := value (toPoly p) x
noncomputable def av (a : A) (x : X) : ℝ :=
  (a 0 : ℝ)+(a 1 : ℝ)*x 0+(a 2 : ℝ)*x 1+(a 3 : ℝ)*x 2+(a 4 : ℝ)*x 3

theorem ev_formula (p : P) (x : X) : ev p x =
    (p 0 : ℝ)+(p 1 : ℝ)*x 0+(p 2 : ℝ)*x 1+(p 3 : ℝ)*x 2+(p 4 : ℝ)*x 3+
    (p 5 : ℝ)*(x 0)^2+(p 6 : ℝ)*x 0*x 1+(p 7 : ℝ)*x 0*x 2+
    (p 8 : ℝ)*x 0*x 3+(p 9 : ℝ)*(x 1)^2+(p 10 : ℝ)*x 1*x 2+
    (p 11 : ℝ)*x 1*x 3+(p 12 : ℝ)*(x 2)^2+(p 13 : ℝ)*x 2*x 3+
    (p 14 : ℝ)*(x 3)^2 := by
  norm_num [ev, toPoly, two, value, Fin.tail]
  ring

def addP (p q : P) : P := fun i => p i+q i
def scaleP (t : ℚ) (p : P) : P := fun i => t*p i
def affine (a : A) : P := ![a 0, a 1, a 2, a 3, a 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def mulA (a b : A) : P := ![a 0*b 0, a 0*b 1+b 0*a 1, a 0*b 2+b 0*a 2, a 0*b 3+b 0*a 3, a 0*b 4+b 0*a 4, a 1*b 1, a 1*b 2+a 2*b 1, a 1*b 3+a 3*b 1, a 1*b 4+a 4*b 1, a 2*b 2, a 2*b 3+a 3*b 2, a 2*b 4+a 4*b 2, a 3*b 3, a 3*b 4+a 4*b 3, a 4*b 4]
@[simp] theorem ev_add (p q : P) (x : X) : ev (addP p q) x = ev p x+ev q x := by
  simp only [ev_formula, addP, Rat.cast_add]; ring
@[simp] theorem ev_scale (t : ℚ) (p : P) (x : X) : ev (scaleP t p) x = (t : ℝ)*ev p x := by
  simp only [ev_formula, scaleP, Rat.cast_mul]; ring
@[simp] theorem ev_affine (a : A) (x : X) : ev (affine a) x = av a x := by
  simp [ev_formula, affine, av]
@[simp] theorem ev_mulA (a b : A) (x : X) : ev (mulA a b) x = av a x*av b x := by
  simp [ev_formula, mulA, av]; ring
def fixed : Fin 8 → P := ![![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0], ![4, 0, 0, 0, -2, -10, -2, 0, 0, 0, 0, 0, 0, 0, (1/4)], ![4, 0, 0, (-4/5), 0, -10, -2, 0, 0, 0, 0, 0, (1/25), 0, 0], ![15, 0, 0, 0, (-3/2), -60, -12, -12, 0, (-1/2), (-6/5), 0, (-1/2), 0, 0], ![0, 0, 2, 0, 0, 0, -1, 0, 0, 0, (-3/14), 0, 0, 0, 0], ![0, 0, 2, 0, 0, 0, -1, 0, 0, 0, 0, (-3/5), 0, 0, 0], ![0, 0, 3, 0, 0, 0, -3, 0, 0, 0, 0, -1, 0, 0, 0], ![0, 0, 4, 0, 0, 0, -6, 0, 0, 0, 0, -1, 0, 0, 0]]
def amin : P := ![0, 0, 0, 0, 0, 0, 0, 0, 0, (1/9), 0, 0, 0, 0, 0]
def necessary (branch : Bool) : Fin 17 → P := ![![5, -10, -1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, (-1/14), 0, 0], ![0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0], ![0, 0, 0, 1, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![3, -3, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![4, -6, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![2, -1, 0, 0, (-3/5), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], ![0, 0, 0, 0, 0, 0, 0, 0, 0, (8/9), 0, 0, 0, 0, 0], ![4, 0, 0, 0, -2, -10, -2, 0, 0, (-1/9), 0, 0, 0, 0, (1/4)], ![4, 0, 0, (-4/5), 0, -10, -2, 0, 0, (-1/9), 0, 0, (1/25), 0, 0], ![15, 0, 0, 0, (-3/2), -60, -12, -12, 0, (-11/18), (-6/5), 0, (-1/2), 0, 0], ![0, 0, 2, 0, 0, 0, -1, 0, 0, (-1/9), (-3/14), 0, 0, 0, 0], ![0, 0, 2, 0, 0, 0, -1, 0, 0, (-1/9), 0, (-3/5), 0, 0, 0], ![0, 0, 3, 0, 0, 0, -3, 0, 0, (-1/9), 0, -1, 0, 0, 0], ![0, 0, 4, 0, 0, 0, -6, 0, 0, (-1/9), 0, -1, 0, 0, 0], ![2, -1, (-1/9), 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], if branch then ![0, 0, 0, 2, -3, 0, 0, -1, 0, 0, (-1/9), 0, 0, 0, 0] else ![4, -4, (-4/9), 0, -1, 1, (2/9), 0, 0, (1/81), 0, 0, 0, 0, 0]]

def thetaQ (N : Nat) : ℚ := (N+8 : ℚ)/(N+2 : ℚ)^2
noncomputable def theta (N : ℝ) : ℝ := (N+8)/(N+2)^2
noncomputable def mass (N j r H D : ℝ) := N+j*r+H-D
noncomputable def energy (N j r H D q a : ℝ) :=
  N+2*j*r+j*r^2+2*(1+r)*H-2*D+a+q
noncomputable def gap (N j r H D q a : ℝ) :=
  theta N*(mass N j r H D)^2-energy N j r H D q a
noncomputable def charge (r H a : ℝ) := if H=0 then 2-r else 2-r-a/H

/-- The manuscript's scalar necessary inequalities. Neither a desired bound,
a numerical replay result nor an arbitrary box enclosure is a field. -/
structure Hyp (r H D q a : ℝ) : Prop where
  r0 : 0 ≤ r
  H0 : 0 ≤ H
  D0 : 0 ≤ D
  q0 : 0 ≤ q
  a0 : 0 ≤ a
  rhalf : r ≤ 1/2
  budget : H+D ≤ 5-10*r
  amin : H^2/9 ≤ a
  amax : a ≤ H^2
  qmin : D^2/14 ≤ q
  qD : q ≤ D
  qsq : q ≤ D^2
  starQ : a ≤ (2-q/2)^2-2*r*H-10*r^2
  starD : a ≤ (2-D/5)^2-2*r*H-10*r^2
  variance : (2/3)*(a-H^2/10)+(q-D^2/15) ≤
    4*(5-10*r-H-D)-(2/5)*(5-10*r-H-D)^2
  topD : a ≤ H*(2-r-3*D/14)
  topQ : a ≤ H*(2-r-3*q/5)
  subset3 : a ≤ H*(3-3*r-q)
  subset4 : a ≤ H*(4-6*r-q)
  q3 : q ≤ 3-3*r
  q4 : q ≤ 4-6*r
  topQ0 : 0 ≤ 2-r-3*q/5
  boxTail : q ≤ max 2 (2*D/3)
  charge0 : 0 ≤ charge r H a
  tail : q ≤ (charge r H a)^2 ∨ 3*q ≤ charge r H a*D

noncomputable def Branch (b : Bool) (r H D q a : ℝ) : Prop :=
  if b then 3*q ≤ charge r H a*D else q ≤ (charge r H a)^2

theorem charge_identity {r H D q a : ℝ} (h : Hyp r H D q a) :
    a = H*(2-r-charge r H a) := by
  by_cases hh : H=0
  · have ha : a=0 := by nlinarith [h.amax, h.a0]
    simp [charge, hh, ha]
  · simp only [charge, if_neg hh]
    field_simp
    ring

private theorem charge_le {r H D q a : ℝ} (h : Hyp r H D q a) :
    charge r H a ≤ 2-r-H/9 := by
  by_cases hh : H=0
  · simp [charge, hh]
  · have hp : 0 < H := lt_of_le_of_ne h.H0 (Ne.symm hh)
    have hm := (le_div_iff₀ hp).2 (show H/9*H ≤ a by nlinarith [h.amin])
    simp only [charge, if_neg hh]
    linarith

/-- All eight scalar elimination caps, with the original variance field. -/
theorem fixed_sound {r H D q a : ℝ} (h : Hyp r H D q a) (i : Fin 8) :
    a ≤ ev (fixed i) ![r,H,D,q] := by
  fin_cases i <;> norm_num [fixed, ev_formula]
  · exact h.amax
  · nlinarith [h.starQ]
  · nlinarith [h.starD]
  · nlinarith [h.variance]
  · nlinarith [h.topD]
  · nlinarith [h.topQ]
  · nlinarith [h.subset3]
  · nlinarith [h.subset4]

theorem necessary_sound {r H D q a : ℝ} (h : Hyp r H D q a)
    (b : Bool) (hb : Branch b r H D q a) (i : Fin 17) :
    0 ≤ ev (necessary b i) ![r,H,D,q] := by
  have hc := charge_le h
  have hc0 := h.charge0
  have hcm : 0 ≤ 2-r-H/9 := hc0.trans hc
  have hA : b=false → q ≤ (2-r-H/9)^2 := by
    intro he; subst b
    simp only [Branch, Bool.false_eq_true, if_false] at hb
    have hm := mul_nonneg (sub_nonneg.mpr hc) (add_nonneg hc0 hcm)
    nlinarith only [hb, hm]
  have hB : b=true → 3*q ≤ (2-r-H/9)*D := by
    intro he; subst b
    simp only [Branch, if_true] at hb
    have hm := mul_le_mul_of_nonneg_right hc h.D0
    linarith
  have caps : ∀ k : Fin 8, H^2/9 ≤ ev (fixed k) ![r,H,D,q] :=
    fun k => h.amin.trans (fixed_sound h k)
  fin_cases i <;> norm_num [necessary, ev_formula]
  · linarith [h.budget]
  · nlinarith [h.qmin]
  · nlinarith [h.qsq]
  · linarith [h.qD]
  · linarith [h.q3]
  · linarith [h.q4]
  · linarith [h.topQ0]
  · have hc := caps 0; norm_num [fixed, ev_formula] at hc; nlinarith [hc]
  · have hc := caps 1; norm_num [fixed, ev_formula] at hc; nlinarith [hc]
  · have hc := caps 2; norm_num [fixed, ev_formula] at hc; nlinarith [hc]
  · have hc := caps 3; norm_num [fixed, ev_formula] at hc; nlinarith [hc]
  · have hc := caps 4; norm_num [fixed, ev_formula] at hc; nlinarith [hc]
  · have hc := caps 5; norm_num [fixed, ev_formula] at hc; nlinarith [hc]
  · have hc := caps 6; norm_num [fixed, ev_formula] at hc; nlinarith [hc]
  · have hc := caps 7; norm_num [fixed, ev_formula] at hc; nlinarith [hc]
  · linarith
  · cases b with
    | false => have hh := hA rfl; norm_num at *; nlinarith only [hh]
    | true => have hh := hB rfl; norm_num at *; nlinarith only [hh]

def target (N : Nat) (j : ℚ) : P :=
  let s : A := ![(N : ℚ),j,1,-1,0]
  addP (addP (addP (scaleP (thetaQ N) (mulA s s))
    (scaleP (-1) (mulA ![2,1,0,0,0] s)))
    (affine ![(N : ℚ),(N : ℚ),0,0,-1]))
    (scaleP (-1) (mulA ![0,1,0,0,0] ![0,0,1,1,0]))
def vertex (N : Nat) : P :=
  addP (addP (affine ![(N : ℚ),(N : ℚ),0,0,-1])
    (scaleP (-1/(4*thetaQ N)) (mulA ![2,1,0,0,0] ![2,1,0,0,0])))
    (scaleP (-1) (mulA ![0,1,0,0,0] ![0,0,1,1,0]))
def derivative (N : Nat) (j : ℚ) : P :=
  affine ![2*thetaQ N*(N : ℚ)-2,2*thetaQ N*j-1,2*thetaQ N,-2*thetaQ N,0]

theorem theta_cast (N : Nat) : (thetaQ N : ℝ) = theta N := by
  simp [thetaQ, theta]

theorem target_value (N : Nat) (j : ℚ) (r H D q a : ℝ) :
    ev (target N j) ![r,H,D,q]-a = gap N j r H D q a := by
  simp [target, av, theta_cast, gap, mass, energy]
  ring

theorem derivative_value (N : Nat) (j : ℚ) (r H D q : ℝ) :
    ev (derivative N j) ![r,H,D,q] =
      2*theta N*(mass N j r H D)-(2+r) := by
  simp [derivative, av, theta_cast, mass]
  ring

theorem target_left (N j r H D q a : ℝ) (ht : 0 ≤ theta N)
    (hr : 0 ≤ r) (hj : 10 ≤ j)
    (hd : 0 ≤ 2*theta N*(mass N 10 r H D)-(2+r)) :
    gap N 10 r H D q a ≤ gap N j r H D q a := by
  have hmul := mul_nonneg (mul_nonneg (sub_nonneg.mpr hj) hr)
    (add_nonneg hd (mul_nonneg (mul_nonneg ht (sub_nonneg.mpr hj)) hr))
  dsimp [gap, mass, energy] at *
  nlinarith only [hmul]

theorem target_right (N j r H D q a : ℝ) (ht : 0 ≤ theta N)
    (hr : 0 ≤ r) (hj : j ≤ N-15)
    (hd : 2*theta N*(mass N (N-15) r H D)-(2+r) ≤ 0) :
    gap N (N-15) r H D q a ≤ gap N j r H D q a := by
  have hmul := mul_nonneg (mul_nonneg (sub_nonneg.mpr hj) hr)
    (add_nonneg (neg_nonneg.mpr hd)
      (mul_nonneg (mul_nonneg ht (sub_nonneg.mpr hj)) hr))
  dsimp [gap, mass, energy] at *
  nlinarith only [hmul]

theorem vertex_value (N : Nat) (j r H D q a : ℝ) (hN : 25 ≤ N) :
    ev (vertex N) ![r,H,D,q]-a ≤ gap N j r H D q a := by
  have hnr : (25 : ℝ) ≤ N := by exact_mod_cast hN
  have hn0 : (0 : ℝ) < N := by linarith
  have ht : 0 < theta N := by dsimp [theta]; positivity
  have hs := mul_nonneg (le_of_lt ht)
    (sq_nonneg (mass N j r H D-(2+r)/(2*theta N)))
  have he : gap N j r H D q a-(ev (vertex N) ![r,H,D,q]-a) =
      theta N*(mass N j r H D-(2+r)/(2*theta N))^2 := by
    simp [vertex, av, theta_cast, gap, mass, energy]
    field_simp
    <;> ring
  linarith

end D5.S3.Quantum.Entanglement.AbsolutePPT.FiveRowP1Algebra
