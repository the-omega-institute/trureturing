/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddlePolynomial
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddlePolynomial
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate.closed_box_exclusion; instance=D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowMiddleCertificate.closed_box_exclusion
   digest: Fixed four-variable polynomials and nonnegative homogeneous tensor evaluation. -/
import D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowHeadPolynomial
set_option autoImplicit false
set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowMiddlePolynomial
noncomputable section

open SixRowHeadPolynomial (row tensor tensor_nonneg)

def T138 (r : ℝ) : ℝ := 138*(1+r) - (2+r)^2/(4*(2421/324818 : ℝ))

def W (r H D a q : ℝ) : ℝ := a+q+r*(H+D)

def a0 (r H D q : ℝ) : ℝ := T138 r-q-r*(H+D)

def slack (r H D : ℝ) : ℝ := 6-15*r-H-D

def cn (r : ℝ) : ℝ := 4-8*r-5*r^2

def den (r : ℝ) : ℝ := 2-3*r

def p_mass (x0 x1 x2 x3 : ℝ) : ℝ :=
  3 + (-3)*x2 + (-3)*x1 + (-3 / 2 : ℝ)*x0

theorem mass_identity (r H D q : ℝ) :
    p_mass (10*(r-1/5)) (H/3) (D/3) (q/2) = slack r H D := by
  norm_num [p_mass, a0, T138, slack, cn, den] <;> ring

def p_qbox (x0 x1 x2 x3 : ℝ) : ℝ :=
  (-2)*x3 + 3*x2

theorem qbox_identity (r H D q : ℝ) :
    p_qbox (10*(r-1/5)) (H/3) (D/3) (q/2) = D - q := by
  norm_num [p_qbox, a0, T138, slack, cn, den] <;> ring

def p_qmass (x0 x1 x2 x3 : ℝ) : ℝ :=
  (-2)*x3 + 9*x2^2

theorem qmass_identity (r H D q : ℝ) :
    p_qmass (10*(r-1/5)) (H/3) (D/3) (q/2) = D^2 - q := by
  norm_num [p_qmass, a0, T138, slack, cn, den] <;> ring

def p_headsq (x0 x1 x2 x3 : ℝ) : ℝ :=
  (-394391 / 121050 : ℝ) + 2*x3 + (3 / 5 : ℝ)*x2 + (3 / 5 : ℝ)*x1 + 9*x1^2 + (116009 / 121050 : ℝ)*x0 + (3 / 10 : ℝ)*x0*x2 + (3 / 10 : ℝ)*x0*x1 + (162409 / 484200 : ℝ)*x0^2

theorem headsq_identity (r H D q : ℝ) :
    p_headsq (10*(r-1/5)) (H/3) (D/3) (q/2) = H^2 - a0 r H D q := by
  norm_num [p_headsq, a0, T138, slack, cn, den] <;> ring

def p_headcap (x0 x1 x2 x3 : ℝ) : ℝ :=
  (-2760737 / 605250 : ℝ) + (14 / 5 : ℝ)*x3 + (21 / 25 : ℝ)*x2 + (186 / 25 : ℝ)*x1 + (2807299 / 1210500 : ℝ)*x0 + (-3 / 5 : ℝ)*x0*x3 + (6 / 25 : ℝ)*x0*x2 + (-69 / 25 : ℝ)*x0*x1 + (440809 / 2421000 : ℝ)*x0^2 + (-9 / 100 : ℝ)*x0^2*x2 + (-6 / 25 : ℝ)*x0^2*x1 + (-162409 / 1614000 : ℝ)*x0^3

theorem headcap_identity (r H D q : ℝ) :
    p_headcap (10*(r-1/5)) (H/3) (D/3) (q/2) = cn r*H - den r*a0 r H D q := by
  norm_num [p_headcap, a0, T138, slack, cn, den] <;> ring

def p_headbox (x0 x1 x2 x3 : ℝ) : ℝ :=
  (9968941 / 3026250 : ℝ) + (98 / 25 : ℝ)*x3 + (147 / 125 : ℝ)*x2 + (-2163 / 125 : ℝ)*x1 + (441 / 25 : ℝ)*x1^2 + (-6332174 / 1513125 : ℝ)*x0 + (-42 / 25 : ℝ)*x0*x3 + (21 / 250 : ℝ)*x0*x2 + (3111 / 250 : ℝ)*x0*x1 + (-189 / 25 : ℝ)*x0*x1^2 + (6773783 / 6052500 : ℝ)*x0^2 + (9 / 50 : ℝ)*x0^2*x3 + (-99 / 500 : ℝ)*x0^2*x2 + (-789 / 500 : ℝ)*x0^2*x1 + (81 / 100 : ℝ)*x0^2*x1^2 + (4541 / 1008750 : ℝ)*x0^3 + (27 / 1000 : ℝ)*x0^3*x2 + (-63 / 1000 : ℝ)*x0^3*x1 + (189309 / 5380000 : ℝ)*x0^4

theorem headbox_identity (r H D q : ℝ) :
    p_headbox (10*(r-1/5)) (H/3) (D/3) (q/2) = (den r*H-cn r)^2 + (cn r)^2 - (den r)^2*a0 r H D q := by
  norm_num [p_headbox, a0, T138, slack, cn, den] <;> ring

def p_coupled (x0 x1 x2 x3 : ℝ) : ℝ :=
  (17179 / 121050 : ℝ) + (-2)*x3 + 1*x3^2 + (3 / 5 : ℝ)*x2 + (-3 / 5 : ℝ)*x1 + (43379 / 121050 : ℝ)*x0 + (3 / 10 : ℝ)*x0*x2 + (-3 / 10 : ℝ)*x0*x1 + (89779 / 484200 : ℝ)*x0^2

theorem coupled_identity (r H D q : ℝ) :
    p_coupled (10*(r-1/5)) (H/3) (D/3) (q/2) = (2-q/2)^2 - 2*r*H - 15*r^2 - a0 r H D q := by
  norm_num [p_coupled, a0, T138, slack, cn, den] <;> ring

def p_variance (x0 x1 x2 x3 : ℝ) : ℝ :=
  (1130839 / 169470 : ℝ) + (-4 / 7 : ℝ)*x3 + (-39 / 7 : ℝ)*x2 + (-18 / 7 : ℝ)*x2^2 + (-39 / 7 : ℝ)*x1 + (-6)*x1*x2 + (-18 / 7 : ℝ)*x1^2 + (-392401 / 169470 : ℝ)*x0 + (-39 / 14 : ℝ)*x0*x2 + (-39 / 14 : ℝ)*x0*x1 + (-346001 / 677880 : ℝ)*x0^2

theorem variance_identity (r H D q : ℝ) :
    p_variance (10*(r-1/5)) (H/3) (D/3) (q/2) = 4*slack r H D - (slack r H D)^2/3 + (H^2+D^2)/21 - (5/7)*a0 r H D q - q := by
  norm_num [p_variance, a0, T138, slack, cn, den] <;> ring

structure Necessary (x0 x1 x2 x3 : ℝ) : Prop where
  mass : 0 ≤ p_mass x0 x1 x2 x3
  qbox : 0 ≤ p_qbox x0 x1 x2 x3
  qmass : 0 ≤ p_qmass x0 x1 x2 x3
  headsq : 0 ≤ p_headsq x0 x1 x2 x3
  headcap : 0 ≤ p_headcap x0 x1 x2 x3
  headbox : 0 ≤ p_headbox x0 x1 x2 x3
  coupled : 0 ≤ p_coupled x0 x1 x2 x3
  variance : 0 ≤ p_variance x0 x1 x2 x3

/-- One outer row over the existing three-dimensional Nat tensor. -/
def tensor4 (cs : List (List (List (List ℕ))))
    (x0 X0 x1 X1 x2 X2 x3 X3 : ℝ) : ℝ :=
  row (cs.map (fun cube => tensor cube x1 X1 x2 X2 x3 X3)) x0 X0

theorem tensor4_nonneg (cs : List (List (List (List ℕ))))
    (x0 X0 x1 X1 x2 X2 x3 X3 : ℝ)
    (h0 : 0 ≤ x0) (h0' : 0 ≤ X0) (h1 : 0 ≤ x1) (h1' : 0 ≤ X1)
    (h2 : 0 ≤ x2) (h2' : 0 ≤ X2) (h3 : 0 ≤ x3) (h3' : 0 ≤ X3) :
    0 ≤ tensor4 cs x0 X0 x1 X1 x2 X2 x3 X3 := by
  induction cs with
  | nil => simp [tensor4, row]
  | cons cube cs ih =>
    simp only [tensor4, List.map_cons, row, List.length_map]
    exact add_nonneg
      (mul_nonneg (tensor_nonneg cube x1 X1 x2 X2 x3 X3 h1 h1' h2 h2' h3 h3')
        (pow_nonneg h0' _)) (mul_nonneg h0 ih)

end
end D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowMiddlePolynomial
