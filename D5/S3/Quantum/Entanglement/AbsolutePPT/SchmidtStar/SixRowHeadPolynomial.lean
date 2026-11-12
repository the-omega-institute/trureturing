/- GID: D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadPolynomial
   generality: G
   mirror-B: D5/B/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadPolynomial
   mirror-E: none(waiver:noncomputational)
   anchors: []
   utility: kind=checker; basis=consumer=D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadScalar.half_angle_bound; instance=D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadCertificate.polynomial_nonneg
   digest: Exact scalar polynomial and homogeneous Bernstein evaluation for the K6 head. -/
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic
set_option autoImplicit false
namespace D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowHeadPolynomial
noncomputable section

def P (z k h : ℝ) : ℝ :=
  (((8 + h*-4) + k*((47 + h*(-16 + h*-4)) + k*((66 + h*(12 + h*-24)) + k*(-9 + h*(72 + h*-36))))) + z*(((0 + h*16) + k*((0 + h*(96 + h*16)) + k*((0 + h*(144 + h*96)) + k*(0 + h*(0 + h*144))))) + z*(((32 + h*-32) + k*((76 + h*(-104 + h*-16)) + k*((-8 + h*(-80 + h*(-80 + h*16))) + k*(156 + h*(-168 + h*(-96 + h*48)))))) + z*(((0 + h*96) + k*((0 + h*(352 + h*96)) + k*((0 + h*(288 + h*320)) + k*(0 + h*(288 + h*96))))) + z*(((0 + h*-104) + k*((-354 + h*(-192 + h*-56)) + k*((-868 + h*(-40 + h*(-208 + h*64))) + k*(-1018 + h*(80 + h*(8 + h*64)))))) + z*(((0 + h*208) + k*((0 + h*(-32 + h*336)) + k*((0 + h*(-1840 + h*864)) + k*(0 + h*(-2688 + h*592))))) + z*(((-192 + h*-160) + k*((-708 + h*(24 + h*-480)) + k*((776 + h*(176 + h*(-2304 + h*192))) + k*(2940 + h*(-168 + h*(-3168 + h*256)))))) + z*(((0 + h*128) + k*((0 + h*(-1152 + h*896)) + k*((0 + h*(128 + h*(1792 + h*-512))) + k*(0 + h*(7040 + h*(384 + h*-1536)))))) + z*(((-344 + h*-60) + k*((577 + h*(288 + h*-1596)) + k*((2550 + h*(-972 + h*(-2728 + h*448))) + k*(-2879 + h*(-1176 + h*(4964 + h*(320 + h*-256))))))) + z*(((0 + h*-224) + k*((0 + h*(-192 + h*1696)) + k*((0 + h*(6688 + h*(1472 + h*-1024))) + k*(0 + h*(-2432 + h*(-1376 + h*1024)))))) + z*(((-64 + h*192) + k*((1816 + h*(-464 + h*-2400)) + k*((-2256 + h*(-2720 + h*(1760 + h*608))) + k*(-1800 + h*(304 + h*(832 + h*-160)))))) + z*(((0 + h*-448) + k*((0 + h*(3136 + h*2112)) + k*((0 + h*(3008 + h*(-640 + h*-512))) + k*(0 + h*(-4672 + h*(-960 + h*512)))))) + z*(((448 + h*336) + k*((-92 + h*(-2112 + h*-1872)) + k*((-4632 + h*(-1584 + h*(3328 + h*448))) + k*(2548 + h*(1568 + h*(-1712 + h*-320)))))) + z*(((0 + h*-224) + k*((0 + h*(4160 + h*1696)) + k*((0 + h*(-4320 + h*-1856)) + k*(0 + h*(640 + h*416))))) + z*(((512 + h*192) + k*((-2728 + h*(-2832 + h*-896)) + k*((144 + h*(1248 + h*(1216 + h*192))) + k*(1304 + h*(496 + h*(-512 + h*-128)))))) + z*(((0 + h*128) + k*((0 + h*(1920 + h*896)) + k*((0 + h*(-3456 + h*-1280)) + k*(0 + h*(1408 + h*384))))) + z*(((88 + h*-60) + k*((-2399 + h*(-1936 + h*-444)) + k*((2702 + h*(2100 + h*(440 + h*64))) + k*(-535 + h*(-296 + h*(-60 + h*-64)))))) + z*(((0 + h*208) + k*((0 + h*(96 + h*336)) + k*((0 + h*(-688 + h*-544)) + k*(0 + h*(384 + h*208))))) + z*(((-224 + h*-160) + k*((-612 + h*(-712 + h*-272)) + k*((1368 + h*(1264 + h*(368 + h*16))) + k*(-532 + h*(-392 + h*(-96 + h*-16)))))) + z*(((0 + h*96) + k*((0 + h*(-160 + h*96)) + k*((0 + h*(32 + h*-192)) + k*(0 + h*(32 + h*96))))) + z*(((-192 + h*-104) + k*((158 + h*(-128 + h*-120)) + k*((188 + h*(472 + h*208)) + k*(-154 + h*(-240 + h*-88))))) + z*(((0 + h*16) + k*((0 + h*(-32 + h*16)) + k*((0 + h*(16 + h*-32)) + k*(0 + h*(0 + h*16))))) + z*(((-64 + h*-32) + k*((108 + h*(-8 + h*-32)) + k*((-24 + h*(112 + h*64)) + k*(-20 + h*(-72 + h*-32))))) + z*(0 + z*((-8 + h*-4) + k*((15 + h*(0 + h*-4)) + k*((-6 + h*(12 + h*8)) + k*(-1 + h*(-8 + h*-4)))))))))))))))))))))))))))))

def numerator (z k h : ℝ) : ℝ :=
  let D := 1+z^2
  let S := 1-z^2
  let J := 2*z
  let A := D^2+(2*S*D+S^2)*k
  let W := 1+k*h
  let B := J^2*A+J^3*k*h
  let E := (W*D^2+J^2*k)*A*D^4-S^4*W*A*D^2-B^2
  4*S^4*B^2*W*A*D^2-E^2

theorem numerator_identity (z k h : ℝ) :
    numerator z k h = 16*k*z^4*P z k h := by
  unfold numerator P
  ring

/-- Homogeneous evaluation of a row, with binomial factors in its entries. -/
def row (cs : List ℝ) (x y : ℝ) : ℝ :=
  match cs with
  | [] => 0
  | c :: tail => c*y^tail.length + x*row tail x y

def tensor (cs : List (List (List ℕ))) (z Z k K h H : ℝ) : ℝ :=
  row (cs.map (fun (plane : List (List ℕ)) => row (plane.map (fun (line : List ℕ) =>
    row (line.map (fun c : ℕ => (c : ℝ))) h H)) k K)) z Z

private theorem row_nonneg (cs : List ℝ) (x y : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hc : ∀ c ∈ cs, 0 ≤ c) :
    0 ≤ row cs x y := by
  induction cs with
  | nil => simp [row]
  | cons c cs ih =>
    simp only [row]
    exact add_nonneg (mul_nonneg (hc c (by simp)) (pow_nonneg hy _))
      (mul_nonneg hx (ih (fun c h => hc c (by simp [h]))))

theorem tensor_nonneg (cs : List (List (List ℕ))) (z Z k K h H : ℝ)
    (hz : 0 ≤ z) (hZ : 0 ≤ Z) (hk : 0 ≤ k) (hK : 0 ≤ K)
    (hh : 0 ≤ h) (hH : 0 ≤ H) : 0 ≤ tensor cs z Z k K h H := by
  unfold tensor
  apply row_nonneg _ _ _ hz hZ
  intro v hv
  obtain ⟨plane, _, rfl⟩ := List.mem_map.mp hv
  apply row_nonneg _ _ _ hk hK
  intro v hv
  obtain ⟨line, _, rfl⟩ := List.mem_map.mp hv
  apply row_nonneg _ _ _ hh hH
  intro c hc
  obtain ⟨n, _, rfl⟩ := List.mem_map.mp hc
  exact Nat.cast_nonneg n

def constraint (z k h : ℝ) : ℝ := (1-z^2)^2*(1+k*h)-z^2

theorem constraint_upper (z k h a b c : ℝ)
    (ha : 0 ≤ a) (haz : a ≤ z) (hz : z ≤ 1)
    (hk : 0 ≤ k) (hkb : k ≤ b) (hh : 0 ≤ h) (hhc : h ≤ c) :
    constraint z k h ≤ constraint a b c := by
  have hz0 : 0 ≤ z := ha.trans haz
  have hzz : a^2 ≤ z^2 := (sq_le_sq₀ ha hz0).mpr haz
  have hSz : 0 ≤ 1-z^2 := by nlinarith
  have hSa : 0 ≤ 1-a^2 := by linarith
  have hSS : (1-z^2)^2 ≤ (1-a^2)^2 :=
    (sq_le_sq₀ hSz hSa).mpr (by linarith)
  have hW : 1+k*h ≤ 1+b*c := by
    linarith only [mul_le_mul hkb hhc hh (hk.trans hkb)]
  have hm := mul_le_mul hSS hW
    (by positivity : 0 ≤ 1+k*h) (sq_nonneg (1-a^2))
  unfold constraint
  linarith only [hm, hzz]

end
end D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar.SixRowHeadPolynomial
