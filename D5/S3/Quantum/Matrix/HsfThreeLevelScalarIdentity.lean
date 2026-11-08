/- GID: D5/S3/Quantum/Matrix/HsfThreeLevelScalarIdentity
   generality: G
   mirror-B: D5/B/S3/Quantum/Matrix/HsfThreeLevelScalarIdentity
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: [D5/S3/Quantum/Matrix/HsfThreeLevelCoefficients]
   utility: kind=numeric-reduction; basis=consumer=D5/S3/Quantum/Matrix/HsfThreeLevelScalarBinding.closed_cubic_nonneg; premises=D5/S3/Quantum/Matrix/HsfThreeLevelScalarIdentity.p396_nonneg
   digest: Structured elementary-symmetric identities for the P396 scalar certificate. -/

module

public import D5.S3.Quantum.Matrix.HsfThreeLevelScalarCertificate

/-! UNCOMPILED source candidate. The P396 input is a fallible completed
   mathematical source, whose separate independent audit is not read here.
   Standard ring/positivity proof bodies below still require real compilation.
   No native computation, reflection framework, new axiom or heartbeat override.
   No original integral identity or full HSF theorem is claimed. -/

@[expose] public section
noncomputable section

namespace D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients

/- The raw degree-72 expansion is avoided. The raw identities below have
   degree at most 24; the remaining core identity uses three elementary
   variables. The final positive decomposition has 913 raw monomials and
   111 elementary monomials. Probe this module separately with the default
   heartbeat limit; its elaboration cost has not been measured. -/

private def qElementary (e f g : ℝ) : ℝ := e^2*f^2-f^3-e^3*g
private def discriminant (e f g : ℝ) : ℝ := e^2*f^2-4*f^3-4*e^3*g+18*e*f*g-27*g^2

private def uElementary (e f g : ℝ) : ℝ :=
  60*e^12*g^4
  - 23*e^11*f^2*g^3
  - 2*e^10*f^4*g^2
  - 433*e^10*f*g^4
  + e^9*f^6*g
  + 165*e^9*f^3*g^3
  + 216*e^9*g^5
  + 12*e^8*f^5*g^2
  + 1089*e^8*f^2*g^4
  - 9*e^7*f^7*g
  - 453*e^7*f^4*g^3
  - 432*e^7*f*g^5
  + e^6*f^9
  + 3*e^6*f^6*g^2
  - 1728*e^6*f^3*g^4
  + 12*e^5*f^8*g
  + 1098*e^5*f^5*g^3
  - 2*e^4*f^10
  - 453*e^4*f^7*g^2
  + 2052*e^4*f^4*g^4
  + 165*e^3*f^9*g
  - 1728*e^3*f^6*g^3
  - 23*e^2*f^11
  + 1089*e^2*f^8*g^2
  - 433*e*f^10*g
  - 432*e*f^7*g^3
  + 60*f^12
  + 216*f^9*g^2

private def tElementary (e f g : ℝ) : ℝ :=
  60*e^10*f*g^3
  - 23*e^9*f^3*g^2
  - 59*e^9*g^4
  - 2*e^8*f^5*g
  - 295*e^8*f^2*g^3
  + e^7*f^7
  + 131*e^7*f^4*g^2
  + 5034*e^7*f*g^4
  - 3*e^6*f^6*g
  - 2901*e^6*f^3*g^3
  + 8532*e^6*g^5
  - 2*e^5*f^8
  + 232*e^5*f^5*g^2
  - 35964*e^5*f^2*g^4
  + 131*e^4*f^7*g
  + 20652*e^4*f^4*g^3
  - 33696*e^4*f*g^5
  - 23*e^3*f^9
  - 2901*e^3*f^6*g^2
  + 76032*e^3*f^3*g^4
  - 295*e^2*f^8*g
  - 35964*e^2*f^5*g^3
  + 23328*e^2*f^2*g^5
  + 60*e*f^10
  + 5034*e*f^7*g^2
  - 33696*e*f^4*g^4
  - 59*f^9*g
  + 8532*f^6*g^3

private def quotientElementaryPart1 (e f g : ℝ) : ℝ :=
  0
  -3600*e^25*f*g^8
  + 9060*e^24*f^3*g^7
  - 2400*e^24*g^9
  - 7144*e^23*f^5*g^6
  + 592175*e^23*f^2*g^8
  + 1340*e^22*f^7*g^5
  + 67706*e^22*f^4*g^7
  - 1373531*e^22*f*g^9
  + 512*e^21*f^9*g^4
  + 11965*e^21*f^6*g^6
  - 6101369*e^21*f^3*g^8
  - 259704*e^21*g^10
  - 164*e^20*f^11*g^3
  - 166284*e^20*f^8*g^5
  - 1608802*e^20*f^5*g^7
  + 23237211*e^20*f^2*g^9
  - 8*e^19*f^13*g^2
  + 60253*e^19*f^10*g^4
  + 1716091*e^19*f^7*g^6
  + 21522961*e^19*f^4*g^8
  - 4027536*e^19*f*g^10
  + 4*e^18*f^15*g
  - 1526*e^18*f^12*g^3
  + 657360*e^18*f^9*g^5
  + 10064223*e^18*f^6*g^7
  - 132324480*e^18*f^3*g^9
  - 684288*e^18*g^11
  - 2381*e^17*f^14*g^2
  - 442059*e^17*f^11*g^4
  - 17552400*e^17*f^8*g^6
  - 14947830*e^17*f^5*g^8
  + 49071744*e^17*f^2*g^10
  + 360*e^16*f^16*g
  + 51930*e^16*f^13*g^3
  + 4637719*e^16*f^10*g^5
  - 24116001*e^16*f^7*g^7
  + 371744316*e^16*f^4*g^9

private def quotientElementaryPart2 (e f g : ℝ) : ℝ :=
  0
  + 4*e^15*f^18
  + 9329*e^15*f^15*g^2
  - 3623*e^15*f^12*g^4
  + 63544701*e^15*f^9*g^6
  - 126122400*e^15*f^6*g^8
  - 135302400*e^15*f^3*g^10
  - 2381*e^14*f^17*g
  - 250547*e^14*f^14*g^3
  - 35259989*e^14*f^11*g^5
  + 27845469*e^14*f^8*g^7
  - 645211008*e^14*f^5*g^9
  - 8*e^13*f^19
  + 51930*e^13*f^16*g^2
  + 8655412*e^13*f^13*g^4
  - 95263717*e^13*f^10*g^6
  + 557165952*e^13*f^7*g^8
  + 151165440*e^13*f^4*g^10
  - 1526*e^12*f^18*g
  - 3623*e^12*f^15*g^3
  + 88005350*e^12*f^12*g^5
  - 142759080*e^12*f^9*g^7
  + 800243712*e^12*f^6*g^9
  - 164*e^11*f^20
  - 442059*e^11*f^17*g^2
  - 35259989*e^11*f^14*g^4
  + 64969692*e^11*f^11*g^6
  - 1193377536*e^11*f^8*g^8
  - 60466176*e^11*f^5*g^10
  + 60253*e^10*f^19*g
  + 4637719*e^10*f^16*g^3
  - 95263717*e^10*f^13*g^5
  + 609691752*e^10*f^10*g^7
  - 695361024*e^10*f^7*g^9
  + 512*e^9*f^21
  + 657360*e^9*f^18*g^2
  + 63544701*e^9*f^15*g^4
  - 142759080*e^9*f^12*g^6

private def quotientElementaryPart3 (e f g : ℝ) : ℝ :=
  0
  + 1446460416*e^9*f^9*g^8
  - 166284*e^8*f^20*g
  - 17552400*e^8*f^17*g^3
  + 27845469*e^8*f^14*g^5
  - 1193377536*e^8*f^11*g^7
  + 287214336*e^8*f^8*g^9
  + 1340*e^7*f^22
  + 1716091*e^7*f^19*g^2
  - 24116001*e^7*f^16*g^4
  + 557165952*e^7*f^13*g^6
  - 695361024*e^7*f^10*g^8
  + 11965*e^6*f^21*g
  + 10064223*e^6*f^18*g^3
  - 126122400*e^6*f^15*g^5
  + 800243712*e^6*f^12*g^7
  - 7144*e^5*f^23
  - 1608802*e^5*f^20*g^2
  - 14947830*e^5*f^17*g^4
  - 645211008*e^5*f^14*g^6
  - 60466176*e^5*f^11*g^8
  + 67706*e^4*f^22*g
  + 21522961*e^4*f^19*g^3
  + 371744316*e^4*f^16*g^5
  + 151165440*e^4*f^13*g^7
  + 9060*e^3*f^24
  - 6101369*e^3*f^21*g^2
  - 132324480*e^3*f^18*g^4
  - 135302400*e^3*f^15*g^6
  + 592175*e^2*f^23*g
  + 23237211*e^2*f^20*g^3
  + 49071744*e^2*f^17*g^5
  - 3600*e*f^25
  - 1373531*e*f^22*g^2
  - 4027536*e*f^19*g^4
  - 2400*f^24*g
  - 259704*f^21*g^3
  - 684288*f^18*g^5

private def quotientElementary (e f g : ℝ) : ℝ :=
  quotientElementaryPart1 e f g + quotientElementaryPart2 e f g + quotientElementaryPart3 e f g

private def minusElementary (e f g : ℝ) : ℝ := -3*e^3*g + e^2*f^2 + 10*e*f*g - 3*f^3 - 8*g^2

private def plusElementary (e f g : ℝ) : ℝ := 5*e^3*g + e^2*f^2 + 18*e*f*g + 5*f^3 + 216*g^2


/- Staged normal forms keep the kernel algebra bounded: each product is
   normalized once, then the final 149-term identity is only additive. -/
private def q2Elementary (e f g : ℝ) : ℝ :=
  e^6*g^2
  -2*e^5*f^2*g
  +2*e^3*f^3*g
  +e^4*f^4
  -2*e^2*f^5
  +f^6

private def q6Elementary (e f g : ℝ) : ℝ :=
  e^18*g^6
  -6*e^17*f^2*g^5
  +6*e^15*f^3*g^5
  +15*e^16*f^4*g^4
  -30*e^14*f^5*g^4
  +15*e^12*f^6*g^4
  -20*e^15*f^6*g^3
  +60*e^13*f^7*g^3
  -60*e^11*f^8*g^3
  +20*e^9*f^9*g^3
  +15*e^14*f^8*g^2
  -60*e^12*f^9*g^2
  +90*e^10*f^10*g^2
  -60*e^8*f^11*g^2
  +15*e^6*f^12*g^2
  -6*e^13*f^10*g
  +30*e^11*f^11*g
  -60*e^9*f^12*g
  +60*e^7*f^13*g
  -30*e^5*f^14*g
  +6*e^3*f^15*g
  +e^12*f^12
  -6*e^10*f^13
  +15*e^8*f^14
  -20*e^6*f^15
  +15*e^4*f^16
  -6*e^2*f^17
  +f^18

private def f2Elementary (e f g : ℝ) : ℝ :=
  49*e^12*g^6
  -1008*e^10*f*g^6
  +6192*e^8*f^2*g^6
  -10368*e^6*f^3*g^6
  +5184*e^4*f^4*g^6
  -98*e^13*f*g^5
  +1484*e^11*f^2*g^5
  -6380*e^9*f^3*g^5
  +8784*e^7*f^4*g^5
  +5472*e^5*f^5*g^5
  -10368*e^3*f^6*g^5
  +49*e^14*f^2*g^4
  -504*e^12*f^3*g^4
  +1934*e^10*f^4*g^4
  -1260*e^8*f^5*g^4
  -8394*e^6*f^6*g^4
  +8784*e^4*f^7*g^4
  +6192*e^2*f^8*g^4
  +28*e^13*f^4*g^3
  -136*e^11*f^5*g^3
  -444*e^9*f^6*g^3
  +2768*e^7*f^7*g^3
  -1260*e^5*f^8*g^3
  -6380*e^3*f^9*g^3
  -1008*e*f^10*g^3
  -10*e^12*f^6*g^2
  +92*e^10*f^7*g^2
  -241*e^8*f^8*g^2
  -444*e^6*f^9*g^2
  +1934*e^4*f^10*g^2
  +1484*e^2*f^11*g^2
  +49*f^12*g^2
  -4*e^11*f^8*g
  +10*e^9*f^9*g
  +92*e^7*f^10*g
  -136*e^5*f^11*g
  -504*e^3*f^12*g
  -98*e*f^13*g
  +e^10*f^10
  -4*e^8*f^11
  -10*e^6*f^12
  +28*e^4*f^13
  +49*e^2*f^14

private def dmpElementary (e f g : ℝ) : ℝ :=
  46656*g^6
  +25488*e^3*g^5
  -85536*e*f*g^5
  +3157*e^6*g^4
  -20340*e^4*f*g^4
  +24084*e^2*f^2*g^4
  +25488*f^3*g^4
  +60*e^9*g^3
  -254*e^7*f*g^3
  -2366*e^5*f^2*g^3
  +14558*e^3*f^3*g^3
  -20340*e*f^4*g^3
  -23*e^8*f^2*g^2
  +100*e^6*f^3*g^2
  +357*e^4*f^4*g^2
  -2366*e^2*f^5*g^2
  +3157*f^6*g^2
  -2*e^7*f^4*g
  +100*e^3*f^6*g
  -254*e*f^7*g
  +e^6*f^6
  -2*e^4*f^7
  -23*e^2*f^8
  +60*f^9

private def uPartElementary (e f g : ℝ) : ℝ :=
  uElementary e f g * (4*q2Elementary e f g*tElementary e f g -
    729*g*f2Elementary e f g)

private def cPartElementary (e f g : ℝ) : ℝ :=
  396*q6Elementary e f g*g*dmpElementary e f g

private theorem Q_elementary (p q r : ℝ) :
    Q p q r = qElementary (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold Q H qElementary
  ring

private theorem discriminant_elementary (p q r : ℝ) :
    (p-q)^2*(q-r)^2*(r-p)^2 = discriminant (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold discriminant
  ring

private theorem minus_elementary (p q r : ℝ) :
    (p^2-p*q+q^2)*(q^2-q*r+r^2)*(r^2-r*p+p^2) =
      minusElementary (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold minusElementary
  ring

private theorem plus_elementary (p q r : ℝ) :
    (p^2+7*p*q+q^2)*(q^2+7*q*r+r^2)*(r^2+7*r*p+p^2) =
      plusElementary (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold plusElementary
  ring

private theorem u_elementary (p q r : ℝ) :
    edgeScaled p q r+edgeScaled q r p+edgeScaled r p q =
      uElementary (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold edgeScaled edgeNumerator H uElementary
  ring

private theorem t_elementary (p q r : ℝ) :
    edgeNumerator p q*edgeNumerator q r*(H r p)^4+
    edgeNumerator q r*edgeNumerator r p*(H p q)^4+
    edgeNumerator r p*edgeNumerator p q*(H q r)^4 =
      (p*q*r)*tElementary (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold edgeNumerator H tElementary
  ring

private theorem pair_scaled (p q r : ℝ) :
    edgeScaled p q r*edgeScaled q r p+edgeScaled q r p*edgeScaled r p q+
      edgeScaled r p q*edgeScaled p q r =
      (Q p q r)^4*(p*q*r)*tElementary (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  calc
    _ = (Q p q r)^4 * (edgeNumerator p q*edgeNumerator q r*(H r p)^4 +
      edgeNumerator q r*edgeNumerator r p*(H p q)^4 +
      edgeNumerator r p*edgeNumerator p q*(H q r)^4) := by
      unfold edgeScaled Q
      ring
    _ = (Q p q r)^4 * ((p*q*r)*tElementary
      (p+q+r) (p*q+q*r+r*p) (p*q*r)) := by rw [t_elementary]
    _ = _ := by ring

private theorem triple_scaled (p q r : ℝ) :
    edgeScaled p q r*edgeScaled q r p*edgeScaled r p q =
      (Q p q r)^8*(p*q*r)^2*
      discriminant (p+q+r) (p*q+q*r+r*p) (p*q*r)*
      minusElementary (p+q+r) (p*q+q*r+r*p) (p*q*r)*
      plusElementary (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  rw [← discriminant_elementary, ← minus_elementary, ← plus_elementary]
  unfold edgeScaled edgeNumerator Q
  ring

-- The expanded elementary identity is split into bounded normal-form products.
private theorem elementary_core (e f g : ℝ) :
    uElementary e f g*(4*(qElementary e f g)^2*tElementary e f g-729*g*(symmetricF e f g)^2)+
      396*(qElementary e f g)^6*g*discriminant e f g*minusElementary e f g*plusElementary e f g =
      discriminant e f g*quotientElementary e f g := by
  have hq2 : qElementary e f g ^ 2 = q2Elementary e f g := by
    unfold qElementary q2Elementary
    ring
  have hq6 : qElementary e f g ^ 6 = q6Elementary e f g := by
    unfold qElementary q6Elementary
    ring
  have hf2 : symmetricF e f g ^ 2 = f2Elementary e f g := by
    unfold symmetricF f2Elementary
    ring
  have hdmp : discriminant e f g * minusElementary e f g * plusElementary e f g =
      dmpElementary e f g := by
    unfold discriminant minusElementary plusElementary dmpElementary
    ring
  have hsum : uPartElementary e f g + cPartElementary e f g =
      discriminant e f g * quotientElementary e f g := by
    unfold uPartElementary cPartElementary q2Elementary q6Elementary f2Elementary
      dmpElementary uElementary tElementary discriminant quotientElementary quotientElementaryPart1 quotientElementaryPart2
      quotientElementaryPart3
    ring
  calc
    _ = uPartElementary e f g + cPartElementary e f g := by
      rw [hq2, hf2, hq6]
      unfold uPartElementary cPartElementary
      rw [← hdmp]
      ring
    _ = _ := hsum

private def sumPowers (n : ℕ) (p q r : ℝ) : ℝ := p^n + q^n + r^n

private theorem sumPowers_recurrence (n : ℕ) (p q r : ℝ) :
    sumPowers (n+3) p q r = (p+q+r)*sumPowers (n+2) p q r -
      (p*q+q*r+r*p)*sumPowers (n+1) p q r + p*q*r*sumPowers n p q r := by
  simp only [sumPowers, pow_add]
  ring

private def newton0row0 (e f : ℝ) : ℝ :=
  3

private def newton0 (e f g : ℝ) : ℝ :=
  newton0row0 e f

private theorem newton0_eval (p q r : ℝ) :
    sumPowers 0 p q r = newton0 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold sumPowers newton0 newton0row0
  ring

private def newton1row0 (e f : ℝ) : ℝ :=
  e

private def newton1 (e f g : ℝ) : ℝ :=
  newton1row0 e f

private theorem newton1_eval (p q r : ℝ) :
    sumPowers 1 p q r = newton1 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold sumPowers newton1 newton1row0
  ring

private def newton2row0 (e f : ℝ) : ℝ :=
  e^2 - 2*f

private def newton2 (e f g : ℝ) : ℝ :=
  newton2row0 e f

private theorem newton2_eval (p q r : ℝ) :
    sumPowers 2 p q r = newton2 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold sumPowers newton2 newton2row0
  ring

private def newton3row0 (e f : ℝ) : ℝ :=
  e^3 - 3*e*f

private def newton3row1 (e f : ℝ) : ℝ :=
  3

private def newton3 (e f g : ℝ) : ℝ :=
  newton3row0 e f +
  newton3row1 e f*g^1

private theorem newton3_rec (e f g : ℝ) :
    e*newton2 e f g - f*newton1 e f g + g*newton0 e f g = newton3 e f g := by
  unfold newton3 newton3row0 newton3row1 newton2 newton2row0 newton1 newton1row0 newton0 newton0row0
  ring

private theorem newton3_eval (p q r : ℝ) :
    sumPowers 3 p q r = newton3 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  have h := sumPowers_recurrence 0 p q r
  change sumPowers 3 p q r = (p+q+r)*sumPowers 2 p q r -
    (p*q+q*r+r*p)*sumPowers 1 p q r + p*q*r*sumPowers 0 p q r at h
  rw [newton2_eval, newton1_eval, newton0_eval] at h
  exact h.trans (newton3_rec _ _ _)

private def newton4row0 (e f : ℝ) : ℝ :=
  e^4 - 4*e^2*f + 2*f^2

private def newton4row1 (e f : ℝ) : ℝ :=
  4*e

private def newton4 (e f g : ℝ) : ℝ :=
  newton4row0 e f +
  newton4row1 e f*g^1

private theorem newton4_rec (e f g : ℝ) :
    e*newton3 e f g - f*newton2 e f g + g*newton1 e f g = newton4 e f g := by
  unfold newton4 newton4row0 newton4row1 newton3 newton3row0 newton3row1 newton2 newton2row0
    newton1 newton1row0
  ring

private theorem newton4_eval (p q r : ℝ) :
    sumPowers 4 p q r = newton4 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  have h := sumPowers_recurrence 1 p q r
  change sumPowers 4 p q r = (p+q+r)*sumPowers 3 p q r -
    (p*q+q*r+r*p)*sumPowers 2 p q r + p*q*r*sumPowers 1 p q r at h
  rw [newton3_eval, newton2_eval, newton1_eval] at h
  exact h.trans (newton4_rec _ _ _)

private def newton5row0 (e f : ℝ) : ℝ :=
  e^5 - 5*e^3*f + 5*e*f^2

private def newton5row1 (e f : ℝ) : ℝ :=
  5*e^2 - 5*f

private def newton5 (e f g : ℝ) : ℝ :=
  newton5row0 e f +
  newton5row1 e f*g^1

private theorem newton5_rec (e f g : ℝ) :
    e*newton4 e f g - f*newton3 e f g + g*newton2 e f g = newton5 e f g := by
  unfold newton5 newton5row0 newton5row1 newton4 newton4row0 newton4row1 newton3 newton3row0
    newton3row1 newton2 newton2row0
  ring

private theorem newton5_eval (p q r : ℝ) :
    sumPowers 5 p q r = newton5 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  have h := sumPowers_recurrence 2 p q r
  change sumPowers 5 p q r = (p+q+r)*sumPowers 4 p q r -
    (p*q+q*r+r*p)*sumPowers 3 p q r + p*q*r*sumPowers 2 p q r at h
  rw [newton4_eval, newton3_eval, newton2_eval] at h
  exact h.trans (newton5_rec _ _ _)

private def newton6row0 (e f : ℝ) : ℝ :=
  e^6 - 6*e^4*f + 9*e^2*f^2 - 2*f^3

private def newton6row1 (e f : ℝ) : ℝ :=
  6*e^3 - 12*e*f

private def newton6row2 (e f : ℝ) : ℝ :=
  3

private def newton6 (e f g : ℝ) : ℝ :=
  newton6row0 e f +
  newton6row1 e f*g^1 +
  newton6row2 e f*g^2

private theorem newton6_rec (e f g : ℝ) :
    e*newton5 e f g - f*newton4 e f g + g*newton3 e f g = newton6 e f g := by
  unfold newton6 newton6row0 newton6row1 newton6row2 newton5 newton5row0 newton5row1 newton4
    newton4row0 newton4row1 newton3 newton3row0 newton3row1
  ring

private theorem newton6_eval (p q r : ℝ) :
    sumPowers 6 p q r = newton6 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  have h := sumPowers_recurrence 3 p q r
  change sumPowers 6 p q r = (p+q+r)*sumPowers 5 p q r -
    (p*q+q*r+r*p)*sumPowers 4 p q r + p*q*r*sumPowers 3 p q r at h
  rw [newton5_eval, newton4_eval, newton3_eval] at h
  exact h.trans (newton6_rec _ _ _)

private def newton7row0 (e f : ℝ) : ℝ :=
  e^7 - 7*e^5*f + 14*e^3*f^2 - 7*e*f^3

private def newton7row1 (e f : ℝ) : ℝ :=
  7*e^4 - 21*e^2*f + 7*f^2

private def newton7row2 (e f : ℝ) : ℝ :=
  7*e

private def newton7 (e f g : ℝ) : ℝ :=
  newton7row0 e f +
  newton7row1 e f*g^1 +
  newton7row2 e f*g^2

private theorem newton7_rec (e f g : ℝ) :
    e*newton6 e f g - f*newton5 e f g + g*newton4 e f g = newton7 e f g := by
  unfold newton7 newton7row0 newton7row1 newton7row2 newton6 newton6row0 newton6row1 newton6row2
    newton5 newton5row0 newton5row1 newton4 newton4row0 newton4row1
  ring

private theorem newton7_eval (p q r : ℝ) :
    sumPowers 7 p q r = newton7 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  have h := sumPowers_recurrence 4 p q r
  change sumPowers 7 p q r = (p+q+r)*sumPowers 6 p q r -
    (p*q+q*r+r*p)*sumPowers 5 p q r + p*q*r*sumPowers 4 p q r at h
  rw [newton6_eval, newton5_eval, newton4_eval] at h
  exact h.trans (newton7_rec _ _ _)

private def newton8row0 (e f : ℝ) : ℝ :=
  e^8 - 8*e^6*f + 20*e^4*f^2 - 16*e^2*f^3 + 2*f^4

private def newton8row1 (e f : ℝ) : ℝ :=
  8*e^5 - 32*e^3*f + 24*e*f^2

private def newton8row2 (e f : ℝ) : ℝ :=
  12*e^2 - 8*f

private def newton8 (e f g : ℝ) : ℝ :=
  newton8row0 e f +
  newton8row1 e f*g^1 +
  newton8row2 e f*g^2

private theorem newton8_rec (e f g : ℝ) :
    e*newton7 e f g - f*newton6 e f g + g*newton5 e f g = newton8 e f g := by
  unfold newton8 newton8row0 newton8row1 newton8row2 newton7 newton7row0 newton7row1 newton7row2
    newton6 newton6row0 newton6row1 newton6row2 newton5 newton5row0 newton5row1
  ring

private theorem newton8_eval (p q r : ℝ) :
    sumPowers 8 p q r = newton8 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  have h := sumPowers_recurrence 5 p q r
  change sumPowers 8 p q r = (p+q+r)*sumPowers 7 p q r -
    (p*q+q*r+r*p)*sumPowers 6 p q r + p*q*r*sumPowers 5 p q r at h
  rw [newton7_eval, newton6_eval, newton5_eval] at h
  exact h.trans (newton8_rec _ _ _)

private def newton9row0 (e f : ℝ) : ℝ :=
  e^9 - 9*e^7*f + 27*e^5*f^2 - 30*e^3*f^3 + 9*e*f^4

private def newton9row1 (e f : ℝ) : ℝ :=
  9*e^6 - 45*e^4*f + 54*e^2*f^2 - 9*f^3

private def newton9row2 (e f : ℝ) : ℝ :=
  18*e^3 - 27*e*f

private def newton9row3 (e f : ℝ) : ℝ :=
  3

private def newton9 (e f g : ℝ) : ℝ :=
  newton9row0 e f +
  newton9row1 e f*g^1 +
  newton9row2 e f*g^2 +
  newton9row3 e f*g^3

private theorem newton9_rec (e f g : ℝ) :
    e*newton8 e f g - f*newton7 e f g + g*newton6 e f g = newton9 e f g := by
  unfold newton9 newton9row0 newton9row1 newton9row2 newton9row3 newton8 newton8row0 newton8row1
    newton8row2 newton7 newton7row0 newton7row1 newton7row2 newton6 newton6row0 newton6row1
    newton6row2
  ring

private theorem newton9_eval (p q r : ℝ) :
    sumPowers 9 p q r = newton9 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  have h := sumPowers_recurrence 6 p q r
  change sumPowers 9 p q r = (p+q+r)*sumPowers 8 p q r -
    (p*q+q*r+r*p)*sumPowers 7 p q r + p*q*r*sumPowers 6 p q r at h
  rw [newton8_eval, newton7_eval, newton6_eval] at h
  exact h.trans (newton9_rec _ _ _)

private def newton10row0 (e f : ℝ) : ℝ :=
  e^10 - 10*e^8*f + 35*e^6*f^2 - 50*e^4*f^3 + 25*e^2*f^4 - 2*f^5

private def newton10row1 (e f : ℝ) : ℝ :=
  10*e^7 - 60*e^5*f + 100*e^3*f^2 - 40*e*f^3

private def newton10row2 (e f : ℝ) : ℝ :=
  25*e^4 - 60*e^2*f + 15*f^2

private def newton10row3 (e f : ℝ) : ℝ :=
  10*e

private def newton10 (e f g : ℝ) : ℝ :=
  newton10row0 e f +
  newton10row1 e f*g^1 +
  newton10row2 e f*g^2 +
  newton10row3 e f*g^3

private theorem newton10_rec (e f g : ℝ) :
    e*newton9 e f g - f*newton8 e f g + g*newton7 e f g = newton10 e f g := by
  unfold newton10 newton10row0 newton10row1 newton10row2 newton10row3 newton9 newton9row0
    newton9row1 newton9row2 newton9row3 newton8 newton8row0 newton8row1 newton8row2 newton7
    newton7row0 newton7row1 newton7row2
  ring

private theorem newton10_eval (p q r : ℝ) :
    sumPowers 10 p q r = newton10 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  have h := sumPowers_recurrence 7 p q r
  change sumPowers 10 p q r = (p+q+r)*sumPowers 9 p q r -
    (p*q+q*r+r*p)*sumPowers 8 p q r + p*q*r*sumPowers 7 p q r at h
  rw [newton9_eval, newton8_eval, newton7_eval] at h
  exact h.trans (newton10_rec _ _ _)

private def newton11row0 (e f : ℝ) : ℝ :=
  e^11 - 11*e^9*f + 44*e^7*f^2 - 77*e^5*f^3 + 55*e^3*f^4 - 11*e*f^5

private def newton11row1 (e f : ℝ) : ℝ :=
  11*e^8 - 77*e^6*f + 165*e^4*f^2 - 110*e^2*f^3 + 11*f^4

private def newton11row2 (e f : ℝ) : ℝ :=
  33*e^5 - 110*e^3*f + 66*e*f^2

private def newton11row3 (e f : ℝ) : ℝ :=
  22*e^2 - 11*f

private def newton11 (e f g : ℝ) : ℝ :=
  newton11row0 e f +
  newton11row1 e f*g^1 +
  newton11row2 e f*g^2 +
  newton11row3 e f*g^3

private theorem newton11_rec (e f g : ℝ) :
    e*newton10 e f g - f*newton9 e f g + g*newton8 e f g = newton11 e f g := by
  unfold newton11 newton11row0 newton11row1 newton11row2 newton11row3 newton10 newton10row0
    newton10row1 newton10row2 newton10row3 newton9 newton9row0 newton9row1 newton9row2 newton9row3
    newton8 newton8row0 newton8row1 newton8row2
  ring

private theorem newton11_eval (p q r : ℝ) :
    sumPowers 11 p q r = newton11 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  have h := sumPowers_recurrence 8 p q r
  change sumPowers 11 p q r = (p+q+r)*sumPowers 10 p q r -
    (p*q+q*r+r*p)*sumPowers 9 p q r + p*q*r*sumPowers 8 p q r at h
  rw [newton10_eval, newton9_eval, newton8_eval] at h
  exact h.trans (newton11_rec _ _ _)

private def newton12row0 (e f : ℝ) : ℝ :=
  e^12 - 12*e^10*f + 54*e^8*f^2 - 112*e^6*f^3 + 105*e^4*f^4 - 36*e^2*f^5 + 2*f^6

private def newton12row1 (e f : ℝ) : ℝ :=
  12*e^9 - 96*e^7*f + 252*e^5*f^2 - 240*e^3*f^3 + 60*e*f^4

private def newton12row2 (e f : ℝ) : ℝ :=
  42*e^6 - 180*e^4*f + 180*e^2*f^2 - 24*f^3

private def newton12row3 (e f : ℝ) : ℝ :=
  40*e^3 - 48*e*f

private def newton12row4 (e f : ℝ) : ℝ :=
  3

private def newton12 (e f g : ℝ) : ℝ :=
  newton12row0 e f +
  newton12row1 e f*g^1 +
  newton12row2 e f*g^2 +
  newton12row3 e f*g^3 +
  newton12row4 e f*g^4

private theorem newton12_rec (e f g : ℝ) :
    e*newton11 e f g - f*newton10 e f g + g*newton9 e f g = newton12 e f g := by
  unfold newton12 newton12row0 newton12row1 newton12row2 newton12row3 newton12row4 newton11
    newton11row0 newton11row1 newton11row2 newton11row3 newton10 newton10row0 newton10row1
    newton10row2 newton10row3 newton9 newton9row0 newton9row1 newton9row2 newton9row3
  ring

private theorem newton12_eval (p q r : ℝ) :
    sumPowers 12 p q r = newton12 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  have h := sumPowers_recurrence 9 p q r
  change sumPowers 12 p q r = (p+q+r)*sumPowers 11 p q r -
    (p*q+q*r+r*p)*sumPowers 10 p q r + p*q*r*sumPowers 9 p q r at h
  rw [newton11_eval, newton10_eval, newton9_eval] at h
  exact h.trans (newton12_rec _ _ _)

private def newton13row0 (e f : ℝ) : ℝ :=
  e^13 - 13*e^11*f + 65*e^9*f^2 - 156*e^7*f^3 + 182*e^5*f^4 - 91*e^3*f^5 + 13*e*f^6

private def newton13row1 (e f : ℝ) : ℝ :=
  13*e^10 - 117*e^8*f + 364*e^6*f^2 - 455*e^4*f^3 + 195*e^2*f^4 - 13*f^5

private def newton13row2 (e f : ℝ) : ℝ :=
  52*e^7 - 273*e^5*f + 390*e^3*f^2 - 130*e*f^3

private def newton13row3 (e f : ℝ) : ℝ :=
  65*e^4 - 130*e^2*f + 26*f^2

private def newton13row4 (e f : ℝ) : ℝ :=
  13*e

private def newton13 (e f g : ℝ) : ℝ :=
  newton13row0 e f +
  newton13row1 e f*g^1 +
  newton13row2 e f*g^2 +
  newton13row3 e f*g^3 +
  newton13row4 e f*g^4

private theorem newton13_rec (e f g : ℝ) :
    e*newton12 e f g - f*newton11 e f g + g*newton10 e f g = newton13 e f g := by
  unfold newton13 newton13row0 newton13row1 newton13row2 newton13row3 newton13row4 newton12
    newton12row0 newton12row1 newton12row2 newton12row3 newton12row4 newton11 newton11row0
    newton11row1 newton11row2 newton11row3 newton10 newton10row0 newton10row1 newton10row2
    newton10row3
  ring

private theorem newton13_eval (p q r : ℝ) :
    sumPowers 13 p q r = newton13 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  have h := sumPowers_recurrence 10 p q r
  change sumPowers 13 p q r = (p+q+r)*sumPowers 12 p q r -
    (p*q+q*r+r*p)*sumPowers 11 p q r + p*q*r*sumPowers 10 p q r at h
  rw [newton12_eval, newton11_eval, newton10_eval] at h
  exact h.trans (newton13_rec _ _ _)

private def newton14row0 (e f : ℝ) : ℝ :=
  e^14 - 14*e^12*f + 77*e^10*f^2 - 210*e^8*f^3 + 294*e^6*f^4 - 196*e^4*f^5 + 49*e^2*f^6 - 2*f^7

private def newton14row1 (e f : ℝ) : ℝ :=
  14*e^11 - 140*e^9*f + 504*e^7*f^2 - 784*e^5*f^3 + 490*e^3*f^4 - 84*e*f^5

private def newton14row2 (e f : ℝ) : ℝ :=
  63*e^8 - 392*e^6*f + 735*e^4*f^2 - 420*e^2*f^3 + 35*f^4

private def newton14row3 (e f : ℝ) : ℝ :=
  98*e^5 - 280*e^3*f + 140*e*f^2

private def newton14row4 (e f : ℝ) : ℝ :=
  35*e^2 - 14*f

private def newton14 (e f g : ℝ) : ℝ :=
  newton14row0 e f +
  newton14row1 e f*g^1 +
  newton14row2 e f*g^2 +
  newton14row3 e f*g^3 +
  newton14row4 e f*g^4

private theorem newton14_rec (e f g : ℝ) :
    e*newton13 e f g - f*newton12 e f g + g*newton11 e f g = newton14 e f g := by
  unfold newton14 newton14row0 newton14row1 newton14row2 newton14row3 newton14row4 newton13
    newton13row0 newton13row1 newton13row2 newton13row3 newton13row4 newton12 newton12row0
    newton12row1 newton12row2 newton12row3 newton12row4 newton11 newton11row0 newton11row1
    newton11row2 newton11row3
  ring

private theorem newton14_eval (p q r : ℝ) :
    sumPowers 14 p q r = newton14 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  have h := sumPowers_recurrence 11 p q r
  change sumPowers 14 p q r = (p+q+r)*sumPowers 13 p q r -
    (p*q+q*r+r*p)*sumPowers 12 p q r + p*q*r*sumPowers 11 p q r at h
  rw [newton13_eval, newton12_eval, newton11_eval] at h
  exact h.trans (newton14_rec _ _ _)

private def newton15row0 (e f : ℝ) : ℝ :=
  e^15 - 15*e^13*f + 90*e^11*f^2 - 275*e^9*f^3 + 450*e^7*f^4 - 378*e^5*f^5 + 140*e^3*f^6 - 15*e*f^7

private def newton15row1 (e f : ℝ) : ℝ :=
  15*e^12 - 165*e^10*f + 675*e^8*f^2 - 1260*e^6*f^3 + 1050*e^4*f^4 - 315*e^2*f^5 + 15*f^6

private def newton15row2 (e f : ℝ) : ℝ :=
  75*e^9 - 540*e^7*f + 1260*e^5*f^2 - 1050*e^3*f^3 + 225*e*f^4

private def newton15row3 (e f : ℝ) : ℝ :=
  140*e^6 - 525*e^4*f + 450*e^2*f^2 - 50*f^3

private def newton15row4 (e f : ℝ) : ℝ :=
  75*e^3 - 75*e*f

private def newton15row5 (e f : ℝ) : ℝ :=
  3

private def newton15 (e f g : ℝ) : ℝ :=
  newton15row0 e f +
  newton15row1 e f*g^1 +
  newton15row2 e f*g^2 +
  newton15row3 e f*g^3 +
  newton15row4 e f*g^4 +
  newton15row5 e f*g^5

private theorem newton15_rec (e f g : ℝ) :
    e*newton14 e f g - f*newton13 e f g + g*newton12 e f g = newton15 e f g := by
  unfold newton15 newton15row0 newton15row1 newton15row2 newton15row3 newton15row4 newton15row5
    newton14 newton14row0 newton14row1 newton14row2 newton14row3 newton14row4 newton13
    newton13row0 newton13row1 newton13row2 newton13row3 newton13row4 newton12 newton12row0
    newton12row1 newton12row2 newton12row3 newton12row4
  ring

private theorem newton15_eval (p q r : ℝ) :
    sumPowers 15 p q r = newton15 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  have h := sumPowers_recurrence 12 p q r
  change sumPowers 15 p q r = (p+q+r)*sumPowers 14 p q r -
    (p*q+q*r+r*p)*sumPowers 13 p q r + p*q*r*sumPowers 12 p q r at h
  rw [newton14_eval, newton13_eval, newton12_eval] at h
  exact h.trans (newton15_rec _ _ _)

private def newton16row0 (e f : ℝ) : ℝ :=
  e^16 - 16*e^14*f + 104*e^12*f^2 - 352*e^10*f^3 + 660*e^8*f^4 - 672*e^6*f^5 + 336*e^4*f^6 -
      64*e^2*f^7 + 2*f^8

private def newton16row1 (e f : ℝ) : ℝ :=
  16*e^13 - 192*e^11*f + 880*e^9*f^2 - 1920*e^7*f^3 + 2016*e^5*f^4 - 896*e^3*f^5 + 112*e*f^6

private def newton16row2 (e f : ℝ) : ℝ :=
  88*e^10 - 720*e^8*f + 2016*e^6*f^2 - 2240*e^4*f^3 + 840*e^2*f^4 - 48*f^5

private def newton16row3 (e f : ℝ) : ℝ :=
  192*e^7 - 896*e^5*f + 1120*e^3*f^2 - 320*e*f^3

private def newton16row4 (e f : ℝ) : ℝ :=
  140*e^4 - 240*e^2*f + 40*f^2

private def newton16row5 (e f : ℝ) : ℝ :=
  16*e

private def newton16 (e f g : ℝ) : ℝ :=
  newton16row0 e f +
  newton16row1 e f*g^1 +
  newton16row2 e f*g^2 +
  newton16row3 e f*g^3 +
  newton16row4 e f*g^4 +
  newton16row5 e f*g^5

private theorem newton16_rec (e f g : ℝ) :
    e*newton15 e f g - f*newton14 e f g + g*newton13 e f g = newton16 e f g := by
  unfold newton16 newton16row0 newton16row1 newton16row2 newton16row3 newton16row4 newton16row5
    newton15 newton15row0 newton15row1 newton15row2 newton15row3 newton15row4 newton15row5
    newton14 newton14row0 newton14row1 newton14row2 newton14row3 newton14row4 newton13
    newton13row0 newton13row1 newton13row2 newton13row3 newton13row4
  ring

private theorem newton16_eval (p q r : ℝ) :
    sumPowers 16 p q r = newton16 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  have h := sumPowers_recurrence 13 p q r
  change sumPowers 16 p q r = (p+q+r)*sumPowers 15 p q r -
    (p*q+q*r+r*p)*sumPowers 14 p q r + p*q*r*sumPowers 13 p q r at h
  rw [newton15_eval, newton14_eval, newton13_eval] at h
  exact h.trans (newton16_rec _ _ _)

private def newton17row0 (e f : ℝ) : ℝ :=
  e^17 - 17*e^15*f + 119*e^13*f^2 - 442*e^11*f^3 + 935*e^9*f^4 - 1122*e^7*f^5 + 714*e^5*f^6 -
      204*e^3*f^7 + 17*e*f^8

private def newton17row1 (e f : ℝ) : ℝ :=
  17*e^14 - 221*e^12*f + 1122*e^10*f^2 - 2805*e^8*f^3 + 3570*e^6*f^4 - 2142*e^4*f^5 + 476*e^2*f^6
      - 17*f^7

private def newton17row2 (e f : ℝ) : ℝ :=
  102*e^11 - 935*e^9*f + 3060*e^7*f^2 - 4284*e^5*f^3 + 2380*e^3*f^4 - 357*e*f^5

private def newton17row3 (e f : ℝ) : ℝ :=
  255*e^8 - 1428*e^6*f + 2380*e^4*f^2 - 1190*e^2*f^3 + 85*f^4

private def newton17row4 (e f : ℝ) : ℝ :=
  238*e^5 - 595*e^3*f + 255*e*f^2

private def newton17row5 (e f : ℝ) : ℝ :=
  51*e^2 - 17*f

private def newton17 (e f g : ℝ) : ℝ :=
  newton17row0 e f +
  newton17row1 e f*g^1 +
  newton17row2 e f*g^2 +
  newton17row3 e f*g^3 +
  newton17row4 e f*g^4 +
  newton17row5 e f*g^5

private theorem newton17_rec (e f g : ℝ) :
    e*newton16 e f g - f*newton15 e f g + g*newton14 e f g = newton17 e f g := by
  unfold newton17 newton17row0 newton17row1 newton17row2 newton17row3 newton17row4 newton17row5
    newton16 newton16row0 newton16row1 newton16row2 newton16row3 newton16row4 newton16row5
    newton15 newton15row0 newton15row1 newton15row2 newton15row3 newton15row4 newton15row5
    newton14 newton14row0 newton14row1 newton14row2 newton14row3 newton14row4
  ring

private theorem newton17_eval (p q r : ℝ) :
    sumPowers 17 p q r = newton17 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  have h := sumPowers_recurrence 14 p q r
  change sumPowers 17 p q r = (p+q+r)*sumPowers 16 p q r -
    (p*q+q*r+r*p)*sumPowers 15 p q r + p*q*r*sumPowers 14 p q r at h
  rw [newton16_eval, newton15_eval, newton14_eval] at h
  exact h.trans (newton17_rec _ _ _)

private def newton18row0 (e f : ℝ) : ℝ :=
  e^18 - 18*e^16*f + 135*e^14*f^2 - 546*e^12*f^3 + 1287*e^10*f^4 - 1782*e^8*f^5 + 1386*e^6*f^6 -
      540*e^4*f^7 + 81*e^2*f^8 - 2*f^9

private def newton18row1 (e f : ℝ) : ℝ :=
  18*e^15 - 252*e^13*f + 1404*e^11*f^2 - 3960*e^9*f^3 + 5940*e^7*f^4 - 4536*e^5*f^5 + 1512*e^3*f^6
      - 144*e*f^7

private def newton18row2 (e f : ℝ) : ℝ :=
  117*e^12 - 1188*e^10*f + 4455*e^8*f^2 - 7560*e^6*f^3 + 5670*e^4*f^4 - 1512*e^2*f^5 + 63*f^6

private def newton18row3 (e f : ℝ) : ℝ :=
  330*e^9 - 2160*e^7*f + 4536*e^5*f^2 - 3360*e^3*f^3 + 630*e*f^4

private def newton18row4 (e f : ℝ) : ℝ :=
  378*e^6 - 1260*e^4*f + 945*e^2*f^2 - 90*f^3

private def newton18row5 (e f : ℝ) : ℝ :=
  126*e^3 - 108*e*f

private def newton18row6 (e f : ℝ) : ℝ :=
  3

private def newton18 (e f g : ℝ) : ℝ :=
  newton18row0 e f +
  newton18row1 e f*g^1 +
  newton18row2 e f*g^2 +
  newton18row3 e f*g^3 +
  newton18row4 e f*g^4 +
  newton18row5 e f*g^5 +
  newton18row6 e f*g^6

private theorem newton18_rec (e f g : ℝ) :
    e*newton17 e f g - f*newton16 e f g + g*newton15 e f g = newton18 e f g := by
  unfold newton18 newton18row0 newton18row1 newton18row2 newton18row3 newton18row4 newton18row5
    newton18row6 newton17 newton17row0 newton17row1 newton17row2 newton17row3 newton17row4
    newton17row5 newton16 newton16row0 newton16row1 newton16row2 newton16row3 newton16row4
    newton16row5 newton15 newton15row0 newton15row1 newton15row2 newton15row3 newton15row4
    newton15row5
  ring

private theorem newton18_eval (p q r : ℝ) :
    sumPowers 18 p q r = newton18 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  have h := sumPowers_recurrence 15 p q r
  change sumPowers 18 p q r = (p+q+r)*sumPowers 17 p q r -
    (p*q+q*r+r*p)*sumPowers 16 p q r + p*q*r*sumPowers 15 p q r at h
  rw [newton17_eval, newton16_eval, newton15_eval] at h
  exact h.trans (newton18_rec _ _ _)

private def newton19row0 (e f : ℝ) : ℝ :=
  e^19 - 19*e^17*f + 152*e^15*f^2 - 665*e^13*f^3 + 1729*e^11*f^4 - 2717*e^9*f^5 + 2508*e^7*f^6 -
      1254*e^5*f^7 + 285*e^3*f^8 - 19*e*f^9

private def newton19row1 (e f : ℝ) : ℝ :=
  19*e^16 - 285*e^14*f + 1729*e^12*f^2 - 5434*e^10*f^3 + 9405*e^8*f^4 - 8778*e^6*f^5 +
      3990*e^4*f^6 - 684*e^2*f^7 + 19*f^8

private def newton19row2 (e f : ℝ) : ℝ :=
  133*e^13 - 1482*e^11*f + 6270*e^9*f^2 - 12540*e^7*f^3 + 11970*e^5*f^4 - 4788*e^3*f^5 + 532*e*f^6

private def newton19row3 (e f : ℝ) : ℝ :=
  418*e^10 - 3135*e^8*f + 7980*e^6*f^2 - 7980*e^4*f^3 + 2660*e^2*f^4 - 133*f^5

private def newton19row4 (e f : ℝ) : ℝ :=
  570*e^7 - 2394*e^5*f + 2660*e^3*f^2 - 665*e*f^3

private def newton19row5 (e f : ℝ) : ℝ :=
  266*e^4 - 399*e^2*f + 57*f^2

private def newton19row6 (e f : ℝ) : ℝ :=
  19*e

private def newton19 (e f g : ℝ) : ℝ :=
  newton19row0 e f +
  newton19row1 e f*g^1 +
  newton19row2 e f*g^2 +
  newton19row3 e f*g^3 +
  newton19row4 e f*g^4 +
  newton19row5 e f*g^5 +
  newton19row6 e f*g^6

private theorem newton19_rec (e f g : ℝ) :
    e*newton18 e f g - f*newton17 e f g + g*newton16 e f g = newton19 e f g := by
  unfold newton19 newton19row0 newton19row1 newton19row2 newton19row3 newton19row4 newton19row5
    newton19row6 newton18 newton18row0 newton18row1 newton18row2 newton18row3 newton18row4
    newton18row5 newton18row6 newton17 newton17row0 newton17row1 newton17row2 newton17row3
    newton17row4 newton17row5 newton16 newton16row0 newton16row1 newton16row2 newton16row3
    newton16row4 newton16row5
  ring

private theorem newton19_eval (p q r : ℝ) :
    sumPowers 19 p q r = newton19 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  have h := sumPowers_recurrence 16 p q r
  change sumPowers 19 p q r = (p+q+r)*sumPowers 18 p q r -
    (p*q+q*r+r*p)*sumPowers 17 p q r + p*q*r*sumPowers 16 p q r at h
  rw [newton18_eval, newton17_eval, newton16_eval] at h
  exact h.trans (newton19_rec _ _ _)

private def newton20row0 (e f : ℝ) : ℝ :=
  e^20 - 20*e^18*f + 170*e^16*f^2 - 800*e^14*f^3 + 2275*e^12*f^4 - 4004*e^10*f^5 + 4290*e^8*f^6 -
      2640*e^6*f^7 + 825*e^4*f^8 - 100*e^2*f^9 + 2*f^10

private def newton20row1 (e f : ℝ) : ℝ :=
  20*e^17 - 320*e^15*f + 2100*e^13*f^2 - 7280*e^11*f^3 + 14300*e^9*f^4 - 15840*e^7*f^5 +
      9240*e^5*f^6 - 2400*e^3*f^7 + 180*e*f^8

private def newton20row2 (e f : ℝ) : ℝ :=
  150*e^14 - 1820*e^12*f + 8580*e^10*f^2 - 19800*e^8*f^3 + 23100*e^6*f^4 - 12600*e^4*f^5 +
      2520*e^2*f^6 - 80*f^7

private def newton20row3 (e f : ℝ) : ℝ :=
  520*e^11 - 4400*e^9*f + 13200*e^7*f^2 - 16800*e^5*f^3 + 8400*e^3*f^4 - 1120*e*f^5

private def newton20row4 (e f : ℝ) : ℝ :=
  825*e^8 - 4200*e^6*f + 6300*e^4*f^2 - 2800*e^2*f^3 + 175*f^4

private def newton20row5 (e f : ℝ) : ℝ :=
  504*e^5 - 1120*e^3*f + 420*e*f^2

private def newton20row6 (e f : ℝ) : ℝ :=
  70*e^2 - 20*f

private def newton20 (e f g : ℝ) : ℝ :=
  newton20row0 e f +
  newton20row1 e f*g^1 +
  newton20row2 e f*g^2 +
  newton20row3 e f*g^3 +
  newton20row4 e f*g^4 +
  newton20row5 e f*g^5 +
  newton20row6 e f*g^6

private theorem newton20_rec (e f g : ℝ) :
    e*newton19 e f g - f*newton18 e f g + g*newton17 e f g = newton20 e f g := by
  unfold newton20 newton20row0 newton20row1 newton20row2 newton20row3 newton20row4 newton20row5
    newton20row6 newton19 newton19row0 newton19row1 newton19row2 newton19row3 newton19row4
    newton19row5 newton19row6 newton18 newton18row0 newton18row1 newton18row2 newton18row3
    newton18row4 newton18row5 newton18row6 newton17 newton17row0 newton17row1 newton17row2
    newton17row3 newton17row4 newton17row5
  ring

private theorem newton20_eval (p q r : ℝ) :
    sumPowers 20 p q r = newton20 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  have h := sumPowers_recurrence 17 p q r
  change sumPowers 20 p q r = (p+q+r)*sumPowers 19 p q r -
    (p*q+q*r+r*p)*sumPowers 18 p q r + p*q*r*sumPowers 17 p q r at h
  rw [newton19_eval, newton18_eval, newton17_eval] at h
  exact h.trans (newton20_rec _ _ _)

private def newton21row0 (e f : ℝ) : ℝ :=
  e^21 - 21*e^19*f + 189*e^17*f^2 - 952*e^15*f^3 + 2940*e^13*f^4 - 5733*e^11*f^5 + 7007*e^9*f^6 -
      5148*e^7*f^7 + 2079*e^5*f^8 - 385*e^3*f^9 + 21*e*f^10

private def newton21row1 (e f : ℝ) : ℝ :=
  21*e^18 - 357*e^16*f + 2520*e^14*f^2 - 9555*e^12*f^3 + 21021*e^10*f^4 - 27027*e^8*f^5 +
      19404*e^6*f^6 - 6930*e^4*f^7 + 945*e^2*f^8 - 21*f^9

private def newton21row2 (e f : ℝ) : ℝ :=
  168*e^15 - 2205*e^13*f + 11466*e^11*f^2 - 30030*e^9*f^3 + 41580*e^7*f^4 - 29106*e^5*f^5 +
      8820*e^3*f^6 - 756*e*f^7

private def newton21row3 (e f : ℝ) : ℝ :=
  637*e^12 - 6006*e^10*f + 20790*e^8*f^2 - 32340*e^6*f^3 + 22050*e^4*f^4 - 5292*e^2*f^5 + 196*f^6

private def newton21row4 (e f : ℝ) : ℝ :=
  1155*e^9 - 6930*e^7*f + 13230*e^5*f^2 - 8820*e^3*f^3 + 1470*e*f^4

private def newton21row5 (e f : ℝ) : ℝ :=
  882*e^6 - 2646*e^4*f + 1764*e^2*f^2 - 147*f^3

private def newton21row6 (e f : ℝ) : ℝ :=
  196*e^3 - 147*e*f

private def newton21row7 (e f : ℝ) : ℝ :=
  3

private def newton21 (e f g : ℝ) : ℝ :=
  newton21row0 e f +
  newton21row1 e f*g^1 +
  newton21row2 e f*g^2 +
  newton21row3 e f*g^3 +
  newton21row4 e f*g^4 +
  newton21row5 e f*g^5 +
  newton21row6 e f*g^6 +
  newton21row7 e f*g^7

private theorem newton21_rec (e f g : ℝ) :
    e*newton20 e f g - f*newton19 e f g + g*newton18 e f g = newton21 e f g := by
  unfold newton21 newton21row0 newton21row1 newton21row2 newton21row3 newton21row4 newton21row5
    newton21row6 newton21row7 newton20 newton20row0 newton20row1 newton20row2 newton20row3
    newton20row4 newton20row5 newton20row6 newton19 newton19row0 newton19row1 newton19row2
    newton19row3 newton19row4 newton19row5 newton19row6 newton18 newton18row0 newton18row1
    newton18row2 newton18row3 newton18row4 newton18row5 newton18row6
  ring

private theorem newton21_eval (p q r : ℝ) :
    sumPowers 21 p q r = newton21 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  have h := sumPowers_recurrence 18 p q r
  change sumPowers 21 p q r = (p+q+r)*sumPowers 20 p q r -
    (p*q+q*r+r*p)*sumPowers 19 p q r + p*q*r*sumPowers 18 p q r at h
  rw [newton20_eval, newton19_eval, newton18_eval] at h
  exact h.trans (newton21_rec _ _ _)

private def newton22row0 (e f : ℝ) : ℝ :=
  e^22 - 22*e^20*f + 209*e^18*f^2 - 1122*e^16*f^3 + 3740*e^14*f^4 - 8008*e^12*f^5 + 11011*e^10*f^6
      - 9438*e^8*f^7 + 4719*e^6*f^8 - 1210*e^4*f^9 + 121*e^2*f^10 - 2*f^11

private def newton22row1 (e f : ℝ) : ℝ :=
  22*e^19 - 396*e^17*f + 2992*e^15*f^2 - 12320*e^13*f^3 + 30030*e^11*f^4 - 44044*e^9*f^5 +
      37752*e^7*f^6 - 17424*e^5*f^7 + 3630*e^3*f^8 - 220*e*f^9

private def newton22row2 (e f : ℝ) : ℝ :=
  187*e^16 - 2640*e^14*f + 15015*e^12*f^2 - 44044*e^10*f^3 + 70785*e^8*f^4 - 60984*e^6*f^5 +
      25410*e^4*f^6 - 3960*e^2*f^7 + 99*f^8

private def newton22row3 (e f : ℝ) : ℝ :=
  770*e^13 - 8008*e^11*f + 31460*e^9*f^2 - 58080*e^7*f^3 + 50820*e^5*f^4 - 18480*e^3*f^5 +
      1848*e*f^6

private def newton22row4 (e f : ℝ) : ℝ :=
  1573*e^10 - 10890*e^8*f + 25410*e^6*f^2 - 23100*e^4*f^3 + 6930*e^2*f^4 - 308*f^5

private def newton22row5 (e f : ℝ) : ℝ :=
  1452*e^7 - 5544*e^5*f + 5544*e^3*f^2 - 1232*e*f^3

private def newton22row6 (e f : ℝ) : ℝ :=
  462*e^4 - 616*e^2*f + 77*f^2

private def newton22row7 (e f : ℝ) : ℝ :=
  22*e

private def newton22 (e f g : ℝ) : ℝ :=
  newton22row0 e f +
  newton22row1 e f*g^1 +
  newton22row2 e f*g^2 +
  newton22row3 e f*g^3 +
  newton22row4 e f*g^4 +
  newton22row5 e f*g^5 +
  newton22row6 e f*g^6 +
  newton22row7 e f*g^7

private theorem newton22_rec (e f g : ℝ) :
    e*newton21 e f g - f*newton20 e f g + g*newton19 e f g = newton22 e f g := by
  unfold newton22 newton22row0 newton22row1 newton22row2 newton22row3 newton22row4 newton22row5
    newton22row6 newton22row7 newton21 newton21row0 newton21row1 newton21row2 newton21row3
    newton21row4 newton21row5 newton21row6 newton21row7 newton20 newton20row0 newton20row1
    newton20row2 newton20row3 newton20row4 newton20row5 newton20row6 newton19 newton19row0
    newton19row1 newton19row2 newton19row3 newton19row4 newton19row5 newton19row6
  ring

private theorem newton22_eval (p q r : ℝ) :
    sumPowers 22 p q r = newton22 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  have h := sumPowers_recurrence 19 p q r
  change sumPowers 22 p q r = (p+q+r)*sumPowers 21 p q r -
    (p*q+q*r+r*p)*sumPowers 20 p q r + p*q*r*sumPowers 19 p q r at h
  rw [newton21_eval, newton20_eval, newton19_eval] at h
  exact h.trans (newton22_rec _ _ _)

private def newton23row0 (e f : ℝ) : ℝ :=
  e^23 - 23*e^21*f + 230*e^19*f^2 - 1311*e^17*f^3 + 4692*e^15*f^4 - 10948*e^13*f^5 +
      16744*e^11*f^6 - 16445*e^9*f^7 + 9867*e^7*f^8 - 3289*e^5*f^9 + 506*e^3*f^10 - 23*e*f^11

private def newton23row1 (e f : ℝ) : ℝ :=
  23*e^20 - 437*e^18*f + 3519*e^16*f^2 - 15640*e^14*f^3 + 41860*e^12*f^4 - 69069*e^10*f^5 +
      69069*e^8*f^6 - 39468*e^6*f^7 + 11385*e^4*f^8 - 1265*e^2*f^9 + 23*f^10

private def newton23row2 (e f : ℝ) : ℝ :=
  207*e^17 - 3128*e^15*f + 19320*e^13*f^2 - 62790*e^11*f^3 + 115115*e^9*f^4 - 118404*e^7*f^5 +
      63756*e^5*f^6 - 15180*e^3*f^7 + 1035*e*f^8

private def newton23row3 (e f : ℝ) : ℝ :=
  920*e^14 - 10465*e^12*f + 46046*e^10*f^2 - 98670*e^8*f^3 + 106260*e^6*f^4 - 53130*e^4*f^5 +
      9660*e^2*f^6 - 276*f^7

private def newton23row4 (e f : ℝ) : ℝ :=
  2093*e^11 - 16445*e^9*f + 45540*e^7*f^2 - 53130*e^5*f^3 + 24150*e^3*f^4 - 2898*e*f^5

private def newton23row5 (e f : ℝ) : ℝ :=
  2277*e^8 - 10626*e^6*f + 14490*e^4*f^2 - 5796*e^2*f^3 + 322*f^4

private def newton23row6 (e f : ℝ) : ℝ :=
  966*e^5 - 1932*e^3*f + 644*e*f^2

private def newton23row7 (e f : ℝ) : ℝ :=
  92*e^2 - 23*f

private def newton23 (e f g : ℝ) : ℝ :=
  newton23row0 e f +
  newton23row1 e f*g^1 +
  newton23row2 e f*g^2 +
  newton23row3 e f*g^3 +
  newton23row4 e f*g^4 +
  newton23row5 e f*g^5 +
  newton23row6 e f*g^6 +
  newton23row7 e f*g^7

private theorem newton23_rec (e f g : ℝ) :
    e*newton22 e f g - f*newton21 e f g + g*newton20 e f g = newton23 e f g := by
  unfold newton23 newton23row0 newton23row1 newton23row2 newton23row3 newton23row4 newton23row5
    newton23row6 newton23row7 newton22 newton22row0 newton22row1 newton22row2 newton22row3
    newton22row4 newton22row5 newton22row6 newton22row7 newton21 newton21row0 newton21row1
    newton21row2 newton21row3 newton21row4 newton21row5 newton21row6 newton21row7 newton20
    newton20row0 newton20row1 newton20row2 newton20row3 newton20row4 newton20row5 newton20row6
  ring

private theorem newton23_eval (p q r : ℝ) :
    sumPowers 23 p q r = newton23 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  have h := sumPowers_recurrence 20 p q r
  change sumPowers 23 p q r = (p+q+r)*sumPowers 22 p q r -
    (p*q+q*r+r*p)*sumPowers 21 p q r + p*q*r*sumPowers 20 p q r at h
  rw [newton22_eval, newton21_eval, newton20_eval] at h
  exact h.trans (newton23_rec _ _ _)

private def newton24row0 (e f : ℝ) : ℝ :=
  e^24 - 24*e^22*f + 252*e^20*f^2 - 1520*e^18*f^3 + 5814*e^16*f^4 - 14688*e^14*f^5 +
      24752*e^12*f^6 - 27456*e^10*f^7 + 19305*e^8*f^8 - 8008*e^6*f^9 + 1716*e^4*f^10 -
      144*e^2*f^11 + 2*f^12

private def newton24row1 (e f : ℝ) : ℝ :=
  24*e^21 - 480*e^19*f + 4104*e^17*f^2 - 19584*e^15*f^3 + 57120*e^13*f^4 - 104832*e^11*f^5 +
      120120*e^9*f^6 - 82368*e^7*f^7 + 30888*e^5*f^8 - 5280*e^3*f^9 + 264*e*f^10

private def newton24row2 (e f : ℝ) : ℝ :=
  228*e^18 - 3672*e^16*f + 24480*e^14*f^2 - 87360*e^12*f^3 + 180180*e^10*f^4 - 216216*e^8*f^5 +
      144144*e^6*f^6 - 47520*e^4*f^7 + 5940*e^2*f^8 - 120*f^9

private def newton24row3 (e f : ℝ) : ℝ :=
  1088*e^15 - 13440*e^13*f + 65520*e^11*f^2 - 160160*e^9*f^3 + 205920*e^7*f^4 - 133056*e^5*f^5 +
      36960*e^3*f^6 - 2880*e*f^7

private def newton24row4 (e f : ℝ) : ℝ :=
  2730*e^12 - 24024*e^10*f + 77220*e^8*f^2 - 110880*e^6*f^3 + 69300*e^4*f^4 - 15120*e^2*f^5 +
      504*f^6

private def newton24row5 (e f : ℝ) : ℝ :=
  3432*e^9 - 19008*e^7*f + 33264*e^5*f^2 - 20160*e^3*f^3 + 3024*e*f^4

private def newton24row6 (e f : ℝ) : ℝ :=
  1848*e^6 - 5040*e^4*f + 3024*e^2*f^2 - 224*f^3

private def newton24row7 (e f : ℝ) : ℝ :=
  288*e^3 - 192*e*f

private def newton24row8 (e f : ℝ) : ℝ :=
  3

private def newton24 (e f g : ℝ) : ℝ :=
  newton24row0 e f +
  newton24row1 e f*g^1 +
  newton24row2 e f*g^2 +
  newton24row3 e f*g^3 +
  newton24row4 e f*g^4 +
  newton24row5 e f*g^5 +
  newton24row6 e f*g^6 +
  newton24row7 e f*g^7 +
  newton24row8 e f*g^8

private theorem newton24_rec (e f g : ℝ) :
    e*newton23 e f g - f*newton22 e f g + g*newton21 e f g = newton24 e f g := by
  unfold newton24 newton24row0 newton24row1 newton24row2 newton24row3 newton24row4 newton24row5
    newton24row6 newton24row7 newton24row8 newton23 newton23row0 newton23row1 newton23row2
    newton23row3 newton23row4 newton23row5 newton23row6 newton23row7 newton22 newton22row0
    newton22row1 newton22row2 newton22row3 newton22row4 newton22row5 newton22row6 newton22row7
    newton21 newton21row0 newton21row1 newton21row2 newton21row3 newton21row4 newton21row5
    newton21row6 newton21row7
  ring

private theorem newton24_eval (p q r : ℝ) :
    sumPowers 24 p q r = newton24 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  have h := sumPowers_recurrence 21 p q r
  change sumPowers 24 p q r = (p+q+r)*sumPowers 23 p q r -
    (p*q+q*r+r*p)*sumPowers 22 p q r + p*q*r*sumPowers 21 p q r at h
  rw [newton23_eval, newton22_eval, newton21_eval] at h
  exact h.trans (newton24_rec _ _ _)

private def newton25row0 (e f : ℝ) : ℝ :=
  e^25 - 25*e^23*f + 275*e^21*f^2 - 1750*e^19*f^3 + 7125*e^17*f^4 - 19380*e^15*f^5 +
      35700*e^13*f^6 - 44200*e^11*f^7 + 35750*e^9*f^8 - 17875*e^7*f^9 + 5005*e^5*f^10 -
      650*e^3*f^11 + 25*e*f^12

private def newton25row1 (e f : ℝ) : ℝ :=
  25*e^22 - 525*e^20*f + 4750*e^18*f^2 - 24225*e^16*f^3 + 76500*e^14*f^4 - 154700*e^12*f^5 +
      200200*e^10*f^6 - 160875*e^8*f^7 + 75075*e^6*f^8 - 17875*e^4*f^9 + 1650*e^2*f^10 - 25*f^11

private def newton25row2 (e f : ℝ) : ℝ :=
  250*e^19 - 4275*e^17*f + 30600*e^15*f^2 - 119000*e^13*f^3 + 273000*e^11*f^4 - 375375*e^9*f^5 +
      300300*e^7*f^6 - 128700*e^5*f^7 + 24750*e^3*f^8 - 1375*e*f^9

private def newton25row3 (e f : ℝ) : ℝ :=
  1275*e^16 - 17000*e^14*f + 91000*e^12*f^2 - 250250*e^10*f^3 + 375375*e^8*f^4 - 300300*e^6*f^5 +
      115500*e^4*f^6 - 16500*e^2*f^7 + 375*f^8

private def newton25row4 (e f : ℝ) : ℝ :=
  3500*e^13 - 34125*e^11*f + 125125*e^9*f^2 - 214500*e^7*f^3 + 173250*e^5*f^4 - 57750*e^3*f^5 +
      5250*e*f^6

private def newton25row5 (e f : ℝ) : ℝ :=
  5005*e^10 - 32175*e^8*f + 69300*e^6*f^2 - 57750*e^4*f^3 + 15750*e^2*f^4 - 630*f^5

private def newton25row6 (e f : ℝ) : ℝ :=
  3300*e^7 - 11550*e^5*f + 10500*e^3*f^2 - 2100*e*f^3

private def newton25row7 (e f : ℝ) : ℝ :=
  750*e^4 - 900*e^2*f + 100*f^2

private def newton25row8 (e f : ℝ) : ℝ :=
  25*e

private def newton25 (e f g : ℝ) : ℝ :=
  newton25row0 e f +
  newton25row1 e f*g^1 +
  newton25row2 e f*g^2 +
  newton25row3 e f*g^3 +
  newton25row4 e f*g^4 +
  newton25row5 e f*g^5 +
  newton25row6 e f*g^6 +
  newton25row7 e f*g^7 +
  newton25row8 e f*g^8

private theorem newton25_rec (e f g : ℝ) :
    e*newton24 e f g - f*newton23 e f g + g*newton22 e f g = newton25 e f g := by
  unfold newton25 newton25row0 newton25row1 newton25row2 newton25row3 newton25row4 newton25row5
    newton25row6 newton25row7 newton25row8 newton24 newton24row0 newton24row1 newton24row2
    newton24row3 newton24row4 newton24row5 newton24row6 newton24row7 newton24row8 newton23
    newton23row0 newton23row1 newton23row2 newton23row3 newton23row4 newton23row5 newton23row6
    newton23row7 newton22 newton22row0 newton22row1 newton22row2 newton22row3 newton22row4
    newton22row5 newton22row6 newton22row7
  ring

private theorem newton25_eval (p q r : ℝ) :
    sumPowers 25 p q r = newton25 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  have h := sumPowers_recurrence 22 p q r
  change sumPowers 25 p q r = (p+q+r)*sumPowers 24 p q r -
    (p*q+q*r+r*p)*sumPowers 23 p q r + p*q*r*sumPowers 22 p q r at h
  rw [newton24_eval, newton23_eval, newton22_eval] at h
  exact h.trans (newton25_rec _ _ _)

private def newton26row0 (e f : ℝ) : ℝ :=
  e^26 - 26*e^24*f + 299*e^22*f^2 - 2002*e^20*f^3 + 8645*e^18*f^4 - 25194*e^16*f^5 +
      50388*e^14*f^6 - 68952*e^12*f^7 + 63206*e^10*f^8 - 37180*e^8*f^9 + 13013*e^6*f^10 -
      2366*e^4*f^11 + 169*e^2*f^12 - 2*f^13

private def newton26row1 (e f : ℝ) : ℝ :=
  26*e^23 - 572*e^21*f + 5460*e^19*f^2 - 29640*e^17*f^3 + 100776*e^15*f^4 - 222768*e^13*f^5 +
      321776*e^11*f^6 - 297440*e^9*f^7 + 167310*e^7*f^8 - 52052*e^5*f^9 + 7436*e^3*f^10 -
      312*e*f^11

private def newton26row2 (e f : ℝ) : ℝ :=
  273*e^20 - 4940*e^18*f + 37791*e^16*f^2 - 159120*e^14*f^3 + 402220*e^12*f^4 - 624624*e^10*f^5 +
      585585*e^8*f^6 - 312312*e^6*f^7 + 83655*e^4*f^8 - 8580*e^2*f^9 + 143*f^10

private def newton26row3 (e f : ℝ) : ℝ :=
  1482*e^17 - 21216*e^15*f + 123760*e^13*f^2 - 378560*e^11*f^3 + 650650*e^9*f^4 - 624624*e^7*f^5 +
      312312*e^5*f^6 - 68640*e^3*f^7 + 4290*e*f^8

private def newton26row4 (e f : ℝ) : ℝ :=
  4420*e^14 - 47320*e^12*f + 195195*e^10*f^2 - 390390*e^8*f^3 + 390390*e^6*f^4 - 180180*e^4*f^5 +
      30030*e^2*f^6 - 780*f^7

private def newton26row5 (e f : ℝ) : ℝ :=
  7098*e^11 - 52052*e^9*f + 133848*e^7*f^2 - 144144*e^5*f^3 + 60060*e^3*f^4 - 6552*e*f^5

private def newton26row6 (e f : ℝ) : ℝ :=
  5577*e^8 - 24024*e^6*f + 30030*e^4*f^2 - 10920*e^2*f^3 + 546*f^4

private def newton26row7 (e f : ℝ) : ℝ :=
  1716*e^5 - 3120*e^3*f + 936*e*f^2

private def newton26row8 (e f : ℝ) : ℝ :=
  117*e^2 - 26*f

private def newton26 (e f g : ℝ) : ℝ :=
  newton26row0 e f +
  newton26row1 e f*g^1 +
  newton26row2 e f*g^2 +
  newton26row3 e f*g^3 +
  newton26row4 e f*g^4 +
  newton26row5 e f*g^5 +
  newton26row6 e f*g^6 +
  newton26row7 e f*g^7 +
  newton26row8 e f*g^8

private theorem newton26_rec (e f g : ℝ) :
    e*newton25 e f g - f*newton24 e f g + g*newton23 e f g = newton26 e f g := by
  unfold newton26 newton26row0 newton26row1 newton26row2 newton26row3 newton26row4 newton26row5
    newton26row6 newton26row7 newton26row8 newton25 newton25row0 newton25row1 newton25row2
    newton25row3 newton25row4 newton25row5 newton25row6 newton25row7 newton25row8 newton24
    newton24row0 newton24row1 newton24row2 newton24row3 newton24row4 newton24row5 newton24row6
    newton24row7 newton24row8 newton23 newton23row0 newton23row1 newton23row2 newton23row3
    newton23row4 newton23row5 newton23row6 newton23row7
  ring

private theorem newton26_eval (p q r : ℝ) :
    sumPowers 26 p q r = newton26 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  have h := sumPowers_recurrence 23 p q r
  change sumPowers 26 p q r = (p+q+r)*sumPowers 25 p q r -
    (p*q+q*r+r*p)*sumPowers 24 p q r + p*q*r*sumPowers 23 p q r at h
  rw [newton25_eval, newton24_eval, newton23_eval] at h
  exact h.trans (newton26_rec _ _ _)

private def newton27row0 (e f : ℝ) : ℝ :=
  e^27 - 27*e^25*f + 324*e^23*f^2 - 2277*e^21*f^3 + 10395*e^19*f^4 - 32319*e^17*f^5 +
      69768*e^15*f^6 - 104652*e^13*f^7 + 107406*e^11*f^8 - 72930*e^9*f^9 + 30888*e^7*f^10 -
      7371*e^5*f^11 + 819*e^3*f^12 - 27*e*f^13

private def newton27row1 (e f : ℝ) : ℝ :=
  27*e^24 - 621*e^22*f + 6237*e^20*f^2 - 35910*e^18*f^3 + 130815*e^16*f^4 - 313956*e^14*f^5 +
      501228*e^12*f^6 - 525096*e^10*f^7 + 347490*e^8*f^8 - 135135*e^6*f^9 + 27027*e^4*f^10 -
      2106*e^2*f^11 + 27*f^12

private def newton27row2 (e f : ℝ) : ℝ :=
  297*e^21 - 5670*e^19*f + 46170*e^17*f^2 - 209304*e^15*f^3 + 578340*e^13*f^4 - 1002456*e^11*f^5 +
      1081080*e^9*f^6 - 694980*e^7*f^7 + 243243*e^5*f^8 - 38610*e^3*f^9 + 1782*e*f^10

private def newton27row3 (e f : ℝ) : ℝ :=
  1710*e^18 - 26163*e^16*f + 165240*e^14*f^2 - 556920*e^12*f^3 + 1081080*e^10*f^4 -
      1216215*e^8*f^5 + 756756*e^6*f^6 - 231660*e^4*f^7 + 26730*e^2*f^8 - 495*f^9

private def newton27row4 (e f : ℝ) : ℝ :=
  5508*e^15 - 64260*e^13*f + 294840*e^11*f^2 - 675675*e^9*f^3 + 810810*e^7*f^4 - 486486*e^5*f^5 +
      124740*e^3*f^6 - 8910*e*f^7

private def newton27row5 (e f : ℝ) : ℝ :=
  9828*e^12 - 81081*e^10*f + 243243*e^8*f^2 - 324324*e^6*f^3 + 187110*e^4*f^4 - 37422*e^2*f^5 +
      1134*f^6

private def newton27row6 (e f : ℝ) : ℝ :=
  9009*e^9 - 46332*e^7*f + 74844*e^5*f^2 - 41580*e^3*f^3 + 5670*e*f^4

private def newton27row7 (e f : ℝ) : ℝ :=
  3564*e^6 - 8910*e^4*f + 4860*e^2*f^2 - 324*f^3

private def newton27row8 (e f : ℝ) : ℝ :=
  405*e^3 - 243*e*f

private def newton27row9 (e f : ℝ) : ℝ :=
  3

private def newton27 (e f g : ℝ) : ℝ :=
  newton27row0 e f +
  newton27row1 e f*g^1 +
  newton27row2 e f*g^2 +
  newton27row3 e f*g^3 +
  newton27row4 e f*g^4 +
  newton27row5 e f*g^5 +
  newton27row6 e f*g^6 +
  newton27row7 e f*g^7 +
  newton27row8 e f*g^8 +
  newton27row9 e f*g^9

private theorem newton27_rec (e f g : ℝ) :
    e*newton26 e f g - f*newton25 e f g + g*newton24 e f g = newton27 e f g := by
  unfold newton27 newton27row0 newton27row1 newton27row2 newton27row3 newton27row4 newton27row5
    newton27row6 newton27row7 newton27row8 newton27row9 newton26 newton26row0 newton26row1
    newton26row2 newton26row3 newton26row4 newton26row5 newton26row6 newton26row7 newton26row8
    newton25 newton25row0 newton25row1 newton25row2 newton25row3 newton25row4 newton25row5
    newton25row6 newton25row7 newton25row8 newton24 newton24row0 newton24row1 newton24row2
    newton24row3 newton24row4 newton24row5 newton24row6 newton24row7 newton24row8
  ring

private theorem newton27_eval (p q r : ℝ) :
    sumPowers 27 p q r = newton27 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  have h := sumPowers_recurrence 24 p q r
  change sumPowers 27 p q r = (p+q+r)*sumPowers 26 p q r -
    (p*q+q*r+r*p)*sumPowers 25 p q r + p*q*r*sumPowers 24 p q r at h
  rw [newton26_eval, newton25_eval, newton24_eval] at h
  exact h.trans (newton27_rec _ _ _)

private def newton28row0 (e f : ℝ) : ℝ :=
  e^28 - 28*e^26*f + 350*e^24*f^2 - 2576*e^22*f^3 + 12397*e^20*f^4 - 40964*e^18*f^5 +
      94962*e^16*f^6 - 155040*e^14*f^7 + 176358*e^12*f^8 - 136136*e^10*f^9 + 68068*e^8*f^10 -
      20384*e^6*f^11 + 3185*e^4*f^12 - 196*e^2*f^13 + 2*f^14

private def newton28row1 (e f : ℝ) : ℝ :=
  28*e^25 - 672*e^23*f + 7084*e^21*f^2 - 43120*e^19*f^3 + 167580*e^17*f^4 - 434112*e^15*f^5 +
      759696*e^13*f^6 - 891072*e^11*f^7 + 680680*e^9*f^8 - 320320*e^7*f^9 + 84084*e^5*f^10 -
      10192*e^3*f^11 + 364*e*f^12

private def newton28row2 (e f : ℝ) : ℝ :=
  322*e^22 - 6468*e^20*f + 55860*e^18*f^2 - 271320*e^16*f^3 + 813960*e^14*f^4 - 1559376*e^12*f^5 +
      1905904*e^10*f^6 - 1441440*e^8*f^7 + 630630*e^6*f^8 - 140140*e^4*f^9 + 12012*e^2*f^10 -
      168*f^11

private def newton28row3 (e f : ℝ) : ℝ :=
  1960*e^19 - 31920*e^17*f + 217056*e^15*f^2 - 799680*e^13*f^3 + 1732640*e^11*f^4 -
      2242240*e^9*f^5 + 1681680*e^7*f^6 - 672672*e^5*f^7 + 120120*e^3*f^8 - 6160*e*f^9

private def newton28row4 (e f : ℝ) : ℝ :=
  6783*e^16 - 85680*e^14*f + 433160*e^12*f^2 - 1121120*e^10*f^3 + 1576575*e^8*f^4 -
      1177176*e^6*f^5 + 420420*e^4*f^6 - 55440*e^2*f^7 + 1155*f^8

private def newton28row5 (e f : ℝ) : ℝ :=
  13328*e^13 - 122304*e^11*f + 420420*e^9*f^2 - 672672*e^7*f^3 + 504504*e^5*f^4 - 155232*e^3*f^5 +
      12936*e*f^6

private def newton28row6 (e f : ℝ) : ℝ :=
  14014*e^10 - 84084*e^8*f + 168168*e^6*f^2 - 129360*e^4*f^3 + 32340*e^2*f^4 - 1176*f^5

private def newton28row7 (e f : ℝ) : ℝ :=
  6864*e^7 - 22176*e^5*f + 18480*e^3*f^2 - 3360*e*f^3

private def newton28row8 (e f : ℝ) : ℝ :=
  1155*e^4 - 1260*e^2*f + 126*f^2

private def newton28row9 (e f : ℝ) : ℝ :=
  28*e

private def newton28 (e f g : ℝ) : ℝ :=
  newton28row0 e f +
  newton28row1 e f*g^1 +
  newton28row2 e f*g^2 +
  newton28row3 e f*g^3 +
  newton28row4 e f*g^4 +
  newton28row5 e f*g^5 +
  newton28row6 e f*g^6 +
  newton28row7 e f*g^7 +
  newton28row8 e f*g^8 +
  newton28row9 e f*g^9

private theorem newton28_rec (e f g : ℝ) :
    e*newton27 e f g - f*newton26 e f g + g*newton25 e f g = newton28 e f g := by
  unfold newton28 newton28row0 newton28row1 newton28row2 newton28row3 newton28row4 newton28row5
    newton28row6 newton28row7 newton28row8 newton28row9 newton27 newton27row0 newton27row1
    newton27row2 newton27row3 newton27row4 newton27row5 newton27row6 newton27row7 newton27row8
    newton27row9 newton26 newton26row0 newton26row1 newton26row2 newton26row3 newton26row4
    newton26row5 newton26row6 newton26row7 newton26row8 newton25 newton25row0 newton25row1
    newton25row2 newton25row3 newton25row4 newton25row5 newton25row6 newton25row7 newton25row8
  ring

private theorem newton28_eval (p q r : ℝ) :
    sumPowers 28 p q r = newton28 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  have h := sumPowers_recurrence 25 p q r
  change sumPowers 28 p q r = (p+q+r)*sumPowers 27 p q r -
    (p*q+q*r+r*p)*sumPowers 26 p q r + p*q*r*sumPowers 25 p q r at h
  rw [newton27_eval, newton26_eval, newton25_eval] at h
  exact h.trans (newton28_rec _ _ _)

private def newton29row0 (e f : ℝ) : ℝ :=
  e^29 - 29*e^27*f + 377*e^25*f^2 - 2900*e^23*f^3 + 14674*e^21*f^4 - 51359*e^19*f^5 +
      127281*e^17*f^6 - 224808*e^15*f^7 + 281010*e^13*f^8 - 243542*e^11*f^9 + 140998*e^9*f^10 -
      51272*e^7*f^11 + 10556*e^5*f^12 - 1015*e^3*f^13 + 29*e*f^14

private def newton29row1 (e f : ℝ) : ℝ :=
  29*e^26 - 725*e^24*f + 8004*e^22*f^2 - 51359*e^20*f^3 + 212135*e^18*f^4 - 590121*e^16*f^5 +
      1124040*e^14*f^6 - 1461252*e^12*f^7 + 1268982*e^10*f^8 - 704990*e^8*f^9 + 232232*e^6*f^10 -
      39585*e^4*f^11 + 2639*e^2*f^12 - 29*f^13

private def newton29row2 (e f : ℝ) : ℝ :=
  348*e^23 - 7337*e^21*f + 66990*e^19*f^2 - 347130*e^17*f^3 + 1124040*e^15*f^4 - 2360484*e^13*f^5
      + 3230136*e^11*f^6 - 2819960*e^9*f^7 + 1492920*e^7*f^8 - 435435*e^5*f^9 + 58058*e^3*f^10 -
      2262*e*f^11

private def newton29row3 (e f : ℝ) : ℝ :=
  2233*e^20 - 38570*e^18*f + 281010*e^16*f^2 - 1124040*e^14*f^3 + 2691780*e^12*f^4 -
      3947944*e^10*f^5 + 3483480*e^8*f^6 - 1741740*e^6*f^7 + 435435*e^4*f^8 - 41470*e^2*f^9 +
      638*f^10

private def newton29row4 (e f : ℝ) : ℝ :=
  8265*e^17 - 112404*e^15*f + 621180*e^13*f^2 - 1794520*e^11*f^3 + 2902900*e^9*f^4 -
      2612610*e^7*f^5 + 1219218*e^5*f^6 - 248820*e^3*f^7 + 14355*e*f^8

private def newton29row5 (e f : ℝ) : ℝ :=
  17748*e^14 - 179452*e^12*f + 696696*e^10*f^2 - 1306305*e^8*f^3 + 1219218*e^6*f^4 -
      522522*e^4*f^5 + 80388*e^2*f^6 - 1914*f^7

private def newton29row6 (e f : ℝ) : ℝ :=
  21112*e^11 - 145145*e^9*f + 348348*e^7*f^2 - 348348*e^5*f^3 + 133980*e^3*f^4 - 13398*e*f^5

private def newton29row7 (e f : ℝ) : ℝ :=
  12441*e^8 - 49764*e^6*f + 57420*e^4*f^2 - 19140*e^2*f^3 + 870*f^4

private def newton29row8 (e f : ℝ) : ℝ :=
  2871*e^5 - 4785*e^3*f + 1305*e*f^2

private def newton29row9 (e f : ℝ) : ℝ :=
  145*e^2 - 29*f

private def newton29 (e f g : ℝ) : ℝ :=
  newton29row0 e f +
  newton29row1 e f*g^1 +
  newton29row2 e f*g^2 +
  newton29row3 e f*g^3 +
  newton29row4 e f*g^4 +
  newton29row5 e f*g^5 +
  newton29row6 e f*g^6 +
  newton29row7 e f*g^7 +
  newton29row8 e f*g^8 +
  newton29row9 e f*g^9

private theorem newton29_rec (e f g : ℝ) :
    e*newton28 e f g - f*newton27 e f g + g*newton26 e f g = newton29 e f g := by
  unfold newton29 newton29row0 newton29row1 newton29row2 newton29row3 newton29row4 newton29row5
    newton29row6 newton29row7 newton29row8 newton29row9 newton28 newton28row0 newton28row1
    newton28row2 newton28row3 newton28row4 newton28row5 newton28row6 newton28row7 newton28row8
    newton28row9 newton27 newton27row0 newton27row1 newton27row2 newton27row3 newton27row4
    newton27row5 newton27row6 newton27row7 newton27row8 newton27row9 newton26 newton26row0
    newton26row1 newton26row2 newton26row3 newton26row4 newton26row5 newton26row6 newton26row7
    newton26row8
  ring

private theorem newton29_eval (p q r : ℝ) :
    sumPowers 29 p q r = newton29 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  have h := sumPowers_recurrence 26 p q r
  change sumPowers 29 p q r = (p+q+r)*sumPowers 28 p q r -
    (p*q+q*r+r*p)*sumPowers 27 p q r + p*q*r*sumPowers 26 p q r at h
  rw [newton28_eval, newton27_eval, newton26_eval] at h
  exact h.trans (newton29_rec _ _ _)

private def newton30row0 (e f : ℝ) : ℝ :=
  e^30 - 30*e^28*f + 405*e^26*f^2 - 3250*e^24*f^3 + 17250*e^22*f^4 - 63756*e^20*f^5 +
      168245*e^18*f^6 - 319770*e^16*f^7 + 436050*e^14*f^8 - 419900*e^12*f^9 + 277134*e^10*f^10 -
      119340*e^8*f^11 + 30940*e^6*f^12 - 4200*e^4*f^13 + 225*e^2*f^14 - 2*f^15

private def newton30row1 (e f : ℝ) : ℝ :=
  30*e^27 - 780*e^25*f + 9000*e^23*f^2 - 60720*e^21*f^3 + 265650*e^19*f^4 - 790020*e^17*f^5 +
      1627920*e^15*f^6 - 2325600*e^13*f^7 + 2267460*e^11*f^8 - 1458600*e^9*f^9 + 583440*e^7*f^10 -
      131040*e^5*f^11 + 13650*e^3*f^12 - 420*e*f^13

private def newton30row2 (e f : ℝ) : ℝ :=
  375*e^24 - 8280*e^22*f + 79695*e^20*f^2 - 438900*e^18*f^3 + 1526175*e^16*f^4 - 3488400*e^14*f^5
      + 5290740*e^12*f^6 - 5250960*e^10*f^7 + 3281850*e^8*f^8 - 1201200*e^6*f^9 + 225225*e^4*f^10
      - 16380*e^2*f^11 + 195*f^12

private def newton30row3 (e f : ℝ) : ℝ :=
  2530*e^21 - 46200*e^19*f + 359100*e^17*f^2 - 1550400*e^15*f^3 + 4069800*e^13*f^4 -
      6683040*e^11*f^5 + 6806800*e^9*f^6 - 4118400*e^7*f^7 + 1351350*e^5*f^8 - 200200*e^3*f^9 +
      8580*e*f^10

private def newton30row4 (e f : ℝ) : ℝ :=
  9975*e^18 - 145350*e^16*f + 872100*e^14*f^2 - 2784600*e^12*f^3 + 5105100*e^10*f^4 -
      5405400*e^8*f^5 + 3153150*e^6*f^6 - 900900*e^4*f^7 + 96525*e^2*f^8 - 1650*f^9

private def newton30row5 (e f : ℝ) : ℝ :=
  23256*e^15 - 257040*e^13*f + 1113840*e^11*f^2 - 2402400*e^9*f^3 + 2702700*e^7*f^4 -
      1513512*e^5*f^5 + 360360*e^3*f^6 - 23760*e*f^7

private def newton30row6 (e f : ℝ) : ℝ :=
  30940*e^12 - 240240*e^10*f + 675675*e^8*f^2 - 840840*e^6*f^3 + 450450*e^4*f^4 - 83160*e^2*f^5 +
      2310*f^6

private def newton30row7 (e f : ℝ) : ℝ :=
  21450*e^9 - 102960*e^7*f + 154440*e^5*f^2 - 79200*e^3*f^3 + 9900*e*f^4

private def newton30row8 (e f : ℝ) : ℝ :=
  6435*e^6 - 14850*e^4*f + 7425*e^2*f^2 - 450*f^3

private def newton30row9 (e f : ℝ) : ℝ :=
  550*e^3 - 300*e*f

private def newton30row10 (e f : ℝ) : ℝ :=
  3

private def newton30 (e f g : ℝ) : ℝ :=
  newton30row0 e f +
  newton30row1 e f*g^1 +
  newton30row2 e f*g^2 +
  newton30row3 e f*g^3 +
  newton30row4 e f*g^4 +
  newton30row5 e f*g^5 +
  newton30row6 e f*g^6 +
  newton30row7 e f*g^7 +
  newton30row8 e f*g^8 +
  newton30row9 e f*g^9 +
  newton30row10 e f*g^10

private theorem newton30_rec (e f g : ℝ) :
    e*newton29 e f g - f*newton28 e f g + g*newton27 e f g = newton30 e f g := by
  unfold newton30 newton30row0 newton30row1 newton30row2 newton30row3 newton30row4 newton30row5
    newton30row6 newton30row7 newton30row8 newton30row9 newton30row10 newton29 newton29row0
    newton29row1 newton29row2 newton29row3 newton29row4 newton29row5 newton29row6 newton29row7
    newton29row8 newton29row9 newton28 newton28row0 newton28row1 newton28row2 newton28row3
    newton28row4 newton28row5 newton28row6 newton28row7 newton28row8 newton28row9 newton27
    newton27row0 newton27row1 newton27row2 newton27row3 newton27row4 newton27row5 newton27row6
    newton27row7 newton27row8 newton27row9
  ring

private theorem newton30_eval (p q r : ℝ) :
    sumPowers 30 p q r = newton30 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  have h := sumPowers_recurrence 27 p q r
  change sumPowers 30 p q r = (p+q+r)*sumPowers 29 p q r -
    (p*q+q*r+r*p)*sumPowers 28 p q r + p*q*r*sumPowers 27 p q r at h
  rw [newton29_eval, newton28_eval, newton27_eval] at h
  exact h.trans (newton30_rec _ _ _)

private def newton31row0 (e f : ℝ) : ℝ :=
  e^31 - 31*e^29*f + 434*e^27*f^2 - 3627*e^25*f^3 + 20150*e^23*f^4 - 78430*e^21*f^5 +
      219604*e^19*f^6 - 447051*e^17*f^7 + 660858*e^15*f^8 - 700910*e^13*f^9 + 520676*e^11*f^10 -
      260338*e^9*f^11 + 82212*e^7*f^12 - 14756*e^5*f^13 + 1240*e^3*f^14 - 31*e*f^15

private def newton31row1 (e f : ℝ) : ℝ :=
  31*e^28 - 837*e^26*f + 10075*e^24*f^2 - 71300*e^22*f^3 + 329406*e^20*f^4 - 1043119*e^18*f^5 +
      2313003*e^16*f^6 - 3604680*e^14*f^7 + 3905070*e^12*f^8 - 2863718*e^10*f^9 + 1356498*e^8*f^10
      - 383656*e^6*f^11 + 56420*e^4*f^12 - 3255*e^2*f^13 + 31*f^14

private def newton31row2 (e f : ℝ) : ℝ :=
  403*e^25 - 9300*e^23*f + 94116*e^21*f^2 - 549010*e^19*f^3 + 2040885*e^17*f^4 - 5046552*e^15*f^5
      + 8410920*e^13*f^6 - 9372168*e^11*f^7 + 6782490*e^9*f^8 - 3014440*e^7*f^9 + 744744*e^5*f^10
      - 84630*e^3*f^11 + 2821*e*f^12

private def newton31row3 (e f : ℝ) : ℝ :=
  2852*e^22 - 54901*e^20*f + 453530*e^18*f^2 - 2102730*e^16*f^3 + 6007800*e^14*f^4 -
      10934196*e^12*f^5 + 12660648*e^10*f^6 - 9043320*e^8*f^7 + 3723720*e^6*f^8 - 775775*e^4*f^9 +
      62062*e^2*f^10 - 806*f^11

private def newton31row4 (e f : ℝ) : ℝ :=
  11935*e^19 - 185535*e^17*f + 1201560*e^15*f^2 - 4205460*e^13*f^3 + 8632260*e^11*f^4 -
      10550540*e^9*f^5 + 7447440*e^7*f^6 - 2792790*e^5*f^7 + 465465*e^3*f^8 - 22165*e*f^9

private def newton31row5 (e f : ℝ) : ℝ :=
  30039*e^16 - 360468*e^14*f + 1726452*e^12*f^2 - 4220216*e^10*f^3 + 5585580*e^8*f^4 -
      3909906*e^6*f^5 + 1303302*e^4*f^6 - 159588*e^2*f^7 + 3069*f^8

private def newton31row6 (e f : ℝ) : ℝ :=
  44268*e^13 - 383656*e^11*f + 1241240*e^9*f^2 - 1861860*e^7*f^3 + 1303302*e^5*f^4 -
      372372*e^3*f^5 + 28644*e*f^6

private def newton31row7 (e f : ℝ) : ℝ :=
  35464*e^10 - 199485*e^8*f + 372372*e^6*f^2 - 265980*e^4*f^3 + 61380*e^2*f^4 - 2046*f^5

private def newton31row8 (e f : ℝ) : ℝ :=
  13299*e^7 - 39897*e^5*f + 30690*e^3*f^2 - 5115*e*f^3

private def newton31row9 (e f : ℝ) : ℝ :=
  1705*e^4 - 1705*e^2*f + 155*f^2

private def newton31row10 (e f : ℝ) : ℝ :=
  31*e

private def newton31 (e f g : ℝ) : ℝ :=
  newton31row0 e f +
  newton31row1 e f*g^1 +
  newton31row2 e f*g^2 +
  newton31row3 e f*g^3 +
  newton31row4 e f*g^4 +
  newton31row5 e f*g^5 +
  newton31row6 e f*g^6 +
  newton31row7 e f*g^7 +
  newton31row8 e f*g^8 +
  newton31row9 e f*g^9 +
  newton31row10 e f*g^10

private theorem newton31_rec (e f g : ℝ) :
    e*newton30 e f g - f*newton29 e f g + g*newton28 e f g = newton31 e f g := by
  unfold newton31 newton31row0 newton31row1 newton31row2 newton31row3 newton31row4 newton31row5
    newton31row6 newton31row7 newton31row8 newton31row9 newton31row10 newton30 newton30row0
    newton30row1 newton30row2 newton30row3 newton30row4 newton30row5 newton30row6 newton30row7
    newton30row8 newton30row9 newton30row10 newton29 newton29row0 newton29row1 newton29row2
    newton29row3 newton29row4 newton29row5 newton29row6 newton29row7 newton29row8 newton29row9
    newton28 newton28row0 newton28row1 newton28row2 newton28row3 newton28row4 newton28row5
    newton28row6 newton28row7 newton28row8 newton28row9
  ring

private theorem newton31_eval (p q r : ℝ) :
    sumPowers 31 p q r = newton31 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  have h := sumPowers_recurrence 28 p q r
  change sumPowers 31 p q r = (p+q+r)*sumPowers 30 p q r -
    (p*q+q*r+r*p)*sumPowers 29 p q r + p*q*r*sumPowers 28 p q r at h
  rw [newton30_eval, newton29_eval, newton28_eval] at h
  exact h.trans (newton31_rec _ _ _)

private def newton32row0 (e f : ℝ) : ℝ :=
  e^32 - 32*e^30*f + 464*e^28*f^2 - 4032*e^26*f^3 + 23400*e^24*f^4 - 95680*e^22*f^5 +
      283360*e^20*f^6 - 615296*e^18*f^7 + 980628*e^16*f^8 - 1136960*e^14*f^9 + 940576*e^12*f^10 -
      537472*e^10*f^11 + 201552*e^8*f^12 - 45696*e^6*f^13 + 5440*e^4*f^14 - 256*e^2*f^15 + 2*f^16

private def newton32row1 (e f : ℝ) : ℝ :=
  32*e^29 - 896*e^27*f + 11232*e^25*f^2 - 83200*e^23*f^3 + 404800*e^21*f^4 - 1360128*e^19*f^5 +
      3230304*e^17*f^6 - 5457408*e^15*f^7 + 6511680*e^13*f^8 - 5374720*e^11*f^9 + 2956096*e^9*f^10
      - 1018368*e^7*f^11 + 198016*e^5*f^12 - 17920*e^3*f^13 + 480*e*f^14

private def newton32row2 (e f : ℝ) : ℝ :=
  432*e^26 - 10400*e^24*f + 110400*e^22*f^2 - 680064*e^20*f^3 + 2691920*e^18*f^4 -
      7162848*e^16*f^5 + 13023360*e^14*f^6 - 16124160*e^12*f^7 + 13302432*e^10*f^8 -
      7001280*e^8*f^9 + 2178176*e^6*f^10 - 349440*e^4*f^11 + 21840*e^2*f^12 - 224*f^13

private def newton32row3 (e f : ℝ) : ℝ :=
  3200*e^23 - 64768*e^21*f + 566720*e^19*f^2 - 2808960*e^17*f^3 + 8682240*e^15*f^4 -
      17364480*e^13*f^5 + 22573824*e^11*f^6 - 18670080*e^9*f^7 + 9335040*e^7*f^8 - 2562560*e^5*f^9
      + 320320*e^3*f^10 - 11648*e*f^11

private def newton32row4 (e f : ℝ) : ℝ :=
  14168*e^20 - 234080*e^18*f + 1627920*e^16*f^2 - 6201600*e^14*f^3 + 14108640*e^12*f^4 -
      19603584*e^10*f^5 + 16336320*e^8*f^6 - 7687680*e^6*f^7 + 1801800*e^4*f^8 - 160160*e^2*f^9 +
      2288*f^10

private def newton32row5 (e f : ℝ) : ℝ :=
  38304*e^17 - 496128*e^15*f + 2604672*e^13*f^2 - 7128576*e^11*f^3 + 10890880*e^9*f^4 -
      9225216*e^7*f^5 + 4036032*e^5*f^6 - 768768*e^3*f^7 + 41184*e*f^8

private def newton32row6 (e f : ℝ) : ℝ :=
  62016*e^14 - 594048*e^12*f + 2178176*e^10*f^2 - 3843840*e^8*f^3 + 3363360*e^6*f^4 -
      1345344*e^4*f^5 + 192192*e^2*f^6 - 4224*f^7

private def newton32row7 (e f : ℝ) : ℝ :=
  56576*e^11 - 366080*e^9*f + 823680*e^7*f^2 - 768768*e^5*f^3 + 274560*e^3*f^4 - 25344*e*f^5

private def newton32row8 (e f : ℝ) : ℝ :=
  25740*e^8 - 96096*e^6*f + 102960*e^4*f^2 - 31680*e^2*f^3 + 1320*f^4

private def newton32row9 (e f : ℝ) : ℝ :=
  4576*e^5 - 7040*e^3*f + 1760*e*f^2

private def newton32row10 (e f : ℝ) : ℝ :=
  176*e^2 - 32*f

private def newton32 (e f g : ℝ) : ℝ :=
  newton32row0 e f +
  newton32row1 e f*g^1 +
  newton32row2 e f*g^2 +
  newton32row3 e f*g^3 +
  newton32row4 e f*g^4 +
  newton32row5 e f*g^5 +
  newton32row6 e f*g^6 +
  newton32row7 e f*g^7 +
  newton32row8 e f*g^8 +
  newton32row9 e f*g^9 +
  newton32row10 e f*g^10

private theorem newton32_rec (e f g : ℝ) :
    e*newton31 e f g - f*newton30 e f g + g*newton29 e f g = newton32 e f g := by
  unfold newton32 newton32row0 newton32row1 newton32row2 newton32row3 newton32row4 newton32row5
    newton32row6 newton32row7 newton32row8 newton32row9 newton32row10 newton31 newton31row0
    newton31row1 newton31row2 newton31row3 newton31row4 newton31row5 newton31row6 newton31row7
    newton31row8 newton31row9 newton31row10 newton30 newton30row0 newton30row1 newton30row2
    newton30row3 newton30row4 newton30row5 newton30row6 newton30row7 newton30row8 newton30row9
    newton30row10 newton29 newton29row0 newton29row1 newton29row2 newton29row3 newton29row4
    newton29row5 newton29row6 newton29row7 newton29row8 newton29row9
  ring

private theorem newton32_eval (p q r : ℝ) :
    sumPowers 32 p q r = newton32 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  have h := sumPowers_recurrence 29 p q r
  change sumPowers 32 p q r = (p+q+r)*sumPowers 31 p q r -
    (p*q+q*r+r*p)*sumPowers 30 p q r + p*q*r*sumPowers 29 p q r at h
  rw [newton31_eval, newton30_eval, newton29_eval] at h
  exact h.trans (newton32_rec _ _ _)

private def newton33row0 (e f : ℝ) : ℝ :=
  e^33 - 33*e^31*f + 495*e^29*f^2 - 4466*e^27*f^3 + 27027*e^25*f^4 - 115830*e^23*f^5 +
      361790*e^21*f^6 - 834900*e^19*f^7 + 1427679*e^17*f^8 - 1797818*e^15*f^9 + 1641486*e^13*f^10
      - 1058148*e^11*f^11 + 461890*e^9*f^12 - 127908*e^7*f^13 + 20196*e^5*f^14 - 1496*e^3*f^15 +
      33*e*f^16

private def newton33row1 (e f : ℝ) : ℝ :=
  33*e^30 - 957*e^28*f + 12474*e^26*f^2 - 96525*e^24*f^3 + 493350*e^22*f^4 - 1753290*e^20*f^5 +
      4441668*e^18*f^6 - 8090181*e^16*f^7 + 10552410*e^14*f^8 - 9699690*e^12*f^9 +
      6096948*e^10*f^10 - 2494206*e^8*f^11 + 612612*e^6*f^12 - 78540*e^4*f^13 + 3960*e^2*f^14 -
      33*f^15

private def newton33row2 (e f : ℝ) : ℝ :=
  462*e^27 - 11583*e^25*f + 128700*e^23*f^2 - 834900*e^21*f^3 + 3506580*e^19*f^4 -
      9993753*e^17*f^5 + 19697832*e^15*f^6 - 26860680*e^13*f^7 + 24942060*e^11*f^8 -
      15242370*e^9*f^9 + 5776056*e^7*f^10 - 1225224*e^5*f^11 + 120120*e^3*f^12 - 3465*e*f^13

private def newton33row3 (e f : ℝ) : ℝ :=
  3575*e^24 - 75900*e^22*f + 701316*e^20*f^2 - 3701390*e^18*f^3 + 12311145*e^16*f^4 -
      26860680*e^14*f^5 + 38798760*e^12*f^6 - 36581688*e^10*f^7 + 21660210*e^8*f^8 -
      7487480*e^6*f^9 + 1321320*e^4*f^10 - 90090*e^2*f^11 + 1001*f^12

private def newton33row4 (e f : ℝ) : ℝ :=
  16698*e^21 - 292215*e^19*f + 2172555*e^17*f^2 - 8953560*e^15*f^3 + 22383900*e^13*f^4 -
      34918884*e^11*f^5 + 33693660*e^9*f^6 - 19253520*e^7*f^7 + 5945940*e^5*f^8 - 825825*e^3*f^9 +
      33033*e*f^10

private def newton33row5 (e f : ℝ) : ℝ :=
  48279*e^18 - 671517*e^16*f + 3837240*e^14*f^2 - 11639628*e^12*f^3 + 20216196*e^10*f^4 -
      20216196*e^8*f^5 + 11099088*e^6*f^6 - 2972970*e^4*f^7 + 297297*e^2*f^8 - 4719*f^9

private def newton33row6 (e f : ℝ) : ℝ :=
  85272*e^15 - 895356*e^13*f + 3675672*e^11*f^2 - 7487480*e^9*f^3 + 7927920*e^7*f^4 -
      4162158*e^5*f^5 + 924924*e^3*f^6 - 56628*e*f^7

private def newton33row7 (e f : ℝ) : ℝ :=
  87516*e^12 - 641784*e^10*f + 1698840*e^8*f^2 - 1981980*e^6*f^3 + 990990*e^4*f^4 - 169884*e^2*f^5
      + 4356*f^6

private def newton33row8 (e f : ℝ) : ℝ :=
  47190*e^9 - 212355*e^7*f + 297297*e^5*f^2 - 141570*e^3*f^3 + 16335*e*f^4

private def newton33row9 (e f : ℝ) : ℝ :=
  11011*e^6 - 23595*e^4*f + 10890*e^2*f^2 - 605*f^3

private def newton33row10 (e f : ℝ) : ℝ :=
  726*e^3 - 363*e*f

private def newton33row11 (e f : ℝ) : ℝ :=
  3

private def newton33 (e f g : ℝ) : ℝ :=
  newton33row0 e f +
  newton33row1 e f*g^1 +
  newton33row2 e f*g^2 +
  newton33row3 e f*g^3 +
  newton33row4 e f*g^4 +
  newton33row5 e f*g^5 +
  newton33row6 e f*g^6 +
  newton33row7 e f*g^7 +
  newton33row8 e f*g^8 +
  newton33row9 e f*g^9 +
  newton33row10 e f*g^10 +
  newton33row11 e f*g^11

private theorem newton33_rec (e f g : ℝ) :
    e*newton32 e f g - f*newton31 e f g + g*newton30 e f g = newton33 e f g := by
  unfold newton33 newton33row0 newton33row1 newton33row2 newton33row3 newton33row4 newton33row5
    newton33row6 newton33row7 newton33row8 newton33row9 newton33row10 newton33row11 newton32
    newton32row0 newton32row1 newton32row2 newton32row3 newton32row4 newton32row5 newton32row6
    newton32row7 newton32row8 newton32row9 newton32row10 newton31 newton31row0 newton31row1
    newton31row2 newton31row3 newton31row4 newton31row5 newton31row6 newton31row7 newton31row8
    newton31row9 newton31row10 newton30 newton30row0 newton30row1 newton30row2 newton30row3
    newton30row4 newton30row5 newton30row6 newton30row7 newton30row8 newton30row9 newton30row10
  ring

private theorem newton33_eval (p q r : ℝ) :
    sumPowers 33 p q r = newton33 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  have h := sumPowers_recurrence 30 p q r
  change sumPowers 33 p q r = (p+q+r)*sumPowers 32 p q r -
    (p*q+q*r+r*p)*sumPowers 31 p q r + p*q*r*sumPowers 30 p q r at h
  rw [newton32_eval, newton31_eval, newton30_eval] at h
  exact h.trans (newton33_rec _ _ _)

private def newton34row0 (e f : ℝ) : ℝ :=
  e^34 - 34*e^32*f + 527*e^30*f^2 - 4930*e^28*f^3 + 31059*e^26*f^4 - 139230*e^24*f^5 +
      457470*e^22*f^6 - 1118260*e^20*f^7 + 2042975*e^18*f^8 - 2778446*e^16*f^9 + 2778446*e^14*f^10
      - 1998724*e^12*f^11 + 999362*e^10*f^12 - 329460*e^8*f^13 + 65892*e^6*f^14 - 6936*e^4*f^15 +
      289*e^2*f^16 - 2*f^17

private def newton34row1 (e f : ℝ) : ℝ :=
  34*e^31 - 1020*e^29*f + 13804*e^27*f^2 - 111384*e^25*f^3 + 596700*e^23*f^4 - 2236520*e^21*f^5 +
      6021400*e^19*f^6 - 11767536*e^17*f^7 + 16670676*e^15*f^8 - 16912280*e^13*f^9 +
      11992344*e^11*f^10 - 5710640*e^9*f^11 + 1713192*e^7*f^12 - 291312*e^5*f^13 + 23120*e^3*f^14
      - 544*e*f^15

private def newton34row2 (e f : ℝ) : ℝ :=
  493*e^28 - 12852*e^26*f + 149175*e^24*f^2 - 1016600*e^22*f^3 + 4516050*e^20*f^4 -
      13728792*e^18*f^5 + 29173683*e^16*f^6 - 43488720*e^14*f^7 + 44971290*e^12*f^8 -
      31408520*e^10*f^9 + 14133834*e^8*f^10 - 3787056*e^6*f^11 + 525980*e^4*f^12 - 28560*e^2*f^13
      + 255*f^14

private def newton34row3 (e f : ℝ) : ℝ :=
  3978*e^25 - 88400*e^23*f + 860200*e^21*f^2 - 4817120*e^19*f^3 + 17160990*e^17*f^4 -
      40589472*e^15*f^5 + 64574160*e^13*f^6 - 68527680*e^11*f^7 + 47112780*e^9*f^8 -
      19836960*e^7*f^9 + 4628624*e^5*f^10 - 495040*e^3*f^11 + 15470*e*f^12

private def newton34row4 (e f : ℝ) : ℝ :=
  19550*e^22 - 361284*e^20*f + 2860165*e^18*f^2 - 12684210*e^16*f^3 + 34593300*e^14*f^4 -
      59961720*e^12*f^5 + 65957892*e^10*f^6 - 44633160*e^8*f^7 + 17357340*e^6*f^8 -
      3403400*e^4*f^9 + 255255*e^2*f^10 - 3094*f^11

private def newton34row5 (e f : ℝ) : ℝ :=
  60214*e^19 - 895356*e^17*f + 5534928*e^15*f^2 - 18449760*e^13*f^3 + 35977032*e^11*f^4 -
      41657616*e^9*f^5 + 27771744*e^7*f^6 - 9801792*e^5*f^7 + 1531530*e^3*f^8 - 68068*e*f^9

private def newton34row6 (e f : ℝ) : ℝ :=
  115311*e^16 - 1317840*e^14*f + 5996172*e^12*f^2 - 13885872*e^10*f^3 + 17357340*e^8*f^4 -
      11435424*e^6*f^5 + 3573570*e^4*f^6 - 408408*e^2*f^7 + 7293*f^8

private def newton34row7 (e f : ℝ) : ℝ :=
  131784*e^13 - 1082016*e^11*f + 3306160*e^9*f^2 - 4667520*e^7*f^3 + 3063060*e^5*f^4 -
      816816*e^3*f^5 + 58344*e*f^6

private def newton34row8 (e f : ℝ) : ℝ :=
  82654*e^10 - 437580*e^8*f + 765765*e^6*f^2 - 510510*e^4*f^3 + 109395*e^2*f^4 - 3366*f^5

private def newton34row9 (e f : ℝ) : ℝ :=
  24310*e^7 - 68068*e^5*f + 48620*e^3*f^2 - 7480*e*f^3

private def newton34row10 (e f : ℝ) : ℝ :=
  2431*e^4 - 2244*e^2*f + 187*f^2

private def newton34row11 (e f : ℝ) : ℝ :=
  34*e

private def newton34 (e f g : ℝ) : ℝ :=
  newton34row0 e f +
  newton34row1 e f*g^1 +
  newton34row2 e f*g^2 +
  newton34row3 e f*g^3 +
  newton34row4 e f*g^4 +
  newton34row5 e f*g^5 +
  newton34row6 e f*g^6 +
  newton34row7 e f*g^7 +
  newton34row8 e f*g^8 +
  newton34row9 e f*g^9 +
  newton34row10 e f*g^10 +
  newton34row11 e f*g^11

private theorem newton34_rec (e f g : ℝ) :
    e*newton33 e f g - f*newton32 e f g + g*newton31 e f g = newton34 e f g := by
  unfold newton34 newton34row0 newton34row1 newton34row2 newton34row3 newton34row4 newton34row5
    newton34row6 newton34row7 newton34row8 newton34row9 newton34row10 newton34row11 newton33
    newton33row0 newton33row1 newton33row2 newton33row3 newton33row4 newton33row5 newton33row6
    newton33row7 newton33row8 newton33row9 newton33row10 newton33row11 newton32 newton32row0
    newton32row1 newton32row2 newton32row3 newton32row4 newton32row5 newton32row6 newton32row7
    newton32row8 newton32row9 newton32row10 newton31 newton31row0 newton31row1 newton31row2
    newton31row3 newton31row4 newton31row5 newton31row6 newton31row7 newton31row8 newton31row9
    newton31row10
  ring

private theorem newton34_eval (p q r : ℝ) :
    sumPowers 34 p q r = newton34 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  have h := sumPowers_recurrence 31 p q r
  change sumPowers 34 p q r = (p+q+r)*sumPowers 33 p q r -
    (p*q+q*r+r*p)*sumPowers 32 p q r + p*q*r*sumPowers 31 p q r at h
  rw [newton33_eval, newton32_eval, newton31_eval] at h
  exact h.trans (newton34_rec _ _ _)


private theorem newton0_dual (p q r : ℝ) :
    sumPowers 0 (p*q) (q*r) (r*p) =
      newton0 (p*q+q*r+r*p) ((p+q+r)*(p*q*r)) ((p*q*r)^2) := by
  rw [newton0_eval]
  congr 1 <;> ring

private theorem newton1_dual (p q r : ℝ) :
    sumPowers 1 (p*q) (q*r) (r*p) =
      newton1 (p*q+q*r+r*p) ((p+q+r)*(p*q*r)) ((p*q*r)^2) := by
  rw [newton1_eval]
  congr 1 <;> ring

private theorem newton2_dual (p q r : ℝ) :
    sumPowers 2 (p*q) (q*r) (r*p) =
      newton2 (p*q+q*r+r*p) ((p+q+r)*(p*q*r)) ((p*q*r)^2) := by
  rw [newton2_eval]
  congr 1 <;> ring

private theorem newton3_dual (p q r : ℝ) :
    sumPowers 3 (p*q) (q*r) (r*p) =
      newton3 (p*q+q*r+r*p) ((p+q+r)*(p*q*r)) ((p*q*r)^2) := by
  rw [newton3_eval]
  congr 1 <;> ring

private theorem newton4_dual (p q r : ℝ) :
    sumPowers 4 (p*q) (q*r) (r*p) =
      newton4 (p*q+q*r+r*p) ((p+q+r)*(p*q*r)) ((p*q*r)^2) := by
  rw [newton4_eval]
  congr 1 <;> ring

private theorem newton5_dual (p q r : ℝ) :
    sumPowers 5 (p*q) (q*r) (r*p) =
      newton5 (p*q+q*r+r*p) ((p+q+r)*(p*q*r)) ((p*q*r)^2) := by
  rw [newton5_eval]
  congr 1 <;> ring

private theorem newton6_dual (p q r : ℝ) :
    sumPowers 6 (p*q) (q*r) (r*p) =
      newton6 (p*q+q*r+r*p) ((p+q+r)*(p*q*r)) ((p*q*r)^2) := by
  rw [newton6_eval]
  congr 1 <;> ring

private theorem newton7_dual (p q r : ℝ) :
    sumPowers 7 (p*q) (q*r) (r*p) =
      newton7 (p*q+q*r+r*p) ((p+q+r)*(p*q*r)) ((p*q*r)^2) := by
  rw [newton7_eval]
  congr 1 <;> ring

private theorem newton8_dual (p q r : ℝ) :
    sumPowers 8 (p*q) (q*r) (r*p) =
      newton8 (p*q+q*r+r*p) ((p+q+r)*(p*q*r)) ((p*q*r)^2) := by
  rw [newton8_eval]
  congr 1 <;> ring

private theorem newton9_dual (p q r : ℝ) :
    sumPowers 9 (p*q) (q*r) (r*p) =
      newton9 (p*q+q*r+r*p) ((p+q+r)*(p*q*r)) ((p*q*r)^2) := by
  rw [newton9_eval]
  congr 1 <;> ring

private theorem newton10_dual (p q r : ℝ) :
    sumPowers 10 (p*q) (q*r) (r*p) =
      newton10 (p*q+q*r+r*p) ((p+q+r)*(p*q*r)) ((p*q*r)^2) := by
  rw [newton10_eval]
  congr 1 <;> ring

private theorem newton11_dual (p q r : ℝ) :
    sumPowers 11 (p*q) (q*r) (r*p) =
      newton11 (p*q+q*r+r*p) ((p+q+r)*(p*q*r)) ((p*q*r)^2) := by
  rw [newton11_eval]
  congr 1 <;> ring

private theorem newton12_dual (p q r : ℝ) :
    sumPowers 12 (p*q) (q*r) (r*p) =
      newton12 (p*q+q*r+r*p) ((p+q+r)*(p*q*r)) ((p*q*r)^2) := by
  rw [newton12_eval]
  congr 1 <;> ring

private theorem newton13_dual (p q r : ℝ) :
    sumPowers 13 (p*q) (q*r) (r*p) =
      newton13 (p*q+q*r+r*p) ((p+q+r)*(p*q*r)) ((p*q*r)^2) := by
  rw [newton13_eval]
  congr 1 <;> ring

private theorem newton14_dual (p q r : ℝ) :
    sumPowers 14 (p*q) (q*r) (r*p) =
      newton14 (p*q+q*r+r*p) ((p+q+r)*(p*q*r)) ((p*q*r)^2) := by
  rw [newton14_eval]
  congr 1 <;> ring

private theorem newton15_dual (p q r : ℝ) :
    sumPowers 15 (p*q) (q*r) (r*p) =
      newton15 (p*q+q*r+r*p) ((p+q+r)*(p*q*r)) ((p*q*r)^2) := by
  rw [newton15_eval]
  congr 1 <;> ring

private theorem newton16_dual (p q r : ℝ) :
    sumPowers 16 (p*q) (q*r) (r*p) =
      newton16 (p*q+q*r+r*p) ((p+q+r)*(p*q*r)) ((p*q*r)^2) := by
  rw [newton16_eval]
  congr 1 <;> ring

private theorem newton17_dual (p q r : ℝ) :
    sumPowers 17 (p*q) (q*r) (r*p) =
      newton17 (p*q+q*r+r*p) ((p+q+r)*(p*q*r)) ((p*q*r)^2) := by
  rw [newton17_eval]
  congr 1 <;> ring

private theorem newton18_dual (p q r : ℝ) :
    sumPowers 18 (p*q) (q*r) (r*p) =
      newton18 (p*q+q*r+r*p) ((p+q+r)*(p*q*r)) ((p*q*r)^2) := by
  rw [newton18_eval]
  congr 1 <;> ring

private theorem newton19_dual (p q r : ℝ) :
    sumPowers 19 (p*q) (q*r) (r*p) =
      newton19 (p*q+q*r+r*p) ((p+q+r)*(p*q*r)) ((p*q*r)^2) := by
  rw [newton19_eval]
  congr 1 <;> ring

private theorem newton20_dual (p q r : ℝ) :
    sumPowers 20 (p*q) (q*r) (r*p) =
      newton20 (p*q+q*r+r*p) ((p+q+r)*(p*q*r)) ((p*q*r)^2) := by
  rw [newton20_eval]
  congr 1 <;> ring

private theorem newton21_dual (p q r : ℝ) :
    sumPowers 21 (p*q) (q*r) (r*p) =
      newton21 (p*q+q*r+r*p) ((p+q+r)*(p*q*r)) ((p*q*r)^2) := by
  rw [newton21_eval]
  congr 1 <;> ring

private theorem newton22_dual (p q r : ℝ) :
    sumPowers 22 (p*q) (q*r) (r*p) =
      newton22 (p*q+q*r+r*p) ((p+q+r)*(p*q*r)) ((p*q*r)^2) := by
  rw [newton22_eval]
  congr 1 <;> ring

private theorem newton23_dual (p q r : ℝ) :
    sumPowers 23 (p*q) (q*r) (r*p) =
      newton23 (p*q+q*r+r*p) ((p+q+r)*(p*q*r)) ((p*q*r)^2) := by
  rw [newton23_eval]
  congr 1 <;> ring

private theorem newton24_dual (p q r : ℝ) :
    sumPowers 24 (p*q) (q*r) (r*p) =
      newton24 (p*q+q*r+r*p) ((p+q+r)*(p*q*r)) ((p*q*r)^2) := by
  rw [newton24_eval]
  congr 1 <;> ring

private theorem newton25_dual (p q r : ℝ) :
    sumPowers 25 (p*q) (q*r) (r*p) =
      newton25 (p*q+q*r+r*p) ((p+q+r)*(p*q*r)) ((p*q*r)^2) := by
  rw [newton25_eval]
  congr 1 <;> ring

private theorem newton26_dual (p q r : ℝ) :
    sumPowers 26 (p*q) (q*r) (r*p) =
      newton26 (p*q+q*r+r*p) ((p+q+r)*(p*q*r)) ((p*q*r)^2) := by
  rw [newton26_eval]
  congr 1 <;> ring

private theorem newton27_dual (p q r : ℝ) :
    sumPowers 27 (p*q) (q*r) (r*p) =
      newton27 (p*q+q*r+r*p) ((p+q+r)*(p*q*r)) ((p*q*r)^2) := by
  rw [newton27_eval]
  congr 1 <;> ring

private theorem newton28_dual (p q r : ℝ) :
    sumPowers 28 (p*q) (q*r) (r*p) =
      newton28 (p*q+q*r+r*p) ((p+q+r)*(p*q*r)) ((p*q*r)^2) := by
  rw [newton28_eval]
  congr 1 <;> ring

private theorem newton29_dual (p q r : ℝ) :
    sumPowers 29 (p*q) (q*r) (r*p) =
      newton29 (p*q+q*r+r*p) ((p+q+r)*(p*q*r)) ((p*q*r)^2) := by
  rw [newton29_eval]
  congr 1 <;> ring

private theorem newton30_dual (p q r : ℝ) :
    sumPowers 30 (p*q) (q*r) (r*p) =
      newton30 (p*q+q*r+r*p) ((p+q+r)*(p*q*r)) ((p*q*r)^2) := by
  rw [newton30_eval]
  congr 1 <;> ring

private theorem newton31_dual (p q r : ℝ) :
    sumPowers 31 (p*q) (q*r) (r*p) =
      newton31 (p*q+q*r+r*p) ((p+q+r)*(p*q*r)) ((p*q*r)^2) := by
  rw [newton31_eval]
  congr 1 <;> ring

private theorem newton32_dual (p q r : ℝ) :
    sumPowers 32 (p*q) (q*r) (r*p) =
      newton32 (p*q+q*r+r*p) ((p+q+r)*(p*q*r)) ((p*q*r)^2) := by
  rw [newton32_eval]
  congr 1 <;> ring

private theorem newton33_dual (p q r : ℝ) :
    sumPowers 33 (p*q) (q*r) (r*p) =
      newton33 (p*q+q*r+r*p) ((p+q+r)*(p*q*r)) ((p*q*r)^2) := by
  rw [newton33_eval]
  congr 1 <;> ring

private theorem newton34_dual (p q r : ℝ) :
    sumPowers 34 (p*q) (q*r) (r*p) =
      newton34 (p*q+q*r+r*p) ((p+q+r)*(p*q*r)) ((p*q*r)^2) := by
  rw [newton34_eval]
  congr 1 <;> ring

private def mono17_17_17 (e f g : ℝ) : ℝ :=
  g^17

private theorem mono17_17_17_eval (p q r : ℝ) :
    monomialSymmetric 17 17 17 p q r =
      mono17_17_17 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono17_17_17
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono18_17_16 (e f g : ℝ) : ℝ :=
  g^16*((newton1 e f g)*(newton1 f (e*g) (g^2))-g^1*(newton0 e f g))

private theorem mono18_17_16_eval (p q r : ℝ) :
    monomialSymmetric 18 17 16 p q r =
      mono18_17_16 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono18_17_16
  rw [← newton0_eval p q r]
  rw [← newton1_dual p q r]
  rw [← newton1_eval p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono18_18_15 (e f g : ℝ) : ℝ :=
  g^15*(newton3 f (e*g) (g^2))

private theorem mono18_18_15_eval (p q r : ℝ) :
    monomialSymmetric 18 18 15 p q r =
      mono18_18_15 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono18_18_15
  rw [← newton3_dual p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono19_16_16 (e f g : ℝ) : ℝ :=
  g^16*(newton3 e f g)

private theorem mono19_16_16_eval (p q r : ℝ) :
    monomialSymmetric 19 16 16 p q r =
      mono19_16_16 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono19_16_16
  rw [← newton3_eval p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono19_17_15 (e f g : ℝ) : ℝ :=
  g^15*((newton2 e f g)*(newton2 f (e*g) (g^2))-g^2*(newton0 e f g))

private theorem mono19_17_15_eval (p q r : ℝ) :
    monomialSymmetric 19 17 15 p q r =
      mono19_17_15 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono19_17_15
  rw [← newton0_eval p q r]
  rw [← newton2_dual p q r]
  rw [← newton2_eval p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono19_18_14 (e f g : ℝ) : ℝ :=
  g^14*((newton1 e f g)*(newton4 f (e*g) (g^2))-g^1*(newton3 f (e*g) (g^2)))

private theorem mono19_18_14_eval (p q r : ℝ) :
    monomialSymmetric 19 18 14 p q r =
      mono19_18_14 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono19_18_14
  rw [← newton1_eval p q r]
  rw [← newton3_dual p q r]
  rw [← newton4_dual p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono19_19_13 (e f g : ℝ) : ℝ :=
  g^13*(newton6 f (e*g) (g^2))

private theorem mono19_19_13_eval (p q r : ℝ) :
    monomialSymmetric 19 19 13 p q r =
      mono19_19_13 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono19_19_13
  rw [← newton6_dual p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono20_16_15 (e f g : ℝ) : ℝ :=
  g^15*((newton4 e f g)*(newton1 f (e*g) (g^2))-g^1*(newton3 e f g))

private theorem mono20_16_15_eval (p q r : ℝ) :
    monomialSymmetric 20 16 15 p q r =
      mono20_16_15 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono20_16_15
  rw [← newton1_dual p q r]
  rw [← newton3_eval p q r]
  rw [← newton4_eval p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono20_17_14 (e f g : ℝ) : ℝ :=
  g^14*((newton3 e f g)*(newton3 f (e*g) (g^2))-g^3*(newton0 e f g))

private theorem mono20_17_14_eval (p q r : ℝ) :
    monomialSymmetric 20 17 14 p q r =
      mono20_17_14 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono20_17_14
  rw [← newton0_eval p q r]
  rw [← newton3_dual p q r]
  rw [← newton3_eval p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono20_18_13 (e f g : ℝ) : ℝ :=
  g^13*((newton2 e f g)*(newton5 f (e*g) (g^2))-g^2*(newton3 f (e*g) (g^2)))

private theorem mono20_18_13_eval (p q r : ℝ) :
    monomialSymmetric 20 18 13 p q r =
      mono20_18_13 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono20_18_13
  rw [← newton2_eval p q r]
  rw [← newton3_dual p q r]
  rw [← newton5_dual p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono20_19_12 (e f g : ℝ) : ℝ :=
  g^12*((newton1 e f g)*(newton7 f (e*g) (g^2))-g^1*(newton6 f (e*g) (g^2)))

private theorem mono20_19_12_eval (p q r : ℝ) :
    monomialSymmetric 20 19 12 p q r =
      mono20_19_12 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono20_19_12
  rw [← newton1_eval p q r]
  rw [← newton6_dual p q r]
  rw [← newton7_dual p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono20_20_11 (e f g : ℝ) : ℝ :=
  g^11*(newton9 f (e*g) (g^2))

private theorem mono20_20_11_eval (p q r : ℝ) :
    monomialSymmetric 20 20 11 p q r =
      mono20_20_11 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono20_20_11
  rw [← newton9_dual p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono21_15_15 (e f g : ℝ) : ℝ :=
  g^15*(newton6 e f g)

private theorem mono21_15_15_eval (p q r : ℝ) :
    monomialSymmetric 21 15 15 p q r =
      mono21_15_15 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono21_15_15
  rw [← newton6_eval p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono21_16_14 (e f g : ℝ) : ℝ :=
  g^14*((newton5 e f g)*(newton2 f (e*g) (g^2))-g^2*(newton3 e f g))

private theorem mono21_16_14_eval (p q r : ℝ) :
    monomialSymmetric 21 16 14 p q r =
      mono21_16_14 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono21_16_14
  rw [← newton2_dual p q r]
  rw [← newton3_eval p q r]
  rw [← newton5_eval p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono21_17_13 (e f g : ℝ) : ℝ :=
  g^13*((newton4 e f g)*(newton4 f (e*g) (g^2))-g^4*(newton0 e f g))

private theorem mono21_17_13_eval (p q r : ℝ) :
    monomialSymmetric 21 17 13 p q r =
      mono21_17_13 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono21_17_13
  rw [← newton0_eval p q r]
  rw [← newton4_dual p q r]
  rw [← newton4_eval p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono21_18_12 (e f g : ℝ) : ℝ :=
  g^12*((newton3 e f g)*(newton6 f (e*g) (g^2))-g^3*(newton3 f (e*g) (g^2)))

private theorem mono21_18_12_eval (p q r : ℝ) :
    monomialSymmetric 21 18 12 p q r =
      mono21_18_12 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono21_18_12
  rw [← newton3_dual p q r]
  rw [← newton3_eval p q r]
  rw [← newton6_dual p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono21_19_11 (e f g : ℝ) : ℝ :=
  g^11*((newton2 e f g)*(newton8 f (e*g) (g^2))-g^2*(newton6 f (e*g) (g^2)))

private theorem mono21_19_11_eval (p q r : ℝ) :
    monomialSymmetric 21 19 11 p q r =
      mono21_19_11 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono21_19_11
  rw [← newton2_eval p q r]
  rw [← newton6_dual p q r]
  rw [← newton8_dual p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono21_20_10 (e f g : ℝ) : ℝ :=
  g^10*((newton1 e f g)*(newton10 f (e*g) (g^2))-g^1*(newton9 f (e*g) (g^2)))

private theorem mono21_20_10_eval (p q r : ℝ) :
    monomialSymmetric 21 20 10 p q r =
      mono21_20_10 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono21_20_10
  rw [← newton1_eval p q r]
  rw [← newton9_dual p q r]
  rw [← newton10_dual p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono21_21_9 (e f g : ℝ) : ℝ :=
  g^9*(newton12 f (e*g) (g^2))

private theorem mono21_21_9_eval (p q r : ℝ) :
    monomialSymmetric 21 21 9 p q r =
      mono21_21_9 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono21_21_9
  rw [← newton12_dual p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono22_15_14 (e f g : ℝ) : ℝ :=
  g^14*((newton7 e f g)*(newton1 f (e*g) (g^2))-g^1*(newton6 e f g))

private theorem mono22_15_14_eval (p q r : ℝ) :
    monomialSymmetric 22 15 14 p q r =
      mono22_15_14 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono22_15_14
  rw [← newton1_dual p q r]
  rw [← newton6_eval p q r]
  rw [← newton7_eval p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono22_16_13 (e f g : ℝ) : ℝ :=
  g^13*((newton6 e f g)*(newton3 f (e*g) (g^2))-g^3*(newton3 e f g))

private theorem mono22_16_13_eval (p q r : ℝ) :
    monomialSymmetric 22 16 13 p q r =
      mono22_16_13 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono22_16_13
  rw [← newton3_dual p q r]
  rw [← newton3_eval p q r]
  rw [← newton6_eval p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono22_17_12 (e f g : ℝ) : ℝ :=
  g^12*((newton5 e f g)*(newton5 f (e*g) (g^2))-g^5*(newton0 e f g))

private theorem mono22_17_12_eval (p q r : ℝ) :
    monomialSymmetric 22 17 12 p q r =
      mono22_17_12 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono22_17_12
  rw [← newton0_eval p q r]
  rw [← newton5_dual p q r]
  rw [← newton5_eval p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono22_18_11 (e f g : ℝ) : ℝ :=
  g^11*((newton4 e f g)*(newton7 f (e*g) (g^2))-g^4*(newton3 f (e*g) (g^2)))

private theorem mono22_18_11_eval (p q r : ℝ) :
    monomialSymmetric 22 18 11 p q r =
      mono22_18_11 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono22_18_11
  rw [← newton3_dual p q r]
  rw [← newton4_eval p q r]
  rw [← newton7_dual p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono22_19_10 (e f g : ℝ) : ℝ :=
  g^10*((newton3 e f g)*(newton9 f (e*g) (g^2))-g^3*(newton6 f (e*g) (g^2)))

private theorem mono22_19_10_eval (p q r : ℝ) :
    monomialSymmetric 22 19 10 p q r =
      mono22_19_10 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono22_19_10
  rw [← newton3_eval p q r]
  rw [← newton6_dual p q r]
  rw [← newton9_dual p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono22_20_9 (e f g : ℝ) : ℝ :=
  g^9*((newton2 e f g)*(newton11 f (e*g) (g^2))-g^2*(newton9 f (e*g) (g^2)))

private theorem mono22_20_9_eval (p q r : ℝ) :
    monomialSymmetric 22 20 9 p q r =
      mono22_20_9 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono22_20_9
  rw [← newton2_eval p q r]
  rw [← newton9_dual p q r]
  rw [← newton11_dual p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono22_21_8 (e f g : ℝ) : ℝ :=
  g^8*((newton1 e f g)*(newton13 f (e*g) (g^2))-g^1*(newton12 f (e*g) (g^2)))

private theorem mono22_21_8_eval (p q r : ℝ) :
    monomialSymmetric 22 21 8 p q r =
      mono22_21_8 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono22_21_8
  rw [← newton1_eval p q r]
  rw [← newton12_dual p q r]
  rw [← newton13_dual p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono22_22_7 (e f g : ℝ) : ℝ :=
  g^7*(newton15 f (e*g) (g^2))

private theorem mono22_22_7_eval (p q r : ℝ) :
    monomialSymmetric 22 22 7 p q r =
      mono22_22_7 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono22_22_7
  rw [← newton15_dual p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono23_14_14 (e f g : ℝ) : ℝ :=
  g^14*(newton9 e f g)

private theorem mono23_14_14_eval (p q r : ℝ) :
    monomialSymmetric 23 14 14 p q r =
      mono23_14_14 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono23_14_14
  rw [← newton9_eval p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono23_15_13 (e f g : ℝ) : ℝ :=
  g^13*((newton8 e f g)*(newton2 f (e*g) (g^2))-g^2*(newton6 e f g))

private theorem mono23_15_13_eval (p q r : ℝ) :
    monomialSymmetric 23 15 13 p q r =
      mono23_15_13 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono23_15_13
  rw [← newton2_dual p q r]
  rw [← newton6_eval p q r]
  rw [← newton8_eval p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono23_16_12 (e f g : ℝ) : ℝ :=
  g^12*((newton7 e f g)*(newton4 f (e*g) (g^2))-g^4*(newton3 e f g))

private theorem mono23_16_12_eval (p q r : ℝ) :
    monomialSymmetric 23 16 12 p q r =
      mono23_16_12 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono23_16_12
  rw [← newton3_eval p q r]
  rw [← newton4_dual p q r]
  rw [← newton7_eval p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono23_17_11 (e f g : ℝ) : ℝ :=
  g^11*((newton6 e f g)*(newton6 f (e*g) (g^2))-g^6*(newton0 e f g))

private theorem mono23_17_11_eval (p q r : ℝ) :
    monomialSymmetric 23 17 11 p q r =
      mono23_17_11 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono23_17_11
  rw [← newton0_eval p q r]
  rw [← newton6_dual p q r]
  rw [← newton6_eval p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono23_18_10 (e f g : ℝ) : ℝ :=
  g^10*((newton5 e f g)*(newton8 f (e*g) (g^2))-g^5*(newton3 f (e*g) (g^2)))

private theorem mono23_18_10_eval (p q r : ℝ) :
    monomialSymmetric 23 18 10 p q r =
      mono23_18_10 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono23_18_10
  rw [← newton3_dual p q r]
  rw [← newton5_eval p q r]
  rw [← newton8_dual p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono23_19_9 (e f g : ℝ) : ℝ :=
  g^9*((newton4 e f g)*(newton10 f (e*g) (g^2))-g^4*(newton6 f (e*g) (g^2)))

private theorem mono23_19_9_eval (p q r : ℝ) :
    monomialSymmetric 23 19 9 p q r =
      mono23_19_9 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono23_19_9
  rw [← newton4_eval p q r]
  rw [← newton6_dual p q r]
  rw [← newton10_dual p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono23_20_8 (e f g : ℝ) : ℝ :=
  g^8*((newton3 e f g)*(newton12 f (e*g) (g^2))-g^3*(newton9 f (e*g) (g^2)))

private theorem mono23_20_8_eval (p q r : ℝ) :
    monomialSymmetric 23 20 8 p q r =
      mono23_20_8 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono23_20_8
  rw [← newton3_eval p q r]
  rw [← newton9_dual p q r]
  rw [← newton12_dual p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono23_21_7 (e f g : ℝ) : ℝ :=
  g^7*((newton2 e f g)*(newton14 f (e*g) (g^2))-g^2*(newton12 f (e*g) (g^2)))

private theorem mono23_21_7_eval (p q r : ℝ) :
    monomialSymmetric 23 21 7 p q r =
      mono23_21_7 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono23_21_7
  rw [← newton2_eval p q r]
  rw [← newton12_dual p q r]
  rw [← newton14_dual p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono23_22_6 (e f g : ℝ) : ℝ :=
  g^6*((newton1 e f g)*(newton16 f (e*g) (g^2))-g^1*(newton15 f (e*g) (g^2)))

private theorem mono23_22_6_eval (p q r : ℝ) :
    monomialSymmetric 23 22 6 p q r =
      mono23_22_6 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono23_22_6
  rw [← newton1_eval p q r]
  rw [← newton15_dual p q r]
  rw [← newton16_dual p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono23_23_5 (e f g : ℝ) : ℝ :=
  g^5*(newton18 f (e*g) (g^2))

private theorem mono23_23_5_eval (p q r : ℝ) :
    monomialSymmetric 23 23 5 p q r =
      mono23_23_5 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono23_23_5
  rw [← newton18_dual p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono24_14_13 (e f g : ℝ) : ℝ :=
  g^13*((newton10 e f g)*(newton1 f (e*g) (g^2))-g^1*(newton9 e f g))

private theorem mono24_14_13_eval (p q r : ℝ) :
    monomialSymmetric 24 14 13 p q r =
      mono24_14_13 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono24_14_13
  rw [← newton1_dual p q r]
  rw [← newton9_eval p q r]
  rw [← newton10_eval p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono24_15_12 (e f g : ℝ) : ℝ :=
  g^12*((newton9 e f g)*(newton3 f (e*g) (g^2))-g^3*(newton6 e f g))

private theorem mono24_15_12_eval (p q r : ℝ) :
    monomialSymmetric 24 15 12 p q r =
      mono24_15_12 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono24_15_12
  rw [← newton3_dual p q r]
  rw [← newton6_eval p q r]
  rw [← newton9_eval p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono24_16_11 (e f g : ℝ) : ℝ :=
  g^11*((newton8 e f g)*(newton5 f (e*g) (g^2))-g^5*(newton3 e f g))

private theorem mono24_16_11_eval (p q r : ℝ) :
    monomialSymmetric 24 16 11 p q r =
      mono24_16_11 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono24_16_11
  rw [← newton3_eval p q r]
  rw [← newton5_dual p q r]
  rw [← newton8_eval p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono24_17_10 (e f g : ℝ) : ℝ :=
  g^10*((newton7 e f g)*(newton7 f (e*g) (g^2))-g^7*(newton0 e f g))

private theorem mono24_17_10_eval (p q r : ℝ) :
    monomialSymmetric 24 17 10 p q r =
      mono24_17_10 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono24_17_10
  rw [← newton0_eval p q r]
  rw [← newton7_dual p q r]
  rw [← newton7_eval p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono24_18_9 (e f g : ℝ) : ℝ :=
  g^9*((newton6 e f g)*(newton9 f (e*g) (g^2))-g^6*(newton3 f (e*g) (g^2)))

private theorem mono24_18_9_eval (p q r : ℝ) :
    monomialSymmetric 24 18 9 p q r =
      mono24_18_9 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono24_18_9
  rw [← newton3_dual p q r]
  rw [← newton6_eval p q r]
  rw [← newton9_dual p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono24_19_8 (e f g : ℝ) : ℝ :=
  g^8*((newton5 e f g)*(newton11 f (e*g) (g^2))-g^5*(newton6 f (e*g) (g^2)))

private theorem mono24_19_8_eval (p q r : ℝ) :
    monomialSymmetric 24 19 8 p q r =
      mono24_19_8 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono24_19_8
  rw [← newton5_eval p q r]
  rw [← newton6_dual p q r]
  rw [← newton11_dual p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono24_20_7 (e f g : ℝ) : ℝ :=
  g^7*((newton4 e f g)*(newton13 f (e*g) (g^2))-g^4*(newton9 f (e*g) (g^2)))

private theorem mono24_20_7_eval (p q r : ℝ) :
    monomialSymmetric 24 20 7 p q r =
      mono24_20_7 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono24_20_7
  rw [← newton4_eval p q r]
  rw [← newton9_dual p q r]
  rw [← newton13_dual p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono24_21_6 (e f g : ℝ) : ℝ :=
  g^6*((newton3 e f g)*(newton15 f (e*g) (g^2))-g^3*(newton12 f (e*g) (g^2)))

private theorem mono24_21_6_eval (p q r : ℝ) :
    monomialSymmetric 24 21 6 p q r =
      mono24_21_6 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono24_21_6
  rw [← newton3_eval p q r]
  rw [← newton12_dual p q r]
  rw [← newton15_dual p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono24_22_5 (e f g : ℝ) : ℝ :=
  g^5*((newton2 e f g)*(newton17 f (e*g) (g^2))-g^2*(newton15 f (e*g) (g^2)))

private theorem mono24_22_5_eval (p q r : ℝ) :
    monomialSymmetric 24 22 5 p q r =
      mono24_22_5 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono24_22_5
  rw [← newton2_eval p q r]
  rw [← newton15_dual p q r]
  rw [← newton17_dual p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono24_23_4 (e f g : ℝ) : ℝ :=
  g^4*((newton1 e f g)*(newton19 f (e*g) (g^2))-g^1*(newton18 f (e*g) (g^2)))

private theorem mono24_23_4_eval (p q r : ℝ) :
    monomialSymmetric 24 23 4 p q r =
      mono24_23_4 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono24_23_4
  rw [← newton1_eval p q r]
  rw [← newton18_dual p q r]
  rw [← newton19_dual p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono24_24_3 (e f g : ℝ) : ℝ :=
  g^3*(newton21 f (e*g) (g^2))

private theorem mono24_24_3_eval (p q r : ℝ) :
    monomialSymmetric 24 24 3 p q r =
      mono24_24_3 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono24_24_3
  rw [← newton21_dual p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono25_13_13 (e f g : ℝ) : ℝ :=
  g^13*(newton12 e f g)

private theorem mono25_13_13_eval (p q r : ℝ) :
    monomialSymmetric 25 13 13 p q r =
      mono25_13_13 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono25_13_13
  rw [← newton12_eval p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono25_14_12 (e f g : ℝ) : ℝ :=
  g^12*((newton11 e f g)*(newton2 f (e*g) (g^2))-g^2*(newton9 e f g))

private theorem mono25_14_12_eval (p q r : ℝ) :
    monomialSymmetric 25 14 12 p q r =
      mono25_14_12 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono25_14_12
  rw [← newton2_dual p q r]
  rw [← newton9_eval p q r]
  rw [← newton11_eval p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono25_15_11 (e f g : ℝ) : ℝ :=
  g^11*((newton10 e f g)*(newton4 f (e*g) (g^2))-g^4*(newton6 e f g))

private theorem mono25_15_11_eval (p q r : ℝ) :
    monomialSymmetric 25 15 11 p q r =
      mono25_15_11 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono25_15_11
  rw [← newton4_dual p q r]
  rw [← newton6_eval p q r]
  rw [← newton10_eval p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono25_16_10 (e f g : ℝ) : ℝ :=
  g^10*((newton9 e f g)*(newton6 f (e*g) (g^2))-g^6*(newton3 e f g))

private theorem mono25_16_10_eval (p q r : ℝ) :
    monomialSymmetric 25 16 10 p q r =
      mono25_16_10 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono25_16_10
  rw [← newton3_eval p q r]
  rw [← newton6_dual p q r]
  rw [← newton9_eval p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono25_17_9 (e f g : ℝ) : ℝ :=
  g^9*((newton8 e f g)*(newton8 f (e*g) (g^2))-g^8*(newton0 e f g))

private theorem mono25_17_9_eval (p q r : ℝ) :
    monomialSymmetric 25 17 9 p q r =
      mono25_17_9 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono25_17_9
  rw [← newton0_eval p q r]
  rw [← newton8_dual p q r]
  rw [← newton8_eval p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono25_18_8 (e f g : ℝ) : ℝ :=
  g^8*((newton7 e f g)*(newton10 f (e*g) (g^2))-g^7*(newton3 f (e*g) (g^2)))

private theorem mono25_18_8_eval (p q r : ℝ) :
    monomialSymmetric 25 18 8 p q r =
      mono25_18_8 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono25_18_8
  rw [← newton3_dual p q r]
  rw [← newton7_eval p q r]
  rw [← newton10_dual p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono25_19_7 (e f g : ℝ) : ℝ :=
  g^7*((newton6 e f g)*(newton12 f (e*g) (g^2))-g^6*(newton6 f (e*g) (g^2)))

private theorem mono25_19_7_eval (p q r : ℝ) :
    monomialSymmetric 25 19 7 p q r =
      mono25_19_7 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono25_19_7
  rw [← newton6_dual p q r]
  rw [← newton6_eval p q r]
  rw [← newton12_dual p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono25_20_6 (e f g : ℝ) : ℝ :=
  g^6*((newton5 e f g)*(newton14 f (e*g) (g^2))-g^5*(newton9 f (e*g) (g^2)))

private theorem mono25_20_6_eval (p q r : ℝ) :
    monomialSymmetric 25 20 6 p q r =
      mono25_20_6 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono25_20_6
  rw [← newton5_eval p q r]
  rw [← newton9_dual p q r]
  rw [← newton14_dual p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono25_21_5 (e f g : ℝ) : ℝ :=
  g^5*((newton4 e f g)*(newton16 f (e*g) (g^2))-g^4*(newton12 f (e*g) (g^2)))

private theorem mono25_21_5_eval (p q r : ℝ) :
    monomialSymmetric 25 21 5 p q r =
      mono25_21_5 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono25_21_5
  rw [← newton4_eval p q r]
  rw [← newton12_dual p q r]
  rw [← newton16_dual p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono25_22_4 (e f g : ℝ) : ℝ :=
  g^4*((newton3 e f g)*(newton18 f (e*g) (g^2))-g^3*(newton15 f (e*g) (g^2)))

private theorem mono25_22_4_eval (p q r : ℝ) :
    monomialSymmetric 25 22 4 p q r =
      mono25_22_4 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono25_22_4
  rw [← newton3_eval p q r]
  rw [← newton15_dual p q r]
  rw [← newton18_dual p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono25_23_3 (e f g : ℝ) : ℝ :=
  g^3*((newton2 e f g)*(newton20 f (e*g) (g^2))-g^2*(newton18 f (e*g) (g^2)))

private theorem mono25_23_3_eval (p q r : ℝ) :
    monomialSymmetric 25 23 3 p q r =
      mono25_23_3 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono25_23_3
  rw [← newton2_eval p q r]
  rw [← newton18_dual p q r]
  rw [← newton20_dual p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono25_24_2 (e f g : ℝ) : ℝ :=
  g^2*((newton1 e f g)*(newton22 f (e*g) (g^2))-g^1*(newton21 f (e*g) (g^2)))

private theorem mono25_24_2_eval (p q r : ℝ) :
    monomialSymmetric 25 24 2 p q r =
      mono25_24_2 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono25_24_2
  rw [← newton1_eval p q r]
  rw [← newton21_dual p q r]
  rw [← newton22_dual p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono25_25_1 (e f g : ℝ) : ℝ :=
  g^1*(newton24 f (e*g) (g^2))

private theorem mono25_25_1_eval (p q r : ℝ) :
    monomialSymmetric 25 25 1 p q r =
      mono25_25_1 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono25_25_1
  rw [← newton24_dual p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono26_13_12 (e f g : ℝ) : ℝ :=
  g^12*((newton13 e f g)*(newton1 f (e*g) (g^2))-g^1*(newton12 e f g))

private theorem mono26_13_12_eval (p q r : ℝ) :
    monomialSymmetric 26 13 12 p q r =
      mono26_13_12 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono26_13_12
  rw [← newton1_dual p q r]
  rw [← newton12_eval p q r]
  rw [← newton13_eval p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono26_14_11 (e f g : ℝ) : ℝ :=
  g^11*((newton12 e f g)*(newton3 f (e*g) (g^2))-g^3*(newton9 e f g))

private theorem mono26_14_11_eval (p q r : ℝ) :
    monomialSymmetric 26 14 11 p q r =
      mono26_14_11 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono26_14_11
  rw [← newton3_dual p q r]
  rw [← newton9_eval p q r]
  rw [← newton12_eval p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono26_15_10 (e f g : ℝ) : ℝ :=
  g^10*((newton11 e f g)*(newton5 f (e*g) (g^2))-g^5*(newton6 e f g))

private theorem mono26_15_10_eval (p q r : ℝ) :
    monomialSymmetric 26 15 10 p q r =
      mono26_15_10 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono26_15_10
  rw [← newton5_dual p q r]
  rw [← newton6_eval p q r]
  rw [← newton11_eval p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono26_16_9 (e f g : ℝ) : ℝ :=
  g^9*((newton10 e f g)*(newton7 f (e*g) (g^2))-g^7*(newton3 e f g))

private theorem mono26_16_9_eval (p q r : ℝ) :
    monomialSymmetric 26 16 9 p q r =
      mono26_16_9 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono26_16_9
  rw [← newton3_eval p q r]
  rw [← newton7_dual p q r]
  rw [← newton10_eval p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono26_17_8 (e f g : ℝ) : ℝ :=
  g^8*((newton9 e f g)*(newton9 f (e*g) (g^2))-g^9*(newton0 e f g))

private theorem mono26_17_8_eval (p q r : ℝ) :
    monomialSymmetric 26 17 8 p q r =
      mono26_17_8 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono26_17_8
  rw [← newton0_eval p q r]
  rw [← newton9_dual p q r]
  rw [← newton9_eval p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono26_18_7 (e f g : ℝ) : ℝ :=
  g^7*((newton8 e f g)*(newton11 f (e*g) (g^2))-g^8*(newton3 f (e*g) (g^2)))

private theorem mono26_18_7_eval (p q r : ℝ) :
    monomialSymmetric 26 18 7 p q r =
      mono26_18_7 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono26_18_7
  rw [← newton3_dual p q r]
  rw [← newton8_eval p q r]
  rw [← newton11_dual p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono26_19_6 (e f g : ℝ) : ℝ :=
  g^6*((newton7 e f g)*(newton13 f (e*g) (g^2))-g^7*(newton6 f (e*g) (g^2)))

private theorem mono26_19_6_eval (p q r : ℝ) :
    monomialSymmetric 26 19 6 p q r =
      mono26_19_6 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono26_19_6
  rw [← newton6_dual p q r]
  rw [← newton7_eval p q r]
  rw [← newton13_dual p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono26_20_5 (e f g : ℝ) : ℝ :=
  g^5*((newton6 e f g)*(newton15 f (e*g) (g^2))-g^6*(newton9 f (e*g) (g^2)))

private theorem mono26_20_5_eval (p q r : ℝ) :
    monomialSymmetric 26 20 5 p q r =
      mono26_20_5 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono26_20_5
  rw [← newton6_eval p q r]
  rw [← newton9_dual p q r]
  rw [← newton15_dual p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono26_21_4 (e f g : ℝ) : ℝ :=
  g^4*((newton5 e f g)*(newton17 f (e*g) (g^2))-g^5*(newton12 f (e*g) (g^2)))

private theorem mono26_21_4_eval (p q r : ℝ) :
    monomialSymmetric 26 21 4 p q r =
      mono26_21_4 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono26_21_4
  rw [← newton5_eval p q r]
  rw [← newton12_dual p q r]
  rw [← newton17_dual p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono26_22_3 (e f g : ℝ) : ℝ :=
  g^3*((newton4 e f g)*(newton19 f (e*g) (g^2))-g^4*(newton15 f (e*g) (g^2)))

private theorem mono26_22_3_eval (p q r : ℝ) :
    monomialSymmetric 26 22 3 p q r =
      mono26_22_3 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono26_22_3
  rw [← newton4_eval p q r]
  rw [← newton15_dual p q r]
  rw [← newton19_dual p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono26_23_2 (e f g : ℝ) : ℝ :=
  g^2*((newton3 e f g)*(newton21 f (e*g) (g^2))-g^3*(newton18 f (e*g) (g^2)))

private theorem mono26_23_2_eval (p q r : ℝ) :
    monomialSymmetric 26 23 2 p q r =
      mono26_23_2 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono26_23_2
  rw [← newton3_eval p q r]
  rw [← newton18_dual p q r]
  rw [← newton21_dual p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono26_24_1 (e f g : ℝ) : ℝ :=
  g^1*((newton2 e f g)*(newton23 f (e*g) (g^2))-g^2*(newton21 f (e*g) (g^2)))

private theorem mono26_24_1_eval (p q r : ℝ) :
    monomialSymmetric 26 24 1 p q r =
      mono26_24_1 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono26_24_1
  rw [← newton2_eval p q r]
  rw [← newton21_dual p q r]
  rw [← newton23_dual p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono26_25_0 (e f g : ℝ) : ℝ :=
  g^0*((newton1 e f g)*(newton25 f (e*g) (g^2))-g^1*(newton24 f (e*g) (g^2)))

private theorem mono26_25_0_eval (p q r : ℝ) :
    monomialSymmetric 26 25 0 p q r =
      mono26_25_0 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono26_25_0
  rw [← newton1_eval p q r]
  rw [← newton24_dual p q r]
  rw [← newton25_dual p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono27_12_12 (e f g : ℝ) : ℝ :=
  g^12*(newton15 e f g)

private theorem mono27_12_12_eval (p q r : ℝ) :
    monomialSymmetric 27 12 12 p q r =
      mono27_12_12 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono27_12_12
  rw [← newton15_eval p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono27_13_11 (e f g : ℝ) : ℝ :=
  g^11*((newton14 e f g)*(newton2 f (e*g) (g^2))-g^2*(newton12 e f g))

private theorem mono27_13_11_eval (p q r : ℝ) :
    monomialSymmetric 27 13 11 p q r =
      mono27_13_11 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono27_13_11
  rw [← newton2_dual p q r]
  rw [← newton12_eval p q r]
  rw [← newton14_eval p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono27_14_10 (e f g : ℝ) : ℝ :=
  g^10*((newton13 e f g)*(newton4 f (e*g) (g^2))-g^4*(newton9 e f g))

private theorem mono27_14_10_eval (p q r : ℝ) :
    monomialSymmetric 27 14 10 p q r =
      mono27_14_10 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono27_14_10
  rw [← newton4_dual p q r]
  rw [← newton9_eval p q r]
  rw [← newton13_eval p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono27_15_9 (e f g : ℝ) : ℝ :=
  g^9*((newton12 e f g)*(newton6 f (e*g) (g^2))-g^6*(newton6 e f g))

private theorem mono27_15_9_eval (p q r : ℝ) :
    monomialSymmetric 27 15 9 p q r =
      mono27_15_9 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono27_15_9
  rw [← newton6_dual p q r]
  rw [← newton6_eval p q r]
  rw [← newton12_eval p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono27_16_8 (e f g : ℝ) : ℝ :=
  g^8*((newton11 e f g)*(newton8 f (e*g) (g^2))-g^8*(newton3 e f g))

private theorem mono27_16_8_eval (p q r : ℝ) :
    monomialSymmetric 27 16 8 p q r =
      mono27_16_8 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono27_16_8
  rw [← newton3_eval p q r]
  rw [← newton8_dual p q r]
  rw [← newton11_eval p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono27_17_7 (e f g : ℝ) : ℝ :=
  g^7*((newton10 e f g)*(newton10 f (e*g) (g^2))-g^10*(newton0 e f g))

private theorem mono27_17_7_eval (p q r : ℝ) :
    monomialSymmetric 27 17 7 p q r =
      mono27_17_7 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono27_17_7
  rw [← newton0_eval p q r]
  rw [← newton10_dual p q r]
  rw [← newton10_eval p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono27_18_6 (e f g : ℝ) : ℝ :=
  g^6*((newton9 e f g)*(newton12 f (e*g) (g^2))-g^9*(newton3 f (e*g) (g^2)))

private theorem mono27_18_6_eval (p q r : ℝ) :
    monomialSymmetric 27 18 6 p q r =
      mono27_18_6 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono27_18_6
  rw [← newton3_dual p q r]
  rw [← newton9_eval p q r]
  rw [← newton12_dual p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono27_19_5 (e f g : ℝ) : ℝ :=
  g^5*((newton8 e f g)*(newton14 f (e*g) (g^2))-g^8*(newton6 f (e*g) (g^2)))

private theorem mono27_19_5_eval (p q r : ℝ) :
    monomialSymmetric 27 19 5 p q r =
      mono27_19_5 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono27_19_5
  rw [← newton6_dual p q r]
  rw [← newton8_eval p q r]
  rw [← newton14_dual p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono27_20_4 (e f g : ℝ) : ℝ :=
  g^4*((newton7 e f g)*(newton16 f (e*g) (g^2))-g^7*(newton9 f (e*g) (g^2)))

private theorem mono27_20_4_eval (p q r : ℝ) :
    monomialSymmetric 27 20 4 p q r =
      mono27_20_4 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono27_20_4
  rw [← newton7_eval p q r]
  rw [← newton9_dual p q r]
  rw [← newton16_dual p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono27_21_3 (e f g : ℝ) : ℝ :=
  g^3*((newton6 e f g)*(newton18 f (e*g) (g^2))-g^6*(newton12 f (e*g) (g^2)))

private theorem mono27_21_3_eval (p q r : ℝ) :
    monomialSymmetric 27 21 3 p q r =
      mono27_21_3 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono27_21_3
  rw [← newton6_eval p q r]
  rw [← newton12_dual p q r]
  rw [← newton18_dual p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono27_22_2 (e f g : ℝ) : ℝ :=
  g^2*((newton5 e f g)*(newton20 f (e*g) (g^2))-g^5*(newton15 f (e*g) (g^2)))

private theorem mono27_22_2_eval (p q r : ℝ) :
    monomialSymmetric 27 22 2 p q r =
      mono27_22_2 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono27_22_2
  rw [← newton5_eval p q r]
  rw [← newton15_dual p q r]
  rw [← newton20_dual p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono27_23_1 (e f g : ℝ) : ℝ :=
  g^1*((newton4 e f g)*(newton22 f (e*g) (g^2))-g^4*(newton18 f (e*g) (g^2)))

private theorem mono27_23_1_eval (p q r : ℝ) :
    monomialSymmetric 27 23 1 p q r =
      mono27_23_1 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono27_23_1
  rw [← newton4_eval p q r]
  rw [← newton18_dual p q r]
  rw [← newton22_dual p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono27_24_0 (e f g : ℝ) : ℝ :=
  g^0*((newton3 e f g)*(newton24 f (e*g) (g^2))-g^3*(newton21 f (e*g) (g^2)))

private theorem mono27_24_0_eval (p q r : ℝ) :
    monomialSymmetric 27 24 0 p q r =
      mono27_24_0 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono27_24_0
  rw [← newton3_eval p q r]
  rw [← newton21_dual p q r]
  rw [← newton24_dual p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono28_12_11 (e f g : ℝ) : ℝ :=
  g^11*((newton16 e f g)*(newton1 f (e*g) (g^2))-g^1*(newton15 e f g))

private theorem mono28_12_11_eval (p q r : ℝ) :
    monomialSymmetric 28 12 11 p q r =
      mono28_12_11 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono28_12_11
  rw [← newton1_dual p q r]
  rw [← newton15_eval p q r]
  rw [← newton16_eval p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono28_13_10 (e f g : ℝ) : ℝ :=
  g^10*((newton15 e f g)*(newton3 f (e*g) (g^2))-g^3*(newton12 e f g))

private theorem mono28_13_10_eval (p q r : ℝ) :
    monomialSymmetric 28 13 10 p q r =
      mono28_13_10 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono28_13_10
  rw [← newton3_dual p q r]
  rw [← newton12_eval p q r]
  rw [← newton15_eval p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono28_14_9 (e f g : ℝ) : ℝ :=
  g^9*((newton14 e f g)*(newton5 f (e*g) (g^2))-g^5*(newton9 e f g))

private theorem mono28_14_9_eval (p q r : ℝ) :
    monomialSymmetric 28 14 9 p q r =
      mono28_14_9 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono28_14_9
  rw [← newton5_dual p q r]
  rw [← newton9_eval p q r]
  rw [← newton14_eval p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono28_15_8 (e f g : ℝ) : ℝ :=
  g^8*((newton13 e f g)*(newton7 f (e*g) (g^2))-g^7*(newton6 e f g))

private theorem mono28_15_8_eval (p q r : ℝ) :
    monomialSymmetric 28 15 8 p q r =
      mono28_15_8 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono28_15_8
  rw [← newton6_eval p q r]
  rw [← newton7_dual p q r]
  rw [← newton13_eval p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono28_16_7 (e f g : ℝ) : ℝ :=
  g^7*((newton12 e f g)*(newton9 f (e*g) (g^2))-g^9*(newton3 e f g))

private theorem mono28_16_7_eval (p q r : ℝ) :
    monomialSymmetric 28 16 7 p q r =
      mono28_16_7 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono28_16_7
  rw [← newton3_eval p q r]
  rw [← newton9_dual p q r]
  rw [← newton12_eval p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono28_17_6 (e f g : ℝ) : ℝ :=
  g^6*((newton11 e f g)*(newton11 f (e*g) (g^2))-g^11*(newton0 e f g))

private theorem mono28_17_6_eval (p q r : ℝ) :
    monomialSymmetric 28 17 6 p q r =
      mono28_17_6 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono28_17_6
  rw [← newton0_eval p q r]
  rw [← newton11_dual p q r]
  rw [← newton11_eval p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono28_18_5 (e f g : ℝ) : ℝ :=
  g^5*((newton10 e f g)*(newton13 f (e*g) (g^2))-g^10*(newton3 f (e*g) (g^2)))

private theorem mono28_18_5_eval (p q r : ℝ) :
    monomialSymmetric 28 18 5 p q r =
      mono28_18_5 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono28_18_5
  rw [← newton3_dual p q r]
  rw [← newton10_eval p q r]
  rw [← newton13_dual p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono28_19_4 (e f g : ℝ) : ℝ :=
  g^4*((newton9 e f g)*(newton15 f (e*g) (g^2))-g^9*(newton6 f (e*g) (g^2)))

private theorem mono28_19_4_eval (p q r : ℝ) :
    monomialSymmetric 28 19 4 p q r =
      mono28_19_4 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono28_19_4
  rw [← newton6_dual p q r]
  rw [← newton9_eval p q r]
  rw [← newton15_dual p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono28_20_3 (e f g : ℝ) : ℝ :=
  g^3*((newton8 e f g)*(newton17 f (e*g) (g^2))-g^8*(newton9 f (e*g) (g^2)))

private theorem mono28_20_3_eval (p q r : ℝ) :
    monomialSymmetric 28 20 3 p q r =
      mono28_20_3 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono28_20_3
  rw [← newton8_eval p q r]
  rw [← newton9_dual p q r]
  rw [← newton17_dual p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono28_21_2 (e f g : ℝ) : ℝ :=
  g^2*((newton7 e f g)*(newton19 f (e*g) (g^2))-g^7*(newton12 f (e*g) (g^2)))

private theorem mono28_21_2_eval (p q r : ℝ) :
    monomialSymmetric 28 21 2 p q r =
      mono28_21_2 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono28_21_2
  rw [← newton7_eval p q r]
  rw [← newton12_dual p q r]
  rw [← newton19_dual p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono28_22_1 (e f g : ℝ) : ℝ :=
  g^1*((newton6 e f g)*(newton21 f (e*g) (g^2))-g^6*(newton15 f (e*g) (g^2)))

private theorem mono28_22_1_eval (p q r : ℝ) :
    monomialSymmetric 28 22 1 p q r =
      mono28_22_1 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono28_22_1
  rw [← newton6_eval p q r]
  rw [← newton15_dual p q r]
  rw [← newton21_dual p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono28_23_0 (e f g : ℝ) : ℝ :=
  g^0*((newton5 e f g)*(newton23 f (e*g) (g^2))-g^5*(newton18 f (e*g) (g^2)))

private theorem mono28_23_0_eval (p q r : ℝ) :
    monomialSymmetric 28 23 0 p q r =
      mono28_23_0 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono28_23_0
  rw [← newton5_eval p q r]
  rw [← newton18_dual p q r]
  rw [← newton23_dual p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono29_11_11 (e f g : ℝ) : ℝ :=
  g^11*(newton18 e f g)

private theorem mono29_11_11_eval (p q r : ℝ) :
    monomialSymmetric 29 11 11 p q r =
      mono29_11_11 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono29_11_11
  rw [← newton18_eval p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono29_12_10 (e f g : ℝ) : ℝ :=
  g^10*((newton17 e f g)*(newton2 f (e*g) (g^2))-g^2*(newton15 e f g))

private theorem mono29_12_10_eval (p q r : ℝ) :
    monomialSymmetric 29 12 10 p q r =
      mono29_12_10 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono29_12_10
  rw [← newton2_dual p q r]
  rw [← newton15_eval p q r]
  rw [← newton17_eval p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono29_13_9 (e f g : ℝ) : ℝ :=
  g^9*((newton16 e f g)*(newton4 f (e*g) (g^2))-g^4*(newton12 e f g))

private theorem mono29_13_9_eval (p q r : ℝ) :
    monomialSymmetric 29 13 9 p q r =
      mono29_13_9 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono29_13_9
  rw [← newton4_dual p q r]
  rw [← newton12_eval p q r]
  rw [← newton16_eval p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono29_14_8 (e f g : ℝ) : ℝ :=
  g^8*((newton15 e f g)*(newton6 f (e*g) (g^2))-g^6*(newton9 e f g))

private theorem mono29_14_8_eval (p q r : ℝ) :
    monomialSymmetric 29 14 8 p q r =
      mono29_14_8 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono29_14_8
  rw [← newton6_dual p q r]
  rw [← newton9_eval p q r]
  rw [← newton15_eval p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono29_15_7 (e f g : ℝ) : ℝ :=
  g^7*((newton14 e f g)*(newton8 f (e*g) (g^2))-g^8*(newton6 e f g))

private theorem mono29_15_7_eval (p q r : ℝ) :
    monomialSymmetric 29 15 7 p q r =
      mono29_15_7 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono29_15_7
  rw [← newton6_eval p q r]
  rw [← newton8_dual p q r]
  rw [← newton14_eval p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono29_16_6 (e f g : ℝ) : ℝ :=
  g^6*((newton13 e f g)*(newton10 f (e*g) (g^2))-g^10*(newton3 e f g))

private theorem mono29_16_6_eval (p q r : ℝ) :
    monomialSymmetric 29 16 6 p q r =
      mono29_16_6 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono29_16_6
  rw [← newton3_eval p q r]
  rw [← newton10_dual p q r]
  rw [← newton13_eval p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono29_17_5 (e f g : ℝ) : ℝ :=
  g^5*((newton12 e f g)*(newton12 f (e*g) (g^2))-g^12*(newton0 e f g))

private theorem mono29_17_5_eval (p q r : ℝ) :
    monomialSymmetric 29 17 5 p q r =
      mono29_17_5 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono29_17_5
  rw [← newton0_eval p q r]
  rw [← newton12_dual p q r]
  rw [← newton12_eval p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono29_18_4 (e f g : ℝ) : ℝ :=
  g^4*((newton11 e f g)*(newton14 f (e*g) (g^2))-g^11*(newton3 f (e*g) (g^2)))

private theorem mono29_18_4_eval (p q r : ℝ) :
    monomialSymmetric 29 18 4 p q r =
      mono29_18_4 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono29_18_4
  rw [← newton3_dual p q r]
  rw [← newton11_eval p q r]
  rw [← newton14_dual p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono29_19_3 (e f g : ℝ) : ℝ :=
  g^3*((newton10 e f g)*(newton16 f (e*g) (g^2))-g^10*(newton6 f (e*g) (g^2)))

private theorem mono29_19_3_eval (p q r : ℝ) :
    monomialSymmetric 29 19 3 p q r =
      mono29_19_3 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono29_19_3
  rw [← newton6_dual p q r]
  rw [← newton10_eval p q r]
  rw [← newton16_dual p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono29_20_2 (e f g : ℝ) : ℝ :=
  g^2*((newton9 e f g)*(newton18 f (e*g) (g^2))-g^9*(newton9 f (e*g) (g^2)))

private theorem mono29_20_2_eval (p q r : ℝ) :
    monomialSymmetric 29 20 2 p q r =
      mono29_20_2 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono29_20_2
  rw [← newton9_dual p q r]
  rw [← newton9_eval p q r]
  rw [← newton18_dual p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono29_21_1 (e f g : ℝ) : ℝ :=
  g^1*((newton8 e f g)*(newton20 f (e*g) (g^2))-g^8*(newton12 f (e*g) (g^2)))

private theorem mono29_21_1_eval (p q r : ℝ) :
    monomialSymmetric 29 21 1 p q r =
      mono29_21_1 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono29_21_1
  rw [← newton8_eval p q r]
  rw [← newton12_dual p q r]
  rw [← newton20_dual p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono29_22_0 (e f g : ℝ) : ℝ :=
  g^0*((newton7 e f g)*(newton22 f (e*g) (g^2))-g^7*(newton15 f (e*g) (g^2)))

private theorem mono29_22_0_eval (p q r : ℝ) :
    monomialSymmetric 29 22 0 p q r =
      mono29_22_0 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono29_22_0
  rw [← newton7_eval p q r]
  rw [← newton15_dual p q r]
  rw [← newton22_dual p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono30_11_10 (e f g : ℝ) : ℝ :=
  g^10*((newton19 e f g)*(newton1 f (e*g) (g^2))-g^1*(newton18 e f g))

private theorem mono30_11_10_eval (p q r : ℝ) :
    monomialSymmetric 30 11 10 p q r =
      mono30_11_10 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono30_11_10
  rw [← newton1_dual p q r]
  rw [← newton18_eval p q r]
  rw [← newton19_eval p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono30_12_9 (e f g : ℝ) : ℝ :=
  g^9*((newton18 e f g)*(newton3 f (e*g) (g^2))-g^3*(newton15 e f g))

private theorem mono30_12_9_eval (p q r : ℝ) :
    monomialSymmetric 30 12 9 p q r =
      mono30_12_9 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono30_12_9
  rw [← newton3_dual p q r]
  rw [← newton15_eval p q r]
  rw [← newton18_eval p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono30_13_8 (e f g : ℝ) : ℝ :=
  g^8*((newton17 e f g)*(newton5 f (e*g) (g^2))-g^5*(newton12 e f g))

private theorem mono30_13_8_eval (p q r : ℝ) :
    monomialSymmetric 30 13 8 p q r =
      mono30_13_8 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono30_13_8
  rw [← newton5_dual p q r]
  rw [← newton12_eval p q r]
  rw [← newton17_eval p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono30_14_7 (e f g : ℝ) : ℝ :=
  g^7*((newton16 e f g)*(newton7 f (e*g) (g^2))-g^7*(newton9 e f g))

private theorem mono30_14_7_eval (p q r : ℝ) :
    monomialSymmetric 30 14 7 p q r =
      mono30_14_7 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono30_14_7
  rw [← newton7_dual p q r]
  rw [← newton9_eval p q r]
  rw [← newton16_eval p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono30_15_6 (e f g : ℝ) : ℝ :=
  g^6*((newton15 e f g)*(newton9 f (e*g) (g^2))-g^9*(newton6 e f g))

private theorem mono30_15_6_eval (p q r : ℝ) :
    monomialSymmetric 30 15 6 p q r =
      mono30_15_6 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono30_15_6
  rw [← newton6_eval p q r]
  rw [← newton9_dual p q r]
  rw [← newton15_eval p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono30_16_5 (e f g : ℝ) : ℝ :=
  g^5*((newton14 e f g)*(newton11 f (e*g) (g^2))-g^11*(newton3 e f g))

private theorem mono30_16_5_eval (p q r : ℝ) :
    monomialSymmetric 30 16 5 p q r =
      mono30_16_5 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono30_16_5
  rw [← newton3_eval p q r]
  rw [← newton11_dual p q r]
  rw [← newton14_eval p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono30_17_4 (e f g : ℝ) : ℝ :=
  g^4*((newton13 e f g)*(newton13 f (e*g) (g^2))-g^13*(newton0 e f g))

private theorem mono30_17_4_eval (p q r : ℝ) :
    monomialSymmetric 30 17 4 p q r =
      mono30_17_4 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono30_17_4
  rw [← newton0_eval p q r]
  rw [← newton13_dual p q r]
  rw [← newton13_eval p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono30_18_3 (e f g : ℝ) : ℝ :=
  g^3*((newton12 e f g)*(newton15 f (e*g) (g^2))-g^12*(newton3 f (e*g) (g^2)))

private theorem mono30_18_3_eval (p q r : ℝ) :
    monomialSymmetric 30 18 3 p q r =
      mono30_18_3 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono30_18_3
  rw [← newton3_dual p q r]
  rw [← newton12_eval p q r]
  rw [← newton15_dual p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono30_19_2 (e f g : ℝ) : ℝ :=
  g^2*((newton11 e f g)*(newton17 f (e*g) (g^2))-g^11*(newton6 f (e*g) (g^2)))

private theorem mono30_19_2_eval (p q r : ℝ) :
    monomialSymmetric 30 19 2 p q r =
      mono30_19_2 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono30_19_2
  rw [← newton6_dual p q r]
  rw [← newton11_eval p q r]
  rw [← newton17_dual p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono30_20_1 (e f g : ℝ) : ℝ :=
  g^1*((newton10 e f g)*(newton19 f (e*g) (g^2))-g^10*(newton9 f (e*g) (g^2)))

private theorem mono30_20_1_eval (p q r : ℝ) :
    monomialSymmetric 30 20 1 p q r =
      mono30_20_1 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono30_20_1
  rw [← newton9_dual p q r]
  rw [← newton10_eval p q r]
  rw [← newton19_dual p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono30_21_0 (e f g : ℝ) : ℝ :=
  g^0*((newton9 e f g)*(newton21 f (e*g) (g^2))-g^9*(newton12 f (e*g) (g^2)))

private theorem mono30_21_0_eval (p q r : ℝ) :
    monomialSymmetric 30 21 0 p q r =
      mono30_21_0 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono30_21_0
  rw [← newton9_eval p q r]
  rw [← newton12_dual p q r]
  rw [← newton21_dual p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono31_10_10 (e f g : ℝ) : ℝ :=
  g^10*(newton21 e f g)

private theorem mono31_10_10_eval (p q r : ℝ) :
    monomialSymmetric 31 10 10 p q r =
      mono31_10_10 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono31_10_10
  rw [← newton21_eval p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono31_11_9 (e f g : ℝ) : ℝ :=
  g^9*((newton20 e f g)*(newton2 f (e*g) (g^2))-g^2*(newton18 e f g))

private theorem mono31_11_9_eval (p q r : ℝ) :
    monomialSymmetric 31 11 9 p q r =
      mono31_11_9 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono31_11_9
  rw [← newton2_dual p q r]
  rw [← newton18_eval p q r]
  rw [← newton20_eval p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono31_12_8 (e f g : ℝ) : ℝ :=
  g^8*((newton19 e f g)*(newton4 f (e*g) (g^2))-g^4*(newton15 e f g))

private theorem mono31_12_8_eval (p q r : ℝ) :
    monomialSymmetric 31 12 8 p q r =
      mono31_12_8 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono31_12_8
  rw [← newton4_dual p q r]
  rw [← newton15_eval p q r]
  rw [← newton19_eval p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono31_13_7 (e f g : ℝ) : ℝ :=
  g^7*((newton18 e f g)*(newton6 f (e*g) (g^2))-g^6*(newton12 e f g))

private theorem mono31_13_7_eval (p q r : ℝ) :
    monomialSymmetric 31 13 7 p q r =
      mono31_13_7 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono31_13_7
  rw [← newton6_dual p q r]
  rw [← newton12_eval p q r]
  rw [← newton18_eval p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono31_14_6 (e f g : ℝ) : ℝ :=
  g^6*((newton17 e f g)*(newton8 f (e*g) (g^2))-g^8*(newton9 e f g))

private theorem mono31_14_6_eval (p q r : ℝ) :
    monomialSymmetric 31 14 6 p q r =
      mono31_14_6 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono31_14_6
  rw [← newton8_dual p q r]
  rw [← newton9_eval p q r]
  rw [← newton17_eval p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono31_15_5 (e f g : ℝ) : ℝ :=
  g^5*((newton16 e f g)*(newton10 f (e*g) (g^2))-g^10*(newton6 e f g))

private theorem mono31_15_5_eval (p q r : ℝ) :
    monomialSymmetric 31 15 5 p q r =
      mono31_15_5 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono31_15_5
  rw [← newton6_eval p q r]
  rw [← newton10_dual p q r]
  rw [← newton16_eval p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono31_16_4 (e f g : ℝ) : ℝ :=
  g^4*((newton15 e f g)*(newton12 f (e*g) (g^2))-g^12*(newton3 e f g))

private theorem mono31_16_4_eval (p q r : ℝ) :
    monomialSymmetric 31 16 4 p q r =
      mono31_16_4 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono31_16_4
  rw [← newton3_eval p q r]
  rw [← newton12_dual p q r]
  rw [← newton15_eval p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono31_17_3 (e f g : ℝ) : ℝ :=
  g^3*((newton14 e f g)*(newton14 f (e*g) (g^2))-g^14*(newton0 e f g))

private theorem mono31_17_3_eval (p q r : ℝ) :
    monomialSymmetric 31 17 3 p q r =
      mono31_17_3 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono31_17_3
  rw [← newton0_eval p q r]
  rw [← newton14_dual p q r]
  rw [← newton14_eval p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono31_18_2 (e f g : ℝ) : ℝ :=
  g^2*((newton13 e f g)*(newton16 f (e*g) (g^2))-g^13*(newton3 f (e*g) (g^2)))

private theorem mono31_18_2_eval (p q r : ℝ) :
    monomialSymmetric 31 18 2 p q r =
      mono31_18_2 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono31_18_2
  rw [← newton3_dual p q r]
  rw [← newton13_eval p q r]
  rw [← newton16_dual p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono31_19_1 (e f g : ℝ) : ℝ :=
  g^1*((newton12 e f g)*(newton18 f (e*g) (g^2))-g^12*(newton6 f (e*g) (g^2)))

private theorem mono31_19_1_eval (p q r : ℝ) :
    monomialSymmetric 31 19 1 p q r =
      mono31_19_1 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono31_19_1
  rw [← newton6_dual p q r]
  rw [← newton12_eval p q r]
  rw [← newton18_dual p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono31_20_0 (e f g : ℝ) : ℝ :=
  g^0*((newton11 e f g)*(newton20 f (e*g) (g^2))-g^11*(newton9 f (e*g) (g^2)))

private theorem mono31_20_0_eval (p q r : ℝ) :
    monomialSymmetric 31 20 0 p q r =
      mono31_20_0 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono31_20_0
  rw [← newton9_dual p q r]
  rw [← newton11_eval p q r]
  rw [← newton20_dual p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono32_10_9 (e f g : ℝ) : ℝ :=
  g^9*((newton22 e f g)*(newton1 f (e*g) (g^2))-g^1*(newton21 e f g))

private theorem mono32_10_9_eval (p q r : ℝ) :
    monomialSymmetric 32 10 9 p q r =
      mono32_10_9 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono32_10_9
  rw [← newton1_dual p q r]
  rw [← newton21_eval p q r]
  rw [← newton22_eval p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono32_11_8 (e f g : ℝ) : ℝ :=
  g^8*((newton21 e f g)*(newton3 f (e*g) (g^2))-g^3*(newton18 e f g))

private theorem mono32_11_8_eval (p q r : ℝ) :
    monomialSymmetric 32 11 8 p q r =
      mono32_11_8 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono32_11_8
  rw [← newton3_dual p q r]
  rw [← newton18_eval p q r]
  rw [← newton21_eval p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono32_12_7 (e f g : ℝ) : ℝ :=
  g^7*((newton20 e f g)*(newton5 f (e*g) (g^2))-g^5*(newton15 e f g))

private theorem mono32_12_7_eval (p q r : ℝ) :
    monomialSymmetric 32 12 7 p q r =
      mono32_12_7 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono32_12_7
  rw [← newton5_dual p q r]
  rw [← newton15_eval p q r]
  rw [← newton20_eval p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono32_13_6 (e f g : ℝ) : ℝ :=
  g^6*((newton19 e f g)*(newton7 f (e*g) (g^2))-g^7*(newton12 e f g))

private theorem mono32_13_6_eval (p q r : ℝ) :
    monomialSymmetric 32 13 6 p q r =
      mono32_13_6 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono32_13_6
  rw [← newton7_dual p q r]
  rw [← newton12_eval p q r]
  rw [← newton19_eval p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono32_14_5 (e f g : ℝ) : ℝ :=
  g^5*((newton18 e f g)*(newton9 f (e*g) (g^2))-g^9*(newton9 e f g))

private theorem mono32_14_5_eval (p q r : ℝ) :
    monomialSymmetric 32 14 5 p q r =
      mono32_14_5 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono32_14_5
  rw [← newton9_dual p q r]
  rw [← newton9_eval p q r]
  rw [← newton18_eval p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono32_15_4 (e f g : ℝ) : ℝ :=
  g^4*((newton17 e f g)*(newton11 f (e*g) (g^2))-g^11*(newton6 e f g))

private theorem mono32_15_4_eval (p q r : ℝ) :
    monomialSymmetric 32 15 4 p q r =
      mono32_15_4 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono32_15_4
  rw [← newton6_eval p q r]
  rw [← newton11_dual p q r]
  rw [← newton17_eval p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono32_16_3 (e f g : ℝ) : ℝ :=
  g^3*((newton16 e f g)*(newton13 f (e*g) (g^2))-g^13*(newton3 e f g))

private theorem mono32_16_3_eval (p q r : ℝ) :
    monomialSymmetric 32 16 3 p q r =
      mono32_16_3 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono32_16_3
  rw [← newton3_eval p q r]
  rw [← newton13_dual p q r]
  rw [← newton16_eval p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono32_17_2 (e f g : ℝ) : ℝ :=
  g^2*((newton15 e f g)*(newton15 f (e*g) (g^2))-g^15*(newton0 e f g))

private theorem mono32_17_2_eval (p q r : ℝ) :
    monomialSymmetric 32 17 2 p q r =
      mono32_17_2 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono32_17_2
  rw [← newton0_eval p q r]
  rw [← newton15_dual p q r]
  rw [← newton15_eval p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono32_18_1 (e f g : ℝ) : ℝ :=
  g^1*((newton14 e f g)*(newton17 f (e*g) (g^2))-g^14*(newton3 f (e*g) (g^2)))

private theorem mono32_18_1_eval (p q r : ℝ) :
    monomialSymmetric 32 18 1 p q r =
      mono32_18_1 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono32_18_1
  rw [← newton3_dual p q r]
  rw [← newton14_eval p q r]
  rw [← newton17_dual p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono32_19_0 (e f g : ℝ) : ℝ :=
  g^0*((newton13 e f g)*(newton19 f (e*g) (g^2))-g^13*(newton6 f (e*g) (g^2)))

private theorem mono32_19_0_eval (p q r : ℝ) :
    monomialSymmetric 32 19 0 p q r =
      mono32_19_0 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono32_19_0
  rw [← newton6_dual p q r]
  rw [← newton13_eval p q r]
  rw [← newton19_dual p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono33_9_9 (e f g : ℝ) : ℝ :=
  g^9*(newton24 e f g)

private theorem mono33_9_9_eval (p q r : ℝ) :
    monomialSymmetric 33 9 9 p q r =
      mono33_9_9 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono33_9_9
  rw [← newton24_eval p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono33_10_8 (e f g : ℝ) : ℝ :=
  g^8*((newton23 e f g)*(newton2 f (e*g) (g^2))-g^2*(newton21 e f g))

private theorem mono33_10_8_eval (p q r : ℝ) :
    monomialSymmetric 33 10 8 p q r =
      mono33_10_8 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono33_10_8
  rw [← newton2_dual p q r]
  rw [← newton21_eval p q r]
  rw [← newton23_eval p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono33_11_7 (e f g : ℝ) : ℝ :=
  g^7*((newton22 e f g)*(newton4 f (e*g) (g^2))-g^4*(newton18 e f g))

private theorem mono33_11_7_eval (p q r : ℝ) :
    monomialSymmetric 33 11 7 p q r =
      mono33_11_7 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono33_11_7
  rw [← newton4_dual p q r]
  rw [← newton18_eval p q r]
  rw [← newton22_eval p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono33_12_6 (e f g : ℝ) : ℝ :=
  g^6*((newton21 e f g)*(newton6 f (e*g) (g^2))-g^6*(newton15 e f g))

private theorem mono33_12_6_eval (p q r : ℝ) :
    monomialSymmetric 33 12 6 p q r =
      mono33_12_6 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono33_12_6
  rw [← newton6_dual p q r]
  rw [← newton15_eval p q r]
  rw [← newton21_eval p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono33_13_5 (e f g : ℝ) : ℝ :=
  g^5*((newton20 e f g)*(newton8 f (e*g) (g^2))-g^8*(newton12 e f g))

private theorem mono33_13_5_eval (p q r : ℝ) :
    monomialSymmetric 33 13 5 p q r =
      mono33_13_5 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono33_13_5
  rw [← newton8_dual p q r]
  rw [← newton12_eval p q r]
  rw [← newton20_eval p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono33_14_4 (e f g : ℝ) : ℝ :=
  g^4*((newton19 e f g)*(newton10 f (e*g) (g^2))-g^10*(newton9 e f g))

private theorem mono33_14_4_eval (p q r : ℝ) :
    monomialSymmetric 33 14 4 p q r =
      mono33_14_4 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono33_14_4
  rw [← newton9_eval p q r]
  rw [← newton10_dual p q r]
  rw [← newton19_eval p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono33_15_3 (e f g : ℝ) : ℝ :=
  g^3*((newton18 e f g)*(newton12 f (e*g) (g^2))-g^12*(newton6 e f g))

private theorem mono33_15_3_eval (p q r : ℝ) :
    monomialSymmetric 33 15 3 p q r =
      mono33_15_3 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono33_15_3
  rw [← newton6_eval p q r]
  rw [← newton12_dual p q r]
  rw [← newton18_eval p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono33_16_2 (e f g : ℝ) : ℝ :=
  g^2*((newton17 e f g)*(newton14 f (e*g) (g^2))-g^14*(newton3 e f g))

private theorem mono33_16_2_eval (p q r : ℝ) :
    monomialSymmetric 33 16 2 p q r =
      mono33_16_2 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono33_16_2
  rw [← newton3_eval p q r]
  rw [← newton14_dual p q r]
  rw [← newton17_eval p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono33_17_1 (e f g : ℝ) : ℝ :=
  g^1*((newton16 e f g)*(newton16 f (e*g) (g^2))-g^16*(newton0 e f g))

private theorem mono33_17_1_eval (p q r : ℝ) :
    monomialSymmetric 33 17 1 p q r =
      mono33_17_1 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono33_17_1
  rw [← newton0_eval p q r]
  rw [← newton16_dual p q r]
  rw [← newton16_eval p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono33_18_0 (e f g : ℝ) : ℝ :=
  g^0*((newton15 e f g)*(newton18 f (e*g) (g^2))-g^15*(newton3 f (e*g) (g^2)))

private theorem mono33_18_0_eval (p q r : ℝ) :
    monomialSymmetric 33 18 0 p q r =
      mono33_18_0 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono33_18_0
  rw [← newton3_dual p q r]
  rw [← newton15_eval p q r]
  rw [← newton18_dual p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono34_9_8 (e f g : ℝ) : ℝ :=
  g^8*((newton25 e f g)*(newton1 f (e*g) (g^2))-g^1*(newton24 e f g))

private theorem mono34_9_8_eval (p q r : ℝ) :
    monomialSymmetric 34 9 8 p q r =
      mono34_9_8 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono34_9_8
  rw [← newton1_dual p q r]
  rw [← newton24_eval p q r]
  rw [← newton25_eval p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono34_10_7 (e f g : ℝ) : ℝ :=
  g^7*((newton24 e f g)*(newton3 f (e*g) (g^2))-g^3*(newton21 e f g))

private theorem mono34_10_7_eval (p q r : ℝ) :
    monomialSymmetric 34 10 7 p q r =
      mono34_10_7 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono34_10_7
  rw [← newton3_dual p q r]
  rw [← newton21_eval p q r]
  rw [← newton24_eval p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono34_11_6 (e f g : ℝ) : ℝ :=
  g^6*((newton23 e f g)*(newton5 f (e*g) (g^2))-g^5*(newton18 e f g))

private theorem mono34_11_6_eval (p q r : ℝ) :
    monomialSymmetric 34 11 6 p q r =
      mono34_11_6 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono34_11_6
  rw [← newton5_dual p q r]
  rw [← newton18_eval p q r]
  rw [← newton23_eval p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono34_12_5 (e f g : ℝ) : ℝ :=
  g^5*((newton22 e f g)*(newton7 f (e*g) (g^2))-g^7*(newton15 e f g))

private theorem mono34_12_5_eval (p q r : ℝ) :
    monomialSymmetric 34 12 5 p q r =
      mono34_12_5 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono34_12_5
  rw [← newton7_dual p q r]
  rw [← newton15_eval p q r]
  rw [← newton22_eval p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono34_13_4 (e f g : ℝ) : ℝ :=
  g^4*((newton21 e f g)*(newton9 f (e*g) (g^2))-g^9*(newton12 e f g))

private theorem mono34_13_4_eval (p q r : ℝ) :
    monomialSymmetric 34 13 4 p q r =
      mono34_13_4 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono34_13_4
  rw [← newton9_dual p q r]
  rw [← newton12_eval p q r]
  rw [← newton21_eval p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono34_14_3 (e f g : ℝ) : ℝ :=
  g^3*((newton20 e f g)*(newton11 f (e*g) (g^2))-g^11*(newton9 e f g))

private theorem mono34_14_3_eval (p q r : ℝ) :
    monomialSymmetric 34 14 3 p q r =
      mono34_14_3 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono34_14_3
  rw [← newton9_eval p q r]
  rw [← newton11_dual p q r]
  rw [← newton20_eval p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono34_15_2 (e f g : ℝ) : ℝ :=
  g^2*((newton19 e f g)*(newton13 f (e*g) (g^2))-g^13*(newton6 e f g))

private theorem mono34_15_2_eval (p q r : ℝ) :
    monomialSymmetric 34 15 2 p q r =
      mono34_15_2 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono34_15_2
  rw [← newton6_eval p q r]
  rw [← newton13_dual p q r]
  rw [← newton19_eval p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def mono34_16_1 (e f g : ℝ) : ℝ :=
  g^1*((newton18 e f g)*(newton15 f (e*g) (g^2))-g^15*(newton3 e f g))

private theorem mono34_16_1_eval (p q r : ℝ) :
    monomialSymmetric 34 16 1 p q r =
      mono34_16_1 (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold mono34_16_1
  rw [← newton3_eval p q r]
  rw [← newton15_dual p q r]
  rw [← newton18_eval p q r]
  norm_num [monomialSymmetric, sumPowers, mul_pow]
  <;> ring

private def boundaryCombination (e f g : ℝ) : ℝ :=
  (4)*(mono34_16_1 e f g) +
  (52)*(mono34_15_2 e f g) +
  (152)*(mono34_14_3 e f g) +
  (-96)*(mono34_13_4 e f g) +
  (100)*(mono34_12_5 e f g) +
  (-100)*(mono34_11_6 e f g) +
  (92)*(mono34_10_7 e f g) +
  (-204)*(mono34_9_8 e f g) +
  (4)*(mono33_18_0 e f g) +
  (52)*(mono32_19_0 e f g) +
  (152)*(mono31_20_0 e f g) +
  (-96)*(mono30_21_0 e f g) +
  (100)*(mono29_22_0 e f g) +
  (-100)*(mono28_23_0 e f g) +
  (92)*(mono27_24_0 e f g) +
  (-204)*(mono26_25_0 e f g)

private theorem boundaryCombination_eval (p q r : ℝ) :
    boundaryCertificate p q r = boundaryCombination (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  have h : boundaryCertificate p q r = (4)*monomialSymmetric 34 16 1 p q r +
      (52)*monomialSymmetric 34 15 2 p q r + (152)*monomialSymmetric 34 14 3 p q r +
      (-96)*monomialSymmetric 34 13 4 p q r + (100)*monomialSymmetric 34 12 5 p q r +
      (-100)*monomialSymmetric 34 11 6 p q r + (92)*monomialSymmetric 34 10 7 p q r +
      (-204)*monomialSymmetric 34 9 8 p q r + (4)*monomialSymmetric 33 18 0 p q r +
      (52)*monomialSymmetric 32 19 0 p q r + (152)*monomialSymmetric 31 20 0 p q r +
      (-96)*monomialSymmetric 30 21 0 p q r + (100)*monomialSymmetric 29 22 0 p q r +
      (-100)*monomialSymmetric 28 23 0 p q r + (92)*monomialSymmetric 27 24 0 p q r +
      (-204)*monomialSymmetric 26 25 0 p q r := by
    norm_num [boundaryCertificate, boundaryW, H, monomialSymmetric]
    <;> ring
  rw [h]
  unfold boundaryCombination
  rw [mono26_25_0_eval, mono27_24_0_eval, mono28_23_0_eval, mono29_22_0_eval, mono30_21_0_eval,
    mono31_20_0_eval, mono32_19_0_eval, mono33_18_0_eval, mono34_9_8_eval, mono34_10_7_eval,
    mono34_11_6_eval, mono34_12_5_eval, mono34_13_4_eval, mono34_14_3_eval, mono34_15_2_eval,
    mono34_16_1_eval]

private def boundaryNormalPart0 (e f g : ℝ) : ℝ :=
  -1728*e^3*g^16
  +20736*e*f*g^16
  +1929128*e^6*g^15
  +324768*e^4*f*g^15
  -794880*e^2*f^2*g^15
  -1728*f^3*g^15
  +4080868*e^9*g^14
  -18852048*e^7*f*g^14
  -7992028*e^5*f^2*g^14
  +9736864*e^3*f^3*g^14
  +324768*e*f^4*g^14
  +4447240*e^12*g^13
  -31333672*e^10*f*g^13
  +65745664*e^8*f^2*g^13
  +68159792*e^6*f^3*g^13
  -53375680*e^4*f^4*g^13
  -7992028*e^2*f^5*g^13
  +1929128*f^6*g^13
  +2407380*e^15*g^12
  -24835872*e^13*f*g^12
  +87322068*e^11*f^2*g^12
  -78965144*e^9*f^3*g^12
  -277753504*e^7*f^4*g^12
  +137923744*e^5*f^5*g^12
  +68159792*e^3*f^6*g^12
  -18852048*e*f^7*g^12
  +639432*e^18*g^11
  -9820656*e^16*f*g^11
  +49640544*e^14*f^2*g^11
  -96107364*e^12*f^3*g^11

private def boundaryNormalPart1 (e f g : ℝ) : ℝ :=
  -75614088*e^10*f^4*g^11
  +600050176*e^8*f^5*g^11
  -108374728*e^6*f^6*g^11
  -277753504*e^4*f^7*g^11
  +65745664*e^2*f^8*g^11
  +4080868*f^9*g^11
  +78764*e^21*g^10
  -1860104*e^19*f*g^10
  +13517640*e^17*f^2*g^10
  -36770400*e^15*f^3*g^10
  -4080756*e^13*f^4*g^10
  +312341400*e^11*f^5*g^10
  -666438872*e^9*f^6*g^10
  -263816520*e^7*f^7*g^10
  +600050176*e^5*f^8*g^10
  -78965144*e^3*f^9*g^10
  -31333672*e*f^10*g^10
  +3592*e^24*g^9
  -150664*e^22*f*g^9
  +1614348*e^20*f^2*g^9
  -5584072*e^18*f^3*g^9
  -4888496*e^16*f^4*g^9
  +93604860*e^14*f^5*g^9
  -313748280*e^12*f^6*g^9
  +251019384*e^10*f^7*g^9
  +747494352*e^8*f^8*g^9
  -666438872*e^6*f^9*g^9
  -75614088*e^4*f^10*g^9
  +87322068*e^2*f^11*g^9
  +4447240*f^12*g^9

private def boundaryNormalPart2 (e f g : ℝ) : ℝ :=
  -3600*e^25*f*g^8
  +63144*e^23*f^2*g^8
  -202852*e^21*f^3*g^8
  -1992080*e^19*f^4*g^8
  +17641240*e^17*f^5*g^8
  -60949716*e^15*f^6*g^8
  +86124872*e^13*f^7*g^8
  +185189412*e^11*f^8*g^8
  -735794400*e^9*f^9*g^8
  +251019384*e^7*f^10*g^8
  +312341400*e^5*f^11*g^8
  -96107364*e^3*f^12*g^8
  -24835872*e*f^13*g^8
  +9060*e^24*f^3*g^7
  -183880*e^22*f^4*g^7
  +1310156*e^20*f^5*g^7
  -3865932*e^18*f^6*g^7
  +997520*e^16*f^7*g^7
  +43240712*e^14*f^8*g^7
  -198921528*e^12*f^9*g^7
  +266844864*e^10*f^10*g^7
  +185189412*e^8*f^11*g^7
  -313748280*e^6*f^12*g^7
  -4080756*e^4*f^13*g^7
  +49640544*e^2*f^14*g^7
  +2407380*f^15*g^7
  -7144*e^23*f^5*g^6
  +160476*e^21*f^6*g^6
  -1327212*e^19*f^7*g^6
  +6146208*e^17*f^8*g^6

private def boundaryNormalPart3 (e f g : ℝ) : ℝ :=
  -20623472*e^15*f^9*g^6
  +37181388*e^13*f^10*g^6
  +35027616*e^11*f^11*g^6
  -198921528*e^9*f^12*g^6
  +86124872*e^7*f^13*g^6
  +93604860*e^5*f^14*g^6
  -36770400*e^3*f^15*g^6
  -9820656*e*f^16*g^6
  +1340*e^22*f^7*g^5
  -41216*e^20*f^8*g^5
  +323748*e^18*f^9*g^5
  -1656636*e^16*f^10*g^5
  +9750904*e^14*f^11*g^5
  -34958560*e^12*f^12*g^5
  +37181388*e^10*f^13*g^5
  +43240712*e^8*f^14*g^5
  -60949716*e^6*f^15*g^5
  -4888496*e^4*f^16*g^5
  +13517640*e^2*f^17*g^5
  +639432*f^18*g^5
  +512*e^21*f^9*g^4
  -3800*e^19*f^10*g^4
  +76892*e^17*f^11*g^4
  -536384*e^15*f^12*g^4
  -212576*e^13*f^13*g^4
  +9750904*e^11*f^14*g^4
  -20623472*e^9*f^15*g^4
  +997520*e^7*f^16*g^4
  +17641240*e^5*f^17*g^4
  -5584072*e^3*f^18*g^4

private def boundaryNormalPart4 (e f g : ℝ) : ℝ :=
  -1860104*e*f^19*g^4
  -164*e^20*f^11*g^3
  +1200*e^18*f^12*g^3
  -32312*e^16*f^13*g^3
  +279560*e^14*f^14*g^3
  -536384*e^12*f^15*g^3
  -1656636*e^10*f^16*g^3
  +6146208*e^8*f^17*g^3
  -3865932*e^6*f^18*g^3
  -1992080*e^4*f^19*g^3
  +1614348*e^2*f^20*g^3
  +78764*f^21*g^3
  -8*e^19*f^13*g^2
  +632*e^17*f^14*g^2
  -248*e^15*f^15*g^2
  -32312*e^13*f^16*g^2
  +76892*e^11*f^17*g^2
  +323748*e^9*f^18*g^2
  -1327212*e^7*f^19*g^2
  +1310156*e^5*f^20*g^2
  -202852*e^3*f^21*g^2
  -150664*e*f^22*g^2
  +4*e^18*f^15*g
  -144*e^16*f^16*g
  +632*e^14*f^17*g
  +1200*e^12*f^18*g
  -3800*e^10*f^19*g
  -41216*e^8*f^20*g
  +160476*e^6*f^21*g
  -183880*e^4*f^22*g

private def boundaryNormalPart5 (e f g : ℝ) : ℝ :=
  63144*e^2*f^23*g
  +3592*f^24*g
  +4*e^15*f^18
  -8*e^13*f^19
  -164*e^11*f^20
  +512*e^9*f^21
  +1340*e^7*f^22
  -7144*e^5*f^23
  +9060*e^3*f^24
  -3600*e*f^25

private def boundaryNormal (e f g : ℝ) : ℝ :=
  boundaryNormalPart0 e f g + boundaryNormalPart1 e f g + boundaryNormalPart2 e f g +
      boundaryNormalPart3 e f g + boundaryNormalPart4 e f g + boundaryNormalPart5 e f g

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
-- Normalize one small symmetric slice in the elementary variables.
private theorem boundary_normal (e f g : ℝ) :
    boundaryCombination e f g = boundaryNormal e f g := by
  unfold boundaryCombination boundaryNormal boundaryNormalPart0 boundaryNormalPart1
    boundaryNormalPart2 boundaryNormalPart3 boundaryNormalPart4 boundaryNormalPart5
  unfold mono26_25_0
  unfold mono27_24_0
  unfold mono28_23_0
  unfold mono29_22_0
  unfold mono30_21_0
  unfold mono31_20_0
  unfold mono32_19_0
  unfold mono33_18_0
  unfold mono34_9_8
  unfold mono34_10_7
  unfold mono34_11_6
  unfold mono34_12_5
  unfold mono34_13_4
  unfold mono34_14_3
  unfold mono34_15_2
  unfold mono34_16_1
  unfold newton1 newton1row0
  unfold newton3 newton3row0 newton3row1
  unfold newton5 newton5row0 newton5row1
  unfold newton6 newton6row0 newton6row1 newton6row2
  unfold newton7 newton7row0 newton7row1 newton7row2
  unfold newton9 newton9row0 newton9row1 newton9row2 newton9row3
  unfold newton11 newton11row0 newton11row1 newton11row2 newton11row3
  unfold newton12 newton12row0 newton12row1 newton12row2 newton12row3 newton12row4
  unfold newton13 newton13row0 newton13row1 newton13row2 newton13row3 newton13row4
  unfold newton15 newton15row0 newton15row1 newton15row2 newton15row3 newton15row4 newton15row5
  unfold newton18 newton18row0 newton18row1 newton18row2 newton18row3 newton18row4 newton18row5
    newton18row6
  unfold newton19 newton19row0 newton19row1 newton19row2 newton19row3 newton19row4 newton19row5
    newton19row6
  unfold newton20 newton20row0 newton20row1 newton20row2 newton20row3 newton20row4 newton20row5
    newton20row6
  unfold newton21 newton21row0 newton21row1 newton21row2 newton21row3 newton21row4 newton21row5
    newton21row6 newton21row7
  unfold newton22 newton22row0 newton22row1 newton22row2 newton22row3 newton22row4 newton22row5
    newton22row6 newton22row7
  unfold newton23 newton23row0 newton23row1 newton23row2 newton23row3 newton23row4 newton23row5
    newton23row6 newton23row7
  unfold newton24 newton24row0 newton24row1 newton24row2 newton24row3 newton24row4 newton24row5
    newton24row6 newton24row7 newton24row8
  unfold newton25 newton25row0 newton25row1 newton25row2 newton25row3 newton25row4 newton25row5
    newton25row6 newton25row7 newton25row8
  ring

private theorem boundary_eval (p q r : ℝ) :
    boundaryCertificate p q r = boundaryNormal (p+q+r) (p*q+q*r+r*p) (p*q*r) :=
  (boundaryCombination_eval p q r).trans (boundary_normal _ _ _)

private def slice1Combination (e f g : ℝ) : ℝ :=
  605002*(mono25_25_1 e f g + mono33_9_9 e f g) +
  313761*(mono26_24_1 e f g + mono33_10_8 e f g) +
  199612*(mono27_23_1 e f g + mono33_11_7 e f g) +
  319069*(mono28_22_1 e f g + mono33_12_6 e f g) +
  156094*(mono29_21_1 e f g + mono33_13_5 e f g) +
  39398*(mono30_20_1 e f g + mono33_14_4 e f g) +
  15572*(mono31_19_1 e f g + mono33_15_3 e f g) +
  5051*(mono32_18_1 e f g + mono33_16_2 e f g) +
  504*(mono33_17_1 e f g)

private theorem slice1Combination_eval (p q r : ℝ) :
    positiveSlice1 p q r = slice1Combination (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold positiveSlice1 pairedMonomial slice1Combination
  norm_num only
  simp only [ite_false, ite_true, add_zero]
  rw [mono25_25_1_eval, mono26_24_1_eval, mono27_23_1_eval, mono28_22_1_eval, mono29_21_1_eval,
    mono30_20_1_eval, mono31_19_1_eval, mono32_18_1_eval, mono33_9_9_eval, mono33_10_8_eval,
    mono33_11_7_eval, mono33_12_6_eval, mono33_13_5_eval, mono33_14_4_eval, mono33_15_3_eval,
    mono33_16_2_eval, mono33_17_1_eval]

private def slice1NormalPart0 (e f g : ℝ) : ℝ :=
  3360696*g^17
  -33739352*e^3*g^16
  -219096816*e*f*g^16
  +790564074*e^6*g^15
  +5747112*e^4*f*g^15
  +3587026824*e^2*f^2*g^15
  -33739352*f^3*g^15
  +813500906*e^9*g^14
  -7142316086*e^7*f*g^14
  +3842127318*e^5*f^2*g^14
  -25493130624*e^3*f^3*g^14
  +5747112*e*f^4*g^14
  +336984096*e^12*g^13
  -6254628986*e^10*f*g^13
  +27767039408*e^8*f^2*g^13
  -27312732794*e^6*f^3*g^13
  +96298744436*e^4*f^4*g^13
  +3842127318*e^2*f^5*g^13
  +790564074*f^6*g^13
  +81472052*e^15*g^12
  -2141054904*e^13*f*g^12
  +19325736640*e^11*f^2*g^12
  -61233368140*e^9*f^3*g^12
  +85484491038*e^7*f^4*g^12
  -210769187560*e^5*f^5*g^12
  -27312732794*e^3*f^6*g^12
  -7142316086*e*f^7*g^12
  +10890316*e^18*g^11
  -387605940*e^16*f*g^11
  +5176229460*e^14*f^2*g^11

private def slice1NormalPart1 (e f g : ℝ) : ℝ :=
  -31290868836*e^12*f^3*g^11
  +83462656772*e^10*f^4*g^11
  -145731560522*e^8*f^5*g^11
  +272022414398*e^6*f^6*g^11
  +85484491038*e^4*f^7*g^11
  +27767039408*e^2*f^8*g^11
  +813500906*f^9*g^11
  +268212*e^21*g^10
  -34533332*e^19*f*g^10
  +666987532*e^17*f^2*g^10
  -6074761580*e^15*f^3*g^10
  +28410089160*e^13*f^4*g^10
  -70684181244*e^11*f^5*g^10
  +141112094156*e^9*f^6*g^10
  -193342663338*e^7*f^7*g^10
  -145731560522*e^5*f^8*g^10
  -61233368140*e^3*f^9*g^10
  -6254628986*e*f^10*g^10
  -5992*e^24*g^9
  -828387*e^22*f*g^9
  +37908079*e^20*f^2*g^9
  -501382060*e^18*f^3*g^9
  +3522610844*e^16*f^4*g^9
  -13965020532*e^14*f^5*g^9
  +34866043000*e^12*f^6*g^9
  -72627265788*e^10*f^7*g^9
  +50335668768*e^8*f^8*g^9
  +141112094156*e^6*f^9*g^9
  +83462656772*e^4*f^10*g^9
  +19325736640*e^2*f^11*g^9

private def slice1NormalPart2 (e f g : ℝ) : ℝ :=
  336984096*f^12*g^9
  +529031*e^23*f^2*g^8
  -14204461*e^21*f^3*g^8
  +141315115*e^19*f^4*g^8
  -834389482*e^17*f^5*g^8
  +3073166384*e^15*f^6*g^8
  -8137647728*e^13*f^7*g^8
  +13372496936*e^11*f^8*g^8
  +22468072528*e^9*f^9*g^8
  -72627265788*e^7*f^10*g^8
  -70684181244*e^5*f^11*g^8
  -31290868836*e^3*f^12*g^8
  -2141054904*e*f^13*g^8
  +251586*e^22*f^4*g^7
  -1037412*e^20*f^5*g^7
  +17264585*e^18*f^6*g^7
  -109747387*e^16*f^7*g^7
  +102835530*e^14*f^8*g^7
  +3342468744*e^12*f^9*g^7
  -18258249944*e^10*f^10*g^7
  +13372496936*e^8*f^11*g^7
  +34866043000*e^6*f^12*g^7
  +28410089160*e^4*f^13*g^7
  +5176229460*e^2*f^14*g^7
  +81472052*f^15*g^7
  -148511*e^21*f^6*g^6
  -1547947*e^19*f^7*g^6
  -9274141*e^17*f^8*g^6
  +261210298*e^15*f^9*g^6
  -1588253754*e^13*f^10*g^6

private def slice1NormalPart3 (e f g : ℝ) : ℝ :=
  3156646480*e^11*f^11*g^6
  +3342468744*e^9*f^12*g^6
  -8137647728*e^7*f^13*g^6
  -13965020532*e^5*f^14*g^6
  -6074761580*e^3*f^15*g^6
  -387605940*e*f^16*g^6
  -125068*e^20*f^8*g^5
  +6583515*e^18*f^9*g^5
  -49104133*e^16*f^10*g^5
  +102912750*e^14*f^11*g^5
  +327167100*e^12*f^12*g^5
  -1588253754*e^10*f^13*g^5
  +102835530*e^8*f^14*g^5
  +3073166384*e^6*f^15*g^5
  +3522610844*e^4*f^16*g^5
  +666987532*e^2*f^17*g^5
  +10890316*f^18*g^5
  +64053*e^19*f^10*g^4
  -3416837*e^17*f^11*g^4
  +30493706*e^15*f^12*g^4
  -109469192*e^13*f^13*g^4
  +102912750*e^11*f^14*g^4
  +261210298*e^9*f^15*g^4
  -109747387*e^7*f^16*g^4
  -834389482*e^5*f^17*g^4
  -501382060*e^3*f^18*g^4
  -34533332*e*f^19*g^4
  -2726*e^18*f^12*g^3
  +692319*e^16*f^13*g^3
  -7260542*e^14*f^14*g^3

private def slice1NormalPart4 (e f g : ℝ) : ℝ :=
  30493706*e^12*f^15*g^3
  -49104133*e^10*f^16*g^3
  -9274141*e^8*f^17*g^3
  +17264585*e^6*f^18*g^3
  +141315115*e^4*f^19*g^3
  +37908079*e^2*f^20*g^3
  +268212*f^21*g^3
  -3013*e^17*f^14*g^2
  -42710*e^15*f^15*g^2
  +692319*e^13*f^16*g^2
  -3416837*e^11*f^17*g^2
  +6583515*e^9*f^18*g^2
  -1547947*e^7*f^19*g^2
  -1037412*e^5*f^20*g^2
  -14204461*e^3*f^21*g^2
  -828387*e*f^22*g^2
  +504*e^16*f^16*g
  -3013*e^14*f^17*g
  -2726*e^12*f^18*g
  +64053*e^10*f^19*g
  -125068*e^8*f^20*g
  -148511*e^6*f^21*g
  +251586*e^4*f^22*g
  +529031*e^2*f^23*g
  -5992*f^24*g

private def slice1Normal (e f g : ℝ) : ℝ :=
  slice1NormalPart0 e f g + slice1NormalPart1 e f g + slice1NormalPart2 e f g + slice1NormalPart3
      e f g + slice1NormalPart4 e f g

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
-- Normalize one small symmetric slice in the elementary variables.
private theorem slice1_normal (e f g : ℝ) :
    slice1Combination e f g = slice1Normal e f g := by
  unfold slice1Combination slice1Normal slice1NormalPart0 slice1NormalPart1 slice1NormalPart2
    slice1NormalPart3 slice1NormalPart4
  unfold mono25_25_1
  unfold mono26_24_1
  unfold mono27_23_1
  unfold mono28_22_1
  unfold mono29_21_1
  unfold mono30_20_1
  unfold mono31_19_1
  unfold mono32_18_1
  unfold mono33_9_9
  unfold mono33_10_8
  unfold mono33_11_7
  unfold mono33_12_6
  unfold mono33_13_5
  unfold mono33_14_4
  unfold mono33_15_3
  unfold mono33_16_2
  unfold mono33_17_1
  unfold newton0 newton0row0
  unfold newton2 newton2row0
  unfold newton3 newton3row0 newton3row1
  unfold newton4 newton4row0 newton4row1
  unfold newton6 newton6row0 newton6row1 newton6row2
  unfold newton8 newton8row0 newton8row1 newton8row2
  unfold newton9 newton9row0 newton9row1 newton9row2 newton9row3
  unfold newton10 newton10row0 newton10row1 newton10row2 newton10row3
  unfold newton12 newton12row0 newton12row1 newton12row2 newton12row3 newton12row4
  unfold newton14 newton14row0 newton14row1 newton14row2 newton14row3 newton14row4
  unfold newton15 newton15row0 newton15row1 newton15row2 newton15row3 newton15row4 newton15row5
  unfold newton16 newton16row0 newton16row1 newton16row2 newton16row3 newton16row4 newton16row5
  unfold newton17 newton17row0 newton17row1 newton17row2 newton17row3 newton17row4 newton17row5
  unfold newton18 newton18row0 newton18row1 newton18row2 newton18row3 newton18row4 newton18row5
    newton18row6
  unfold newton19 newton19row0 newton19row1 newton19row2 newton19row3 newton19row4 newton19row5
    newton19row6
  unfold newton20 newton20row0 newton20row1 newton20row2 newton20row3 newton20row4 newton20row5
    newton20row6
  unfold newton21 newton21row0 newton21row1 newton21row2 newton21row3 newton21row4 newton21row5
    newton21row6 newton21row7
  unfold newton22 newton22row0 newton22row1 newton22row2 newton22row3 newton22row4 newton22row5
    newton22row6 newton22row7
  unfold newton23 newton23row0 newton23row1 newton23row2 newton23row3 newton23row4 newton23row5
    newton23row6 newton23row7
  unfold newton24 newton24row0 newton24row1 newton24row2 newton24row3 newton24row4 newton24row5
    newton24row6 newton24row7 newton24row8
  ring

private theorem slice1_eval (p q r : ℝ) :
    positiveSlice1 p q r = slice1Normal (p+q+r) (p*q+q*r+r*p) (p*q*r) :=
  (slice1Combination_eval p q r).trans (slice1_normal _ _ _)

private def slice2Combination (e f g : ℝ) : ℝ :=
  10743909*(mono25_24_2 e f g + mono32_10_9 e f g) +
  5726328*(mono26_23_2 e f g + mono32_11_8 e f g) +
  5654692*(mono27_22_2 e f g + mono32_12_7 e f g) +
  5187586*(mono28_21_2 e f g + mono32_13_6 e f g) +
  1987422*(mono29_20_2 e f g + mono32_14_5 e f g) +
  483020*(mono30_19_2 e f g + mono32_15_4 e f g) +
  176228*(mono31_18_2 e f g + mono32_16_3 e f g) +
  52287*(mono32_17_2 e f g)

private theorem slice2Combination_eval (p q r : ℝ) :
    positiveSlice2 p q r = slice2Combination (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold positiveSlice2 pairedMonomial slice2Combination
  norm_num only
  simp only [ite_false, ite_true, add_zero]
  rw [mono25_24_2_eval, mono26_23_2_eval, mono27_22_2_eval, mono28_21_2_eval, mono29_20_2_eval,
    mono30_19_2_eval, mono31_18_2_eval, mono32_10_9_eval, mono32_11_8_eval, mono32_12_7_eval,
    mono32_13_6_eval, mono32_14_5_eval, mono32_15_4_eval, mono32_16_3_eval, mono32_17_2_eval]

private def slice2NormalPart0 (e f g : ℝ) : ℝ :=
  -40593888*g^17
  +910000617*e^3*g^16
  +2312271216*e*f*g^16
  -5748228867*e^6*g^15
  -8305520757*e^4*f*g^15
  -33623412717*e^2*f^2*g^15
  +910000617*f^3*g^15
  -3703885683*e^9*g^14
  +40952917741*e^7*f*g^14
  +15230169951*e^5*f^2*g^14
  +215434255107*e^3*f^3*g^14
  -8305520757*e*f^4*g^14
  -510874540*e^12*g^13
  +24763356454*e^10*f*g^13
  -125928025833*e^8*f^2*g^13
  +65881547131*e^6*f^3*g^13
  -743569339294*e^4*f^4*g^13
  +15230169951*e^2*f^5*g^13
  -5748228867*f^6*g^13
  -15902778*e^15*g^12
  +4052683182*e^13*f*g^12
  -65308946671*e^11*f^2*g^12
  +228873210797*e^9*f^3*g^12
  -350996112755*e^7*f^4*g^12
  +1505585521774*e^5*f^5*g^12
  +65881547131*e^3*f^6*g^12
  +40952917741*e*f^7*g^12
  -16085064*e^18*g^11
  +327096912*e^16*f*g^11
  -9907220730*e^14*f^2*g^11

private def slice2NormalPart1 (e f g : ℝ) : ℝ :=
  90512613426*e^12*f^3*g^11
  -279665549064*e^10*f^4*g^11
  +689150431566*e^8*f^5*g^11
  -1820662884987*e^6*f^6*g^11
  -350996112755*e^4*f^7*g^11
  -125928025833*e^2*f^8*g^11
  -3703885683*f^9*g^11
  +746936*e^21*g^10
  +31322140*e^19*f*g^10
  -653903730*e^17*f^2*g^10
  +10803263046*e^15*f^3*g^10
  -72652344294*e^13*f^4*g^10
  +235344890946*e^11*f^5*g^10
  -702359672751*e^9*f^6*g^10
  +1235007417909*e^7*f^7*g^10
  +689150431566*e^5*f^8*g^10
  +228873210797*e^3*f^9*g^10
  +24763356454*e*f^10*g^10
  -394480*e^22*f*g^9
  -27517864*e^20*f^2*g^9
  +461705012*e^18*f^3*g^9
  -5731246880*e^16*f^4*g^9
  +34377967698*e^14*f^5*g^9
  -126183858918*e^12*f^6*g^9
  +367977230610*e^10*f^7*g^9
  -332934885129*e^8*f^8*g^9
  -702359672751*e^6*f^9*g^9
  -279665549064*e^4*f^10*g^9
  -65308946671*e^2*f^11*g^9
  -510874540*f^12*g^9

private def slice2NormalPart2 (e f g : ℝ) : ℝ :=
  8305944*e^21*f^3*g^8
  -105804486*e^19*f^4*g^8
  +1380249900*e^17*f^5*g^8
  -8836477758*e^15*f^6*g^8
  +34352425418*e^13*f^7*g^8
  -68379841605*e^11*f^8*g^8
  -95166529557*e^9*f^9*g^8
  +367977230610*e^7*f^10*g^8
  +235344890946*e^5*f^11*g^8
  +90512613426*e^3*f^12*g^8
  +4052683182*e*f^13*g^8
  -1881546*e^20*f^5*g^7
  -112933046*e^18*f^6*g^7
  +780093530*e^16*f^7*g^7
  -912832947*e^14*f^8*g^7
  -14684528365*e^12*f^9*g^7
  +78479011897*e^10*f^10*g^7
  -68379841605*e^8*f^11*g^7
  -126183858918*e^6*f^12*g^7
  -72652344294*e^4*f^13*g^7
  -9907220730*e^2*f^14*g^7
  -15902778*f^15*g^7
  +4591250*e^19*f^7*g^6
  +85325857*e^17*f^8*g^6
  -1116811583*e^15*f^9*g^6
  +5373688025*e^13*f^10*g^6
  -8889416839*e^11*f^11*g^6
  -14684528365*e^9*f^12*g^6
  +34352425418*e^7*f^13*g^6
  +34377967698*e^5*f^14*g^6

private def slice2NormalPart3 (e f g : ℝ) : ℝ :=
  10803263046*e^3*f^15*g^6
  +327096912*e*f^16*g^6
  -6249903*e^18*f^9*g^5
  +18589252*e^16*f^10*g^5
  +227213799*e^14*f^11*g^5
  -1981770726*e^12*f^12*g^5
  +5373688025*e^10*f^13*g^5
  -912832947*e^8*f^14*g^5
  -8836477758*e^6*f^15*g^5
  -5731246880*e^4*f^16*g^5
  -653903730*e^2*f^17*g^5
  -16085064*f^18*g^5
  +2897886*e^17*f^11*g^4
  -23031349*e^15*f^12*g^4
  +44073094*e^13*f^13*g^4
  +227213799*e^11*f^14*g^4
  -1116811583*e^9*f^15*g^4
  +780093530*e^7*f^16*g^4
  +1380249900*e^5*f^17*g^4
  +461705012*e^3*f^18*g^4
  +31322140*e*f^19*g^4
  -608077*e^16*f^13*g^3
  +6125279*e^14*f^14*g^3
  -23031349*e^12*f^15*g^3
  +18589252*e^10*f^16*g^3
  +85325857*e^8*f^17*g^3
  -112933046*e^6*f^18*g^3
  -105804486*e^4*f^19*g^3
  -27517864*e^2*f^20*g^3
  +746936*f^21*g^3

private def slice2NormalPart4 (e f g : ℝ) : ℝ :=
  52287*e^15*f^15*g^2
  -608077*e^13*f^16*g^2
  +2897886*e^11*f^17*g^2
  -6249903*e^9*f^18*g^2
  +4591250*e^7*f^19*g^2
  -1881546*e^5*f^20*g^2
  +8305944*e^3*f^21*g^2
  -394480*e*f^22*g^2

private def slice2Normal (e f g : ℝ) : ℝ :=
  slice2NormalPart0 e f g + slice2NormalPart1 e f g + slice2NormalPart2 e f g + slice2NormalPart3
      e f g + slice2NormalPart4 e f g

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
-- Normalize one small symmetric slice in the elementary variables.
private theorem slice2_normal (e f g : ℝ) :
    slice2Combination e f g = slice2Normal e f g := by
  unfold slice2Combination slice2Normal slice2NormalPart0 slice2NormalPart1 slice2NormalPart2
    slice2NormalPart3 slice2NormalPart4
  unfold mono25_24_2
  unfold mono26_23_2
  unfold mono27_22_2
  unfold mono28_21_2
  unfold mono29_20_2
  unfold mono30_19_2
  unfold mono31_18_2
  unfold mono32_10_9
  unfold mono32_11_8
  unfold mono32_12_7
  unfold mono32_13_6
  unfold mono32_14_5
  unfold mono32_15_4
  unfold mono32_16_3
  unfold mono32_17_2
  unfold newton0 newton0row0
  unfold newton1 newton1row0
  unfold newton3 newton3row0 newton3row1
  unfold newton5 newton5row0 newton5row1
  unfold newton6 newton6row0 newton6row1 newton6row2
  unfold newton7 newton7row0 newton7row1 newton7row2
  unfold newton9 newton9row0 newton9row1 newton9row2 newton9row3
  unfold newton11 newton11row0 newton11row1 newton11row2 newton11row3
  unfold newton12 newton12row0 newton12row1 newton12row2 newton12row3 newton12row4
  unfold newton13 newton13row0 newton13row1 newton13row2 newton13row3 newton13row4
  unfold newton15 newton15row0 newton15row1 newton15row2 newton15row3 newton15row4 newton15row5
  unfold newton16 newton16row0 newton16row1 newton16row2 newton16row3 newton16row4 newton16row5
  unfold newton17 newton17row0 newton17row1 newton17row2 newton17row3 newton17row4 newton17row5
  unfold newton18 newton18row0 newton18row1 newton18row2 newton18row3 newton18row4 newton18row5
    newton18row6
  unfold newton19 newton19row0 newton19row1 newton19row2 newton19row3 newton19row4 newton19row5
    newton19row6
  unfold newton20 newton20row0 newton20row1 newton20row2 newton20row3 newton20row4 newton20row5
    newton20row6
  unfold newton21 newton21row0 newton21row1 newton21row2 newton21row3 newton21row4 newton21row5
    newton21row6 newton21row7
  unfold newton22 newton22row0 newton22row1 newton22row2 newton22row3 newton22row4 newton22row5
    newton22row6 newton22row7
  ring

private theorem slice2_eval (p q r : ℝ) :
    positiveSlice2 p q r = slice2Normal (p+q+r) (p*q+q*r+r*p) (p*q*r) :=
  (slice2Combination_eval p q r).trans (slice2_normal _ _ _)

private def slice3Combination (e f g : ℝ) : ℝ :=
  108463952*(mono24_24_3 e f g + mono31_10_10 e f g) +
  80194388*(mono25_23_3 e f g + mono31_11_9 e f g) +
  51067648*(mono26_22_3 e f g + mono31_12_8 e f g) +
  49261680*(mono27_21_3 e f g + mono31_13_7 e f g) +
  31265484*(mono28_20_3 e f g + mono31_14_6 e f g) +
  8723280*(mono29_19_3 e f g + mono31_15_5 e f g) +
  1542588*(mono30_18_3 e f g + mono31_16_4 e f g) +
  605156*(mono31_17_3 e f g)

private theorem slice3Combination_eval (p q r : ℝ) :
    positiveSlice3 p q r = slice3Combination (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold positiveSlice3 pairedMonomial slice3Combination
  norm_num only
  simp only [ite_false, ite_true, add_zero]
  rw [mono24_24_3_eval, mono25_23_3_eval, mono26_22_3_eval, mono27_21_3_eval, mono28_20_3_eval,
    mono29_19_3_eval, mono30_18_3_eval, mono31_10_10_eval, mono31_11_9_eval, mono31_12_8_eval,
    mono31_13_7_eval, mono31_14_6_eval, mono31_15_5_eval, mono31_16_4_eval, mono31_17_3_eval]

private def slice3NormalPart0 (e f g : ℝ) : ℝ :=
  231114660*g^17
  -6949038700*e^3*g^16
  -11284929400*e*f*g^16
  +22444238036*e^6*g^15
  +67854832784*e^4*f*g^15
  +143245990188*e^2*f^2*g^15
  -6949038700*f^3*g^15
  +10195493820*e^9*g^14
  -123875406280*e^7*f*g^14
  -220931621496*e^5*f^2*g^14
  -813917562624*e^3*f^3*g^14
  +67854832784*e*f^4*g^14
  -921062492*e^12*g^13
  -57148215488*e^10*f*g^13
  +278312048496*e^8*f^2*g^13
  +212492052184*e^6*f^3*g^13
  +2522826335716*e^4*f^4*g^13
  -220931621496*e^2*f^5*g^13
  +22444238036*f^6*g^13
  -710967400*e^15*g^12
  -773427900*e^13*f*g^12
  +121524664520*e^11*f^2*g^12
  -359496368280*e^9*f^3*g^12
  +382644953316*e^7*f^4*g^12
  -4631507976248*e^5*f^5*g^12
  +212492052184*e^3*f^6*g^12
  -123875406280*e*f^7*g^12
  +23392092*e^18*g^11
  +1028000584*e^16*f*g^11
  +7220203352*e^14*f^2*g^11

private def slice3NormalPart1 (e f g : ℝ) : ℝ :=
  -132687960748*e^12*f^3*g^11
  +344929534096*e^10*f^4*g^11
  -1229142940536*e^8*f^5*g^11
  +5117354118012*e^6*f^6*g^11
  +382644953316*e^4*f^7*g^11
  +278312048496*e^2*f^8*g^11
  +10195493820*f^9*g^11
  -1353616*e^21*g^10
  -17178180*e^19*f*g^10
  -442852668*e^17*f^2*g^10
  -8883271544*e^15*f^3*g^10
  +84024179120*e^13*f^4*g^10
  -277278583428*e^11*f^5*g^10
  +1347492654172*e^9*f^6*g^10
  -3208261704096*e^7*f^7*g^10
  -1229142940536*e^5*f^8*g^10
  -359496368280*e^3*f^9*g^10
  -57148215488*e*f^10*g^10
  +11232648*e^20*f^2*g^9
  +39291712*e^18*f^3*g^9
  +4421122532*e^16*f^4*g^9
  -33215161380*e^14*f^5*g^9
  +155189386604*e^12*f^6*g^9
  -687188856968*e^10*f^7*g^9
  +857172651408*e^8*f^8*g^9
  +1347492654172*e^6*f^9*g^9
  +344929534096*e^4*f^10*g^9
  +121524664520*e^2*f^11*g^9
  -921062492*f^12*g^9
  -11995588*e^19*f^4*g^8

private def slice3NormalPart2 (e f g : ℝ) : ℝ :=
  -1012773788*e^17*f^5*g^8
  +7726969600*e^15*f^6*g^8
  -41523654868*e^13*f^7*g^8
  +121175598764*e^11*f^8*g^8
  +124080549208*e^9*f^9*g^8
  -687188856968*e^7*f^10*g^8
  -277278583428*e^5*f^11*g^8
  -132687960748*e^3*f^12*g^8
  -773427900*e*f^13*g^8
  +109598616*e^18*f^6*g^7
  -480607896*e^16*f^7*g^7
  +457068300*e^14*f^8*g^7
  +17360699116*e^12*f^9*g^7
  -109697858776*e^10*f^10*g^7
  +121175598764*e^8*f^11*g^7
  +155189386604*e^6*f^12*g^7
  +84024179120*e^4*f^13*g^7
  +7220203352*e^2*f^14*g^7
  -710967400*f^15*g^7
  -99750324*e^17*f^8*g^6
  +903451448*e^15*f^9*g^6
  -4451889896*e^13*f^10*g^6
  +7808065600*e^11*f^11*g^6
  +17360699116*e^9*f^12*g^6
  -41523654868*e^7*f^13*g^6
  -33215161380*e^5*f^14*g^6
  -8883271544*e^3*f^15*g^6
  +1028000584*e*f^16*g^6
  +36809236*e^16*f^10*g^5
  -366959704*e^14*f^11*g^5

private def slice3NormalPart3 (e f g : ℝ) : ℝ :=
  1879478572*e^12*f^12*g^5
  -4451889896*e^10*f^13*g^5
  +457068300*e^8*f^14*g^5
  +7726969600*e^6*f^15*g^5
  +4421122532*e^4*f^16*g^5
  -442852668*e^2*f^17*g^5
  +23392092*f^18*g^5
  -6929596*e^15*f^12*g^4
  +72332936*e^13*f^13*g^4
  -366959704*e^11*f^14*g^4
  +903451448*e^9*f^15*g^4
  -480607896*e^7*f^16*g^4
  -1012773788*e^5*f^17*g^4
  +39291712*e^3*f^18*g^4
  -17178180*e*f^19*g^4
  +605156*e^14*f^14*g^3
  -6929596*e^12*f^15*g^3
  +36809236*e^10*f^16*g^3
  -99750324*e^8*f^17*g^3
  +109598616*e^6*f^18*g^3
  -11995588*e^4*f^19*g^3
  +11232648*e^2*f^20*g^3
  -1353616*f^21*g^3

private def slice3Normal (e f g : ℝ) : ℝ :=
  slice3NormalPart0 e f g + slice3NormalPart1 e f g + slice3NormalPart2 e f g + slice3NormalPart3
      e f g

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
-- Normalize one small symmetric slice in the elementary variables.
private theorem slice3_normal (e f g : ℝ) :
    slice3Combination e f g = slice3Normal e f g := by
  unfold slice3Combination slice3Normal slice3NormalPart0 slice3NormalPart1 slice3NormalPart2
    slice3NormalPart3
  unfold mono24_24_3
  unfold mono25_23_3
  unfold mono26_22_3
  unfold mono27_21_3
  unfold mono28_20_3
  unfold mono29_19_3
  unfold mono30_18_3
  unfold mono31_10_10
  unfold mono31_11_9
  unfold mono31_12_8
  unfold mono31_13_7
  unfold mono31_14_6
  unfold mono31_15_5
  unfold mono31_16_4
  unfold mono31_17_3
  unfold newton0 newton0row0
  unfold newton2 newton2row0
  unfold newton3 newton3row0 newton3row1
  unfold newton4 newton4row0 newton4row1
  unfold newton6 newton6row0 newton6row1 newton6row2
  unfold newton8 newton8row0 newton8row1 newton8row2
  unfold newton9 newton9row0 newton9row1 newton9row2 newton9row3
  unfold newton10 newton10row0 newton10row1 newton10row2 newton10row3
  unfold newton12 newton12row0 newton12row1 newton12row2 newton12row3 newton12row4
  unfold newton14 newton14row0 newton14row1 newton14row2 newton14row3 newton14row4
  unfold newton15 newton15row0 newton15row1 newton15row2 newton15row3 newton15row4 newton15row5
  unfold newton16 newton16row0 newton16row1 newton16row2 newton16row3 newton16row4 newton16row5
  unfold newton17 newton17row0 newton17row1 newton17row2 newton17row3 newton17row4 newton17row5
  unfold newton18 newton18row0 newton18row1 newton18row2 newton18row3 newton18row4 newton18row5
    newton18row6
  unfold newton19 newton19row0 newton19row1 newton19row2 newton19row3 newton19row4 newton19row5
    newton19row6
  unfold newton20 newton20row0 newton20row1 newton20row2 newton20row3 newton20row4 newton20row5
    newton20row6
  unfold newton21 newton21row0 newton21row1 newton21row2 newton21row3 newton21row4 newton21row5
    newton21row6 newton21row7
  ring

private theorem slice3_eval (p q r : ℝ) :
    positiveSlice3 p q r = slice3Normal (p+q+r) (p*q+q*r+r*p) (p*q*r) :=
  (slice3Combination_eval p q r).trans (slice3_normal _ _ _)

private def slice4Combination (e f g : ℝ) : ℝ :=
  574395548*(mono24_23_4 e f g + mono30_11_10 e f g) +
  370828650*(mono25_22_4 e f g + mono30_12_9 e f g) +
  269255764*(mono26_21_4 e f g + mono30_13_8 e f g) +
  214543632*(mono27_20_4 e f g + mono30_14_7 e f g) +
  96992592*(mono28_19_4 e f g + mono30_15_6 e f g) +
  16927212*(mono29_18_4 e f g + mono30_16_5 e f g) +
  1931150*(mono30_17_4 e f g)

private theorem slice4Combination_eval (p q r : ℝ) :
    positiveSlice4 p q r = slice4Combination (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold positiveSlice4 pairedMonomial slice4Combination
  norm_num only
  simp only [ite_false, ite_true, add_zero]
  rw [mono24_23_4_eval, mono25_22_4_eval, mono26_21_4_eval, mono27_20_4_eval, mono28_19_4_eval,
    mono29_18_4_eval, mono30_11_10_eval, mono30_12_9_eval, mono30_13_8_eval, mono30_14_7_eval,
    mono30_15_6_eval, mono30_16_5_eval, mono30_17_4_eval]

private def slice4NormalPart0 (e f g : ℝ) : ℝ :=
  -842671482*g^17
  +28679247068*e^3*g^16
  +34423913534*e*f*g^16
  -64767264834*e^6*g^15
  -262489640062*e^4*f*g^15
  -373070618068*e^2*f^2*g^15
  +28679247068*f^3*g^15
  -29803761198*e^9*g^14
  +287324854730*e^7*f*g^14
  +884296196532*e^5*f^2*g^14
  +1844076315996*e^3*f^3*g^14
  -262489640062*e*f^4*g^14
  +122716004*e^12*g^13
  +138164331676*e^10*f*g^13
  -454666136118*e^8*f^2*g^13
  -1343427987090*e^6*f^3*g^13
  -5053686487430*e^4*f^4*g^13
  +884296196532*e^2*f^5*g^13
  -64767264834*f^6*g^13
  +1902390052*e^15*g^12
  +5283535968*e^13*f*g^12
  -226399810222*e^11*f^2*g^12
  +280728677054*e^9*f^3*g^12
  +635840892024*e^7*f^4*g^12
  +8319035711178*e^5*f^5*g^12
  -1343427987090*e^3*f^6*g^12
  +287324854730*e*f^7*g^12
  -52076364*e^18*g^11
  -2209229460*e^16*f*g^11
  -14511277220*e^14*f^2*g^11

private def slice4NormalPart1 (e f g : ℝ) : ℝ :=
  167805346864*e^12*f^3*g^11
  -34884489872*e^10*f^4*g^11
  +801472544868*e^8*f^5*g^11
  -8358358058040*e^6*f^6*g^11
  +635840892024*e^4*f^7*g^11
  -454666136118*e^2*f^8*g^11
  -29803761198*f^9*g^11
  +18221940*e^19*f*g^10
  +862281744*e^17*f^2*g^10
  +11144007404*e^15*f^3*g^10
  -54620084200*e^13*f^4*g^10
  +20180470584*e^11*f^5*g^10
  -1329488968056*e^9*f^6*g^10
  +4865812941192*e^7*f^7*g^10
  +801472544868*e^5*f^8*g^10
  +280728677054*e^3*f^9*g^10
  +138164331676*e*f^10*g^10
  -126355072*e^18*f^3*g^9
  -3214963756*e^16*f^4*g^9
  +7120570340*e^14*f^5*g^9
  -58477346532*e^12*f^6*g^9
  +726333183772*e^10*f^7*g^9
  -1308972765522*e^8*f^8*g^9
  -1329488968056*e^6*f^9*g^9
  -34884489872*e^4*f^10*g^9
  -226399810222*e^2*f^11*g^9
  +122716004*f^12*g^9
  +434324300*e^17*f^5*g^8
  -902950396*e^15*f^6*g^8
  +24430353772*e^13*f^7*g^8

private def slice4NormalPart2 (e f g : ℝ) : ℝ :=
  -134247453614*e^11*f^8*g^8
  -48053518330*e^9*f^9*g^8
  +726333183772*e^7*f^10*g^8
  +20180470584*e^5*f^11*g^8
  +167805346864*e^3*f^12*g^8
  +5283535968*e*f^13*g^8
  -214851768*e^16*f^7*g^7
  -443948322*e^14*f^8*g^7
  -7614432812*e^12*f^9*g^7
  +83012729690*e^10*f^10*g^7
  -134247453614*e^8*f^11*g^7
  -58477346532*e^6*f^12*g^7
  -54620084200*e^4*f^13*g^7
  -14511277220*e^2*f^14*g^7
  +1902390052*f^15*g^7
  +36318010*e^15*f^9*g^6
  +848580292*e^13*f^10*g^6
  -3235688582*e^11*f^11*g^6
  -7614432812*e^9*f^12*g^6
  +24430353772*e^7*f^13*g^6
  +7120570340*e^5*f^14*g^6
  +11144007404*e^3*f^15*g^6
  -2209229460*e*f^16*g^6
  -8177738*e^14*f^11*g^5
  -147597586*e^12*f^12*g^5
  +848580292*e^10*f^13*g^5
  -443948322*e^8*f^14*g^5
  -902950396*e^6*f^15*g^5
  -3214963756*e^4*f^16*g^5
  +862281744*e^2*f^17*g^5

private def slice4NormalPart3 (e f g : ℝ) : ℝ :=
  -52076364*f^18*g^5
  +1931150*e^13*f^13*g^4
  -8177738*e^11*f^14*g^4
  +36318010*e^9*f^15*g^4
  -214851768*e^7*f^16*g^4
  +434324300*e^5*f^17*g^4
  -126355072*e^3*f^18*g^4
  +18221940*e*f^19*g^4

private def slice4Normal (e f g : ℝ) : ℝ :=
  slice4NormalPart0 e f g + slice4NormalPart1 e f g + slice4NormalPart2 e f g + slice4NormalPart3
      e f g

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
-- Normalize one small symmetric slice in the elementary variables.
private theorem slice4_normal (e f g : ℝ) :
    slice4Combination e f g = slice4Normal e f g := by
  unfold slice4Combination slice4Normal slice4NormalPart0 slice4NormalPart1 slice4NormalPart2
    slice4NormalPart3
  unfold mono24_23_4
  unfold mono25_22_4
  unfold mono26_21_4
  unfold mono27_20_4
  unfold mono28_19_4
  unfold mono29_18_4
  unfold mono30_11_10
  unfold mono30_12_9
  unfold mono30_13_8
  unfold mono30_14_7
  unfold mono30_15_6
  unfold mono30_16_5
  unfold mono30_17_4
  unfold newton0 newton0row0
  unfold newton1 newton1row0
  unfold newton3 newton3row0 newton3row1
  unfold newton5 newton5row0 newton5row1
  unfold newton6 newton6row0 newton6row1 newton6row2
  unfold newton7 newton7row0 newton7row1 newton7row2
  unfold newton9 newton9row0 newton9row1 newton9row2 newton9row3
  unfold newton11 newton11row0 newton11row1 newton11row2 newton11row3
  unfold newton12 newton12row0 newton12row1 newton12row2 newton12row3 newton12row4
  unfold newton13 newton13row0 newton13row1 newton13row2 newton13row3 newton13row4
  unfold newton14 newton14row0 newton14row1 newton14row2 newton14row3 newton14row4
  unfold newton15 newton15row0 newton15row1 newton15row2 newton15row3 newton15row4 newton15row5
  unfold newton16 newton16row0 newton16row1 newton16row2 newton16row3 newton16row4 newton16row5
  unfold newton17 newton17row0 newton17row1 newton17row2 newton17row3 newton17row4 newton17row5
  unfold newton18 newton18row0 newton18row1 newton18row2 newton18row3 newton18row4 newton18row5
    newton18row6
  unfold newton19 newton19row0 newton19row1 newton19row2 newton19row3 newton19row4 newton19row5
    newton19row6
  ring

private theorem slice4_eval (p q r : ℝ) :
    positiveSlice4 p q r = slice4Normal (p+q+r) (p*q+q*r+r*p) (p*q*r) :=
  (slice4Combination_eval p q r).trans (slice4_normal _ _ _)

private def slice5Combination (e f g : ℝ) : ℝ :=
  2642231280*(mono23_23_5 e f g + mono29_11_11 e f g) +
  2118372260*(mono24_22_5 e f g + mono29_12_10 e f g) +
  1371798086*(mono25_21_5 e f g + mono29_13_9 e f g) +
  1021378314*(mono26_20_5 e f g + mono29_14_8 e f g) +
  651096776*(mono27_19_5 e f g + mono29_15_7 e f g) +
  233668828*(mono28_18_5 e f g + mono29_16_6 e f g) +
  45686550*(mono29_17_5 e f g)

private theorem slice5Combination_eval (p q r : ℝ) :
    positiveSlice5 p q r = slice5Combination (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold positiveSlice5 pairedMonomial slice5Combination
  norm_num only
  simp only [ite_false, ite_true, add_zero]
  rw [mono23_23_5_eval, mono24_22_5_eval, mono25_21_5_eval, mono26_20_5_eval, mono27_19_5_eval,
    mono28_18_5_eval, mono29_11_11_eval, mono29_12_10_eval, mono29_13_9_eval, mono29_14_8_eval,
    mono29_15_7_eval, mono29_16_6_eval, mono29_17_5_eval]

private def slice5NormalPart0 (e f g : ℝ) : ℝ :=
  2134431048*g^17
  -74838448172*e^3*g^16
  -69168901192*e*f*g^16
  +173450841670*e^6*g^15
  +604185693204*e^4*f*g^15
  +603872621956*e^2*f^2*g^15
  -74838448172*f^3*g^15
  +83458145412*e^9*g^14
  -720345598234*e^7*f*g^14
  -1945384302182*e^5*f^2*g^14
  -2445713264092*e^3*f^3*g^14
  +604185693204*e*f^4*g^14
  +5367250076*e^12*g^13
  -350481172920*e^10*f*g^13
  +1046077104156*e^8*f^2*g^13
  +3362806602574*e^6*f^3*g^13
  +5634934298320*e^4*f^4*g^13
  -1945384302182*e^2*f^5*g^13
  +173450841670*f^6*g^13
  -4150851690*e^15*g^12
  -24281621348*e^13*f*g^12
  +503853144788*e^11*f^2*g^12
  -394788863892*e^9*f^3*g^12
  -3361815004072*e^7*f^4*g^12
  -8185875164432*e^5*f^5*g^12
  +3362806602574*e^3*f^6*g^12
  -720345598234*e*f^7*g^12
  +32555300*e^18*g^11
  +3245616912*e^16*f*g^11
  +40310861850*e^14*f^2*g^11

private def slice5NormalPart1 (e f g : ℝ) : ℝ :=
  -287596360254*e^12*f^3*g^11
  -471029974986*e^10*f^4*g^11
  +1669634399884*e^8*f^5*g^11
  +7912437272264*e^6*f^6*g^11
  -3361815004072*e^4*f^7*g^11
  +1046077104156*e^2*f^8*g^11
  +83458145412*f^9*g^11
  -396958774*e^17*f^2*g^10
  -20032004478*e^15*f^3*g^10
  +19390412300*e^13*f^4*g^10
  +489367175622*e^11*f^5*g^10
  +103532954814*e^9*f^6*g^10
  -5037870053208*e^7*f^7*g^10
  +1669634399884*e^5*f^8*g^10
  -394788863892*e^3*f^9*g^10
  -350481172920*e*f^10*g^10
  +1379110072*e^16*f^4*g^9
  +27217248628*e^14*f^5*g^9
  -94952583334*e^12*f^6*g^9
  -543686749598*e^10*f^7*g^9
  +1813648176642*e^8*f^8*g^9
  +103532954814*e^6*f^9*g^9
  -471029974986*e^4*f^10*g^9
  +503853144788*e^2*f^11*g^9
  +5367250076*f^12*g^9
  -1125880514*e^15*f^6*g^8
  -25815987026*e^13*f^7*g^8
  +177183808972*e^11*f^8*g^8
  -151496274460*e^9*f^9*g^8
  -543686749598*e^7*f^10*g^8

private def slice5NormalPart2 (e f g : ℝ) : ℝ :=
  489367175622*e^5*f^11*g^8
  -287596360254*e^3*f^12*g^8
  -24281621348*e*f^13*g^8
  +781482196*e^14*f^8*g^7
  +7393420796*e^12*f^9*g^7
  -77360929968*e^10*f^10*g^7
  +177183808972*e^8*f^11*g^7
  -94952583334*e^6*f^12*g^7
  +19390412300*e^4*f^13*g^7
  +40310861850*e^2*f^14*g^7
  -4150851690*f^15*g^7
  -314569772*e^13*f^10*g^6
  +503473672*e^11*f^11*g^6
  +7393420796*e^9*f^12*g^6
  -25815987026*e^7*f^13*g^6
  +27217248628*e^5*f^14*g^6
  -20032004478*e^3*f^15*g^6
  +3245616912*e*f^16*g^6
  +45686550*e^12*f^12*g^5
  -314569772*e^10*f^13*g^5
  +781482196*e^8*f^14*g^5
  -1125880514*e^6*f^15*g^5
  +1379110072*e^4*f^16*g^5
  -396958774*e^2*f^17*g^5
  +32555300*f^18*g^5

private def slice5Normal (e f g : ℝ) : ℝ :=
  slice5NormalPart0 e f g + slice5NormalPart1 e f g + slice5NormalPart2 e f g

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
-- Normalize one small symmetric slice in the elementary variables.
private theorem slice5_normal (e f g : ℝ) :
    slice5Combination e f g = slice5Normal e f g := by
  unfold slice5Combination slice5Normal slice5NormalPart0 slice5NormalPart1 slice5NormalPart2
  unfold mono23_23_5
  unfold mono24_22_5
  unfold mono25_21_5
  unfold mono26_20_5
  unfold mono27_19_5
  unfold mono28_18_5
  unfold mono29_11_11
  unfold mono29_12_10
  unfold mono29_13_9
  unfold mono29_14_8
  unfold mono29_15_7
  unfold mono29_16_6
  unfold mono29_17_5
  unfold newton0 newton0row0
  unfold newton2 newton2row0
  unfold newton3 newton3row0 newton3row1
  unfold newton4 newton4row0 newton4row1
  unfold newton6 newton6row0 newton6row1 newton6row2
  unfold newton8 newton8row0 newton8row1 newton8row2
  unfold newton9 newton9row0 newton9row1 newton9row2 newton9row3
  unfold newton10 newton10row0 newton10row1 newton10row2 newton10row3
  unfold newton12 newton12row0 newton12row1 newton12row2 newton12row3 newton12row4
  unfold newton13 newton13row0 newton13row1 newton13row2 newton13row3 newton13row4
  unfold newton14 newton14row0 newton14row1 newton14row2 newton14row3 newton14row4
  unfold newton15 newton15row0 newton15row1 newton15row2 newton15row3 newton15row4 newton15row5
  unfold newton16 newton16row0 newton16row1 newton16row2 newton16row3 newton16row4 newton16row5
  unfold newton17 newton17row0 newton17row1 newton17row2 newton17row3 newton17row4 newton17row5
  unfold newton18 newton18row0 newton18row1 newton18row2 newton18row3 newton18row4 newton18row5
    newton18row6
  ring

private theorem slice5_eval (p q r : ℝ) :
    positiveSlice5 p q r = slice5Normal (p+q+r) (p*q+q*r+r*p) (p*q*r) :=
  (slice5Combination_eval p q r).trans (slice5_normal _ _ _)

private def slice6Combination (e f g : ℝ) : ℝ :=
  8794276088*(mono23_22_6 e f g + mono28_12_11 e f g) +
  6430027040*(mono24_21_6 e f g + mono28_13_10 e f g) +
  4523886771*(mono25_20_6 e f g + mono28_14_9 e f g) +
  3269762208*(mono26_19_6 e f g + mono28_15_8 e f g) +
  1814014164*(mono27_18_6 e f g + mono28_16_7 e f g) +
  686861745*(mono28_17_6 e f g)

private theorem slice6Combination_eval (p q r : ℝ) :
    positiveSlice6 p q r = slice6Combination (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold positiveSlice6 pairedMonomial slice6Combination
  norm_num only
  simp only [ite_false, ite_true, add_zero]
  rw [mono23_22_6_eval, mono24_21_6_eval, mono25_20_6_eval, mono26_19_6_eval, mono27_18_6_eval,
    mono28_12_11_eval, mono28_13_10_eval, mono28_14_9_eval, mono28_15_8_eval, mono28_16_7_eval,
    mono28_17_6_eval]

private def slice6NormalPart0 (e f g : ℝ) : ℝ :=
  -2659641189*g^17
  +229091117764*e^3*g^16
  +37481219887*e*f*g^16
  -378132576219*e^6*g^15
  -1844765978457*e^4*f*g^15
  -89331818574*e^2*f^2*g^15
  +229091117764*f^3*g^15
  -289980948299*e^9*g^14
  +1229863038395*e^7*f*g^14
  +6261597316592*e^5*f^2*g^14
  +208452592522*e^3*f^3*g^14
  -1844765978457*e*f^4*g^14
  -45472127102*e^12*g^13
  +904157488100*e^10*f*g^13
  -744193014311*e^8*f^2*g^13
  -11526126509891*e^6*f^3*g^13
  -1946257083683*e^4*f^4*g^13
  +6261597316592*e^2*f^5*g^13
  -378132576219*f^6*g^13
  +5622086680*e^15*g^12
  +95712400136*e^13*f*g^12
  -844517587737*e^11*f^2*g^12
  -1576989426605*e^9*f^3*g^12
  +11547080881980*e^7*f^4*g^12
  +6998404895181*e^5*f^5*g^12
  -11526126509891*e^3*f^6*g^12
  +1229863038395*e*f^7*g^12
  -1994058352*e^16*f*g^11
  -72232281728*e^14*f^2*g^11
  +162523957684*e^12*f^3*g^11

private def slice6NormalPart1 (e f g : ℝ) : ℝ :=
  2347149508894*e^10*f^4*g^11
  -4972429708506*e^8*f^5*g^11
  -10994161383828*e^6*f^6*g^11
  +11547080881980*e^4*f^7*g^11
  -744193014311*e^2*f^8*g^11
  -289980948299*f^9*g^11
  +12944235152*e^15*f^3*g^10
  +107680063050*e^13*f^4*g^10
  -896236577502*e^11*f^5*g^10
  -496177291288*e^9*f^6*g^10
  +7973486433804*e^7*f^7*g^10
  -4972429708506*e^5*f^8*g^10
  -1576989426605*e^3*f^9*g^10
  +904157488100*e*f^10*g^10
  -22274420622*e^14*f^5*g^9
  -11486558244*e^12*f^6*g^9
  +887533380774*e^10*f^7*g^9
  -2095977186162*e^8*f^8*g^9
  -496177291288*e^6*f^9*g^9
  +2347149508894*e^4*f^10*g^9
  -844517587737*e^2*f^11*g^9
  -45472127102*f^12*g^9
  +17165551512*e^13*f^7*g^8
  -73522219521*e^11*f^8*g^8
  -131072544402*e^9*f^9*g^8
  +887533380774*e^7*f^10*g^8
  -896236577502*e^5*f^11*g^8
  +162523957684*e^3*f^12*g^8
  +95712400136*e*f^13*g^8
  -5741465031*e^12*f^9*g^7

private def slice6NormalPart2 (e f g : ℝ) : ℝ :=
  39573931209*e^10*f^10*g^7
  -73522219521*e^8*f^11*g^7
  -11486558244*e^6*f^12*g^7
  +107680063050*e^4*f^13*g^7
  -72232281728*e^2*f^14*g^7
  +5622086680*f^15*g^7
  +686861745*e^11*f^11*g^6
  -5741465031*e^9*f^12*g^6
  +17165551512*e^7*f^13*g^6
  -22274420622*e^5*f^14*g^6
  +12944235152*e^3*f^15*g^6
  -1994058352*e*f^16*g^6

private def slice6Normal (e f g : ℝ) : ℝ :=
  slice6NormalPart0 e f g + slice6NormalPart1 e f g + slice6NormalPart2 e f g

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
-- Normalize one small symmetric slice in the elementary variables.
private theorem slice6_normal (e f g : ℝ) :
    slice6Combination e f g = slice6Normal e f g := by
  unfold slice6Combination slice6Normal slice6NormalPart0 slice6NormalPart1 slice6NormalPart2
  unfold mono23_22_6
  unfold mono24_21_6
  unfold mono25_20_6
  unfold mono26_19_6
  unfold mono27_18_6
  unfold mono28_12_11
  unfold mono28_13_10
  unfold mono28_14_9
  unfold mono28_15_8
  unfold mono28_16_7
  unfold mono28_17_6
  unfold newton0 newton0row0
  unfold newton1 newton1row0
  unfold newton3 newton3row0 newton3row1
  unfold newton5 newton5row0 newton5row1
  unfold newton6 newton6row0 newton6row1 newton6row2
  unfold newton7 newton7row0 newton7row1 newton7row2
  unfold newton9 newton9row0 newton9row1 newton9row2 newton9row3
  unfold newton11 newton11row0 newton11row1 newton11row2 newton11row3
  unfold newton12 newton12row0 newton12row1 newton12row2 newton12row3 newton12row4
  unfold newton13 newton13row0 newton13row1 newton13row2 newton13row3 newton13row4
  unfold newton14 newton14row0 newton14row1 newton14row2 newton14row3 newton14row4
  unfold newton15 newton15row0 newton15row1 newton15row2 newton15row3 newton15row4 newton15row5
  unfold newton16 newton16row0 newton16row1 newton16row2 newton16row3 newton16row4 newton16row5
  ring

private theorem slice6_eval (p q r : ℝ) :
    positiveSlice6 p q r = slice6Normal (p+q+r) (p*q+q*r+r*p) (p*q*r) :=
  (slice6Combination_eval p q r).trans (slice6_normal _ _ _)

private def slice7Combination (e f g : ℝ) : ℝ :=
  26247468288*(mono22_22_7 e f g + mono27_12_12 e f g) +
  22940308472*(mono23_21_7 e f g + mono27_13_11 e f g) +
  17275128516*(mono24_20_7 e f g + mono27_14_10 e f g) +
  13210829476*(mono25_19_7 e f g + mono27_15_9 e f g) +
  8981170920*(mono26_18_7 e f g + mono27_16_8 e f g) +
  4594212780*(mono27_17_7 e f g)

private theorem slice7Combination_eval (p q r : ℝ) :
    positiveSlice7 p q r = slice7Combination (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold positiveSlice7 pairedMonomial slice7Combination
  norm_num only
  simp only [ite_false, ite_true, add_zero]
  rw [mono22_22_7_eval, mono23_21_7_eval, mono24_20_7_eval, mono25_19_7_eval, mono26_18_7_eval,
    mono27_12_12_eval, mono27_13_11_eval, mono27_14_10_eval, mono27_15_9_eval, mono27_16_8_eval,
    mono27_17_7_eval]

private def slice7NormalPart0 (e f g : ℝ) : ℝ :=
  7052477652*g^17
  -893797036188*e^3*g^16
  -65567368424*e*f*g^16
  -131983640960*e^6*g^15
  +6518500854684*e^4*f*g^15
  +290299021180*e^2*f^2*g^15
  -893797036188*f^3*g^15
  +472414412000*e^9*g^14
  +1789099398580*e^7*f*g^14
  -17949896412620*e^5*f^2*g^14
  -3116972205808*e^3*f^3*g^14
  +6518500854684*e*f^4*g^14
  +128148869104*e^12*g^13
  -898335470980*e^10*f*g^13
  -5494172584420*e^8*f^2*g^13
  +23161653785400*e^6*f^3*g^13
  +13917317699140*e^4*f^4*g^13
  -17949896412620*e^2*f^5*g^13
  -131983640960*f^6*g^13
  -2730634296*e^15*g^12
  -145621054624*e^13*f*g^12
  +164358657224*e^11*f^2*g^12
  +6635456703220*e^9*f^3*g^12
  -12346536409700*e^7*f^4*g^12
  -26219277867272*e^5*f^5*g^12
  +23161653785400*e^3*f^6*g^12
  +1789099398580*e*f^7*g^12
  +43893844472*e^14*f^2*g^11
  +327758853752*e^12*f^3*g^11
  -3007176447776*e^10*f^4*g^11

private def slice7NormalPart1 (e f g : ℝ) : ℝ :=
  -954054631452*e^8*f^5*g^11
  +22715392344204*e^6*f^6*g^11
  -12346536409700*e^4*f^7*g^11
  -5494172584420*e^2*f^8*g^11
  +472414412000*f^9*g^11
  -112077068940*e^13*f^4*g^10
  +152498278884*e^11*f^5*g^10
  +3009716885276*e^9*f^6*g^10
  -7796164521120*e^7*f^7*g^10
  -954054631452*e^5*f^8*g^10
  +6635456703220*e^3*f^9*g^10
  -898335470980*e*f^10*g^10
  +102158909416*e^12*f^6*g^9
  -535047737472*e^10*f^7*g^9
  +10679115468*e^8*f^8*g^9
  +3009716885276*e^6*f^9*g^9
  -3007176447776*e^4*f^10*g^9
  +164358657224*e^2*f^11*g^9
  +128148869104*f^12*g^9
  -36960956880*e^11*f^8*g^8
  +261835517760*e^9*f^9*g^8
  -535047737472*e^7*f^10*g^8
  +152498278884*e^5*f^11*g^8
  +327758853752*e^3*f^12*g^8
  -145621054624*e*f^13*g^8
  +4594212780*e^10*f^10*g^7
  -36960956880*e^8*f^11*g^7
  +102158909416*e^6*f^12*g^7
  -112077068940*e^4*f^13*g^7
  +43893844472*e^2*f^14*g^7

private def slice7NormalPart2 (e f g : ℝ) : ℝ :=
  -2730634296*f^15*g^7

private def slice7Normal (e f g : ℝ) : ℝ :=
  slice7NormalPart0 e f g + slice7NormalPart1 e f g + slice7NormalPart2 e f g

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
-- Normalize one small symmetric slice in the elementary variables.
private theorem slice7_normal (e f g : ℝ) :
    slice7Combination e f g = slice7Normal e f g := by
  unfold slice7Combination slice7Normal slice7NormalPart0 slice7NormalPart1 slice7NormalPart2
  unfold mono22_22_7
  unfold mono23_21_7
  unfold mono24_20_7
  unfold mono25_19_7
  unfold mono26_18_7
  unfold mono27_12_12
  unfold mono27_13_11
  unfold mono27_14_10
  unfold mono27_15_9
  unfold mono27_16_8
  unfold mono27_17_7
  unfold newton0 newton0row0
  unfold newton2 newton2row0
  unfold newton3 newton3row0 newton3row1
  unfold newton4 newton4row0 newton4row1
  unfold newton6 newton6row0 newton6row1 newton6row2
  unfold newton8 newton8row0 newton8row1 newton8row2
  unfold newton9 newton9row0 newton9row1 newton9row2 newton9row3
  unfold newton10 newton10row0 newton10row1 newton10row2 newton10row3
  unfold newton11 newton11row0 newton11row1 newton11row2 newton11row3
  unfold newton12 newton12row0 newton12row1 newton12row2 newton12row3 newton12row4
  unfold newton13 newton13row0 newton13row1 newton13row2 newton13row3 newton13row4
  unfold newton14 newton14row0 newton14row1 newton14row2 newton14row3 newton14row4
  unfold newton15 newton15row0 newton15row1 newton15row2 newton15row3 newton15row4 newton15row5
  ring

private theorem slice7_eval (p q r : ℝ) :
    positiveSlice7 p q r = slice7Normal (p+q+r) (p*q+q*r+r*p) (p*q*r) :=
  (slice7Combination_eval p q r).trans (slice7_normal _ _ _)

private def slice8Combination (e f g : ℝ) : ℝ :=
  60937077274*(mono22_21_8 e f g + mono26_13_12 e f g) +
  51524731584*(mono23_20_8 e f g + mono26_14_11 e f g) +
  41890112880*(mono24_19_8 e f g + mono26_15_10 e f g) +
  32043272883*(mono25_18_8 e f g + mono26_16_9 e f g) +
  19586982069*(mono26_17_8 e f g)

private theorem slice8Combination_eval (p q r : ℝ) :
    positiveSlice8 p q r = slice8Combination (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold positiveSlice8 pairedMonomial slice8Combination
  norm_num only
  simp only [ite_false, ite_true, add_zero]
  rw [mono22_21_8_eval, mono23_20_8_eval, mono24_19_8_eval, mono25_18_8_eval, mono26_13_12_eval,
    mono26_14_11_eval, mono26_15_10_eval, mono26_16_9_eval, mono26_17_8_eval]

private def slice8NormalPart0 (e f g : ℝ) : ℝ :=
  -73404106800*g^17
  +1798358420053*e^3*g^16
  +1568592939920*e*f*g^16
  +2396209258401*e^6*g^15
  -10357675514669*e^4*f*g^15
  -9673754638373*e^2*f^2*g^15
  +1798358420053*f^3*g^15
  +79292947911*e^9*g^14
  -8753708686711*e^7*f*g^14
  +18739009538787*e^5*f^2*g^14
  +29783363103531*e^3*f^3*g^14
  -10357675514669*e*f^4*g^14
  -131879921128*e^12*g^13
  -489870376160*e^10*f*g^13
  +11250567125127*e^8*f^2*g^13
  -9252951072005*e^6*f^3*g^13
  -50590774489774*e^4*f^4*g^13
  +18739009538787*e^2*f^5*g^13
  +2396209258401*f^6*g^13
  +67793375362*e^13*f*g^12
  +810556365941*e^11*f^2*g^12
  -5590189027255*e^9*f^3*g^12
  -7155486959355*e^7*f^4*g^12
  +44611522104334*e^5*f^5*g^12
  -9252951072005*e^3*f^6*g^12
  -8753708686711*e*f^7*g^12
  -296929474524*e^12*f^3*g^11
  +228811457328*e^10*f^4*g^11
  +8136366771798*e^8*f^5*g^11
  -16361796460527*e^6*f^6*g^11

private def slice8NormalPart1 (e f g : ℝ) : ℝ :=
  -7155486959355*e^4*f^7*g^11
  +11250567125127*e^2*f^8*g^11
  +79292947911*f^9*g^11
  +346435718562*e^11*f^5*g^10
  -1679601393111*e^9*f^6*g^10
  -268189488447*e^7*f^7*g^10
  +8136366771798*e^5*f^8*g^10
  -5590189027255*e^3*f^9*g^10
  -489870376160*e*f^10*g^10
  -144239565738*e^10*f^7*g^9
  +945680089929*e^8*f^8*g^9
  -1679601393111*e^6*f^9*g^9
  +228811457328*e^4*f^10*g^9
  +810556365941*e^2*f^11*g^9
  -131879921128*f^12*g^9
  +19586982069*e^9*f^9*g^8
  -144239565738*e^7*f^10*g^8
  +346435718562*e^5*f^11*g^8
  -296929474524*e^3*f^12*g^8
  +67793375362*e*f^13*g^8

private def slice8Normal (e f g : ℝ) : ℝ :=
  slice8NormalPart0 e f g + slice8NormalPart1 e f g

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
-- Normalize one small symmetric slice in the elementary variables.
private theorem slice8_normal (e f g : ℝ) :
    slice8Combination e f g = slice8Normal e f g := by
  unfold slice8Combination slice8Normal slice8NormalPart0 slice8NormalPart1
  unfold mono22_21_8
  unfold mono23_20_8
  unfold mono24_19_8
  unfold mono25_18_8
  unfold mono26_13_12
  unfold mono26_14_11
  unfold mono26_15_10
  unfold mono26_16_9
  unfold mono26_17_8
  unfold newton0 newton0row0
  unfold newton1 newton1row0
  unfold newton3 newton3row0 newton3row1
  unfold newton5 newton5row0 newton5row1
  unfold newton6 newton6row0 newton6row1 newton6row2
  unfold newton7 newton7row0 newton7row1 newton7row2
  unfold newton9 newton9row0 newton9row1 newton9row2 newton9row3
  unfold newton10 newton10row0 newton10row1 newton10row2 newton10row3
  unfold newton11 newton11row0 newton11row1 newton11row2 newton11row3
  unfold newton12 newton12row0 newton12row1 newton12row2 newton12row3 newton12row4
  unfold newton13 newton13row0 newton13row1 newton13row2 newton13row3 newton13row4
  ring

private theorem slice8_eval (p q r : ℝ) :
    positiveSlice8 p q r = slice8Normal (p+q+r) (p*q+q*r+r*p) (p*q*r) :=
  (slice8Combination_eval p q r).trans (slice8_normal _ _ _)

private def slice9Combination (e f g : ℝ) : ℝ :=
  131121471756*(mono21_21_9 e f g + mono25_13_13 e f g) +
  121919619725*(mono22_20_9 e f g + mono25_14_12 e f g) +
  104561900952*(mono23_19_9 e f g + mono25_15_11 e f g) +
  85710012316*(mono24_18_9 e f g + mono25_16_10 e f g) +
  59908854582*(mono25_17_9 e f g)

private theorem slice9Combination_eval (p q r : ℝ) :
    positiveSlice9 p q r = slice9Combination (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold positiveSlice9 pairedMonomial slice9Combination
  norm_num only
  simp only [ite_false, ite_true, add_zero]
  rw [mono21_21_9_eval, mono22_20_9_eval, mono23_19_9_eval, mono24_18_9_eval, mono25_13_13_eval,
    mono25_14_12_eval, mono25_15_11_eval, mono25_16_10_eval, mono25_17_9_eval]

private def slice9NormalPart0 (e f g : ℝ) : ℝ :=
  276633290520*g^17
  -252477213816*e^3*g^16
  -5472816971318*e*f*g^16
  -3716999374064*e^6*g^15
  -261505499244*e^4*f*g^15
  +26611377405760*e^2*f^2*g^15
  -252477213816*f^3*g^15
  -926348834395*e^9*g^14
  +8821248526120*e^7*f*g^14
  +8785910925028*e^5*f^2*g^14
  -54421438220752*e^3*f^3*g^14
  -261505499244*e*f^4*g^14
  +44803718742*e^12*g^13
  +1200704579042*e^10*f*g^13
  -5223544095037*e^8*f^2*g^13
  -20314511742876*e^6*f^3*g^13
  +52628234713990*e^4*f^4*g^13
  +8785910925028*e^2*f^5*g^13
  -3716999374064*f^6*g^13
  -483479546551*e^11*f^2*g^12
  -406941032203*e^9*f^3*g^12
  +15436274461732*e^7*f^4*g^12
  -19240745579426*e^5*f^5*g^12
  -20314511742876*e^3*f^6*g^12
  +8821248526120*e*f^7*g^12
  +788478918696*e^10*f^4*g^11
  -3209253908388*e^8*f^5*g^11
  -2612722255752*e^6*f^6*g^11
  +15436274461732*e^4*f^7*g^11
  -5223544095037*e^2*f^8*g^11

private def slice9NormalPart1 (e f g : ℝ) : ℝ :=
  -926348834395*f^9*g^11
  -393560824340*e^9*f^6*g^10
  +2291386471560*e^7*f^7*g^10
  -3209253908388*e^5*f^8*g^10
  -406941032203*e^3*f^9*g^10
  +1200704579042*e*f^10*g^10
  +59908854582*e^8*f^8*g^9
  -393560824340*e^6*f^9*g^9
  +788478918696*e^4*f^10*g^9
  -483479546551*e^2*f^11*g^9
  +44803718742*f^12*g^9

private def slice9Normal (e f g : ℝ) : ℝ :=
  slice9NormalPart0 e f g + slice9NormalPart1 e f g

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
-- Normalize one small symmetric slice in the elementary variables.
private theorem slice9_normal (e f g : ℝ) :
    slice9Combination e f g = slice9Normal e f g := by
  unfold slice9Combination slice9Normal slice9NormalPart0 slice9NormalPart1
  unfold mono21_21_9
  unfold mono22_20_9
  unfold mono23_19_9
  unfold mono24_18_9
  unfold mono25_13_13
  unfold mono25_14_12
  unfold mono25_15_11
  unfold mono25_16_10
  unfold mono25_17_9
  unfold newton0 newton0row0
  unfold newton2 newton2row0
  unfold newton3 newton3row0 newton3row1
  unfold newton4 newton4row0 newton4row1
  unfold newton6 newton6row0 newton6row1 newton6row2
  unfold newton8 newton8row0 newton8row1 newton8row2
  unfold newton9 newton9row0 newton9row1 newton9row2 newton9row3
  unfold newton10 newton10row0 newton10row1 newton10row2 newton10row3
  unfold newton11 newton11row0 newton11row1 newton11row2 newton11row3
  unfold newton12 newton12row0 newton12row1 newton12row2 newton12row3 newton12row4
  ring

private theorem slice9_eval (p q r : ℝ) :
    positiveSlice9 p q r = slice9Normal (p+q+r) (p*q+q*r+r*p) (p*q*r) :=
  (slice9Combination_eval p q r).trans (slice9_normal _ _ _)

private def slice10Combination (e f g : ℝ) : ℝ :=
  246156714638*(mono21_20_10 e f g + mono24_14_13 e f g) +
  217979843552*(mono22_19_10 e f g + mono24_15_12 e f g) +
  182181426960*(mono23_18_10 e f g + mono24_16_11 e f g) +
  138398982264*(mono24_17_10 e f g)

private theorem slice10Combination_eval (p q r : ℝ) :
    positiveSlice10 p q r = slice10Combination (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold positiveSlice10 pairedMonomial slice10Combination
  norm_num only
  simp only [ite_false, ite_true, add_zero]
  rw [mono21_20_10_eval, mono22_19_10_eval, mono23_18_10_eval, mono24_14_13_eval,
    mono24_15_12_eval, mono24_16_11_eval, mono24_17_10_eval]

private def slice10NormalPart0 (e f g : ℝ) : ℝ :=
  -369467673756*g^17
  -4474357771844*e^3*g^16
  +6659894138596*e*f*g^16
  +856589385822*e^6*g^15
  +18226912995678*e^4*f*g^15
  -24453200201808*e^2*f^2*g^15
  -4474357771844*f^3*g^15
  +830031410986*e^9*g^14
  -601368633502*e^7*f*g^14
  -28019272123564*e^5*f^2*g^14
  +29295973385440*e^3*f^3*g^14
  +18226912995678*e*f^4*g^14
  -465668557066*e^10*f*g^13
  -1992192642044*e^8*f^2*g^13
  +19114528396114*e^6*f^3*g^13
  -7227673147880*e^4*f^4*g^13
  -28019272123564*e^2*f^5*g^13
  +856589385822*f^6*g^13
  +1244658460448*e^9*f^3*g^12
  -3625240360392*e^7*f^4*g^12
  -8187370746960*e^5*f^5*g^12
  +19114528396114*e^3*f^6*g^12
  -601368633502*e*f^7*g^12
  -786611448888*e^8*f^5*g^11
  +3866647299576*e^6*f^6*g^11
  -3625240360392*e^4*f^7*g^11
  -1992192642044*e^2*f^8*g^11
  +830031410986*f^9*g^11
  +138398982264*e^7*f^7*g^10
  -786611448888*e^5*f^8*g^10

private def slice10NormalPart1 (e f g : ℝ) : ℝ :=
  1244658460448*e^3*f^9*g^10
  -465668557066*e*f^10*g^10

private def slice10Normal (e f g : ℝ) : ℝ :=
  slice10NormalPart0 e f g + slice10NormalPart1 e f g

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
-- Normalize one small symmetric slice in the elementary variables.
private theorem slice10_normal (e f g : ℝ) :
    slice10Combination e f g = slice10Normal e f g := by
  unfold slice10Combination slice10Normal slice10NormalPart0 slice10NormalPart1
  unfold mono21_20_10
  unfold mono22_19_10
  unfold mono23_18_10
  unfold mono24_14_13
  unfold mono24_15_12
  unfold mono24_16_11
  unfold mono24_17_10
  unfold newton0 newton0row0
  unfold newton1 newton1row0
  unfold newton3 newton3row0 newton3row1
  unfold newton5 newton5row0 newton5row1
  unfold newton6 newton6row0 newton6row1 newton6row2
  unfold newton7 newton7row0 newton7row1 newton7row2
  unfold newton8 newton8row0 newton8row1 newton8row2
  unfold newton9 newton9row0 newton9row1 newton9row2 newton9row3
  unfold newton10 newton10row0 newton10row1 newton10row2 newton10row3
  ring

private theorem slice10_eval (p q r : ℝ) :
    positiveSlice10 p q r = slice10Normal (p+q+r) (p*q+q*r+r*p) (p*q*r) :=
  (slice10Combination_eval p q r).trans (slice10_normal _ _ _)

private def slice11Combination (e f g : ℝ) : ℝ :=
  434723213784*(mono20_20_11 e f g + mono23_14_14 e f g) +
  403354654784*(mono21_19_11 e f g + mono23_15_13 e f g) +
  336762736136*(mono22_18_11 e f g + mono23_16_12 e f g) +
  263955969408*(mono23_17_11 e f g)

private theorem slice11Combination_eval (p q r : ℝ) :
    positiveSlice11 p q r = slice11Combination (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold positiveSlice11 pairedMonomial slice11Combination
  norm_num only
  simp only [ite_false, ite_true, add_zero]
  rw [mono20_20_11_eval, mono21_19_11_eval, mono22_18_11_eval, mono23_14_14_eval,
    mono23_15_13_eval, mono23_16_12_eval, mono23_17_11_eval]

private def slice11NormalPart0 (e f g : ℝ) : ℝ :=
  -248629246368*g^17
  +6366485166304*e^3*g^16
  +987266966624*e*f*g^16
  +2558602836480*e^6*g^15
  -17985263123160*e^4*f*g^15
  -3094026181760*e^2*f^2*g^15
  +6366485166304*f^3*g^15
  -226372562328*e^9*g^14
  -3183800961824*e^7*f*g^14
  +13811730579744*e^5*f^2*g^14
  +12324566063424*e^3*f^3*g^14
  -17985263123160*e*f^4*g^14
  +1431907434912*e^8*f^2*g^13
  -1752688852144*e^6*f^3*g^13
  -14492958225296*e^4*f^4*g^13
  +13811730579744*e^2*f^5*g^13
  +2558602836480*f^6*g^13
  -1246973080312*e^7*f^4*g^12
  +4787736592784*e^5*f^5*g^12
  -1752688852144*e^3*f^6*g^12
  -3183800961824*e*f^7*g^12
  +263955969408*e^6*f^6*g^11
  -1246973080312*e^4*f^7*g^11
  +1431907434912*e^2*f^8*g^11
  -226372562328*f^9*g^11

private def slice11Normal (e f g : ℝ) : ℝ :=
  slice11NormalPart0 e f g

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
-- Normalize one small symmetric slice in the elementary variables.
private theorem slice11_normal (e f g : ℝ) :
    slice11Combination e f g = slice11Normal e f g := by
  unfold slice11Combination slice11Normal slice11NormalPart0
  unfold mono20_20_11
  unfold mono21_19_11
  unfold mono22_18_11
  unfold mono23_14_14
  unfold mono23_15_13
  unfold mono23_16_12
  unfold mono23_17_11
  unfold newton0 newton0row0
  unfold newton2 newton2row0
  unfold newton3 newton3row0 newton3row1
  unfold newton4 newton4row0 newton4row1
  unfold newton6 newton6row0 newton6row1 newton6row2
  unfold newton7 newton7row0 newton7row1 newton7row2
  unfold newton8 newton8row0 newton8row1 newton8row2
  unfold newton9 newton9row0 newton9row1 newton9row2 newton9row3
  ring

private theorem slice11_eval (p q r : ℝ) :
    positiveSlice11 p q r = slice11Normal (p+q+r) (p*q+q*r+r*p) (p*q*r) :=
  (slice11Combination_eval p q r).trans (slice11_normal _ _ _)

private def slice12Combination (e f g : ℝ) : ℝ :=
  651774508964*(mono20_19_12 e f g + mono22_15_14 e f g) +
  565207218120*(mono21_18_12 e f g + mono22_16_13 e f g) +
  453123772903*(mono22_17_12 e f g)

private theorem slice12Combination_eval (p q r : ℝ) :
    positiveSlice12 p q r = slice12Combination (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold positiveSlice12 pairedMonomial slice12Combination
  norm_num only
  simp only [ite_false, ite_true, add_zero]
  rw [mono20_19_12_eval, mono21_18_12_eval, mono22_15_14_eval, mono22_16_13_eval, mono22_17_12_eval]

private def slice12NormalPart0 (e f g : ℝ) : ℝ :=
  1512468244947*g^17
  -1459869742003*e^3*g^16
  -11381880658873*e*f*g^16
  -2352186155359*e^6*g^15
  +2828132537894*e^4*f*g^15
  +20781544622705*e^2*f^2*g^15
  -1459869742003*f^3*g^15
  +1221771719119*e^7*f*g^14
  +1635697868432*e^5*f^2*g^14
  -16817111232623*e^3*f^3*g^14
  +2828132537894*e*f^4*g^14
  -1700411646395*e^6*f^3*g^13
  +4545607705135*e^4*f^4*g^13
  +1635697868432*e^2*f^5*g^13
  -2352186155359*f^6*g^13
  +453123772903*e^5*f^5*g^12
  -1700411646395*e^3*f^6*g^12
  +1221771719119*e*f^7*g^12

private def slice12Normal (e f g : ℝ) : ℝ :=
  slice12NormalPart0 e f g

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
-- Normalize one small symmetric slice in the elementary variables.
private theorem slice12_normal (e f g : ℝ) :
    slice12Combination e f g = slice12Normal e f g := by
  unfold slice12Combination slice12Normal slice12NormalPart0
  unfold mono20_19_12
  unfold mono21_18_12
  unfold mono22_15_14
  unfold mono22_16_13
  unfold mono22_17_12
  unfold newton0 newton0row0
  unfold newton1 newton1row0
  unfold newton3 newton3row0 newton3row1
  unfold newton5 newton5row0 newton5row1
  unfold newton6 newton6row0 newton6row1 newton6row2
  unfold newton7 newton7row0 newton7row1 newton7row2
  ring

private theorem slice12_eval (p q r : ℝ) :
    positiveSlice12 p q r = slice12Normal (p+q+r) (p*q+q*r+r*p) (p*q*r) :=
  (slice12Combination_eval p q r).trans (slice12_normal _ _ _)

private def slice13Combination (e f g : ℝ) : ℝ :=
  896599559504*(mono19_19_13 e f g + mono21_15_15 e f g) +
  837188338706*(mono20_18_13 e f g + mono21_16_14 e f g) +
  709752652300*(mono21_17_13 e f g)

private theorem slice13Combination_eval (p q r : ℝ) :
    positiveSlice13 p q r = slice13Combination (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold positiveSlice13 pairedMonomial slice13Combination
  norm_num only
  simp only [ite_false, ite_true, add_zero]
  rw [mono19_19_13_eval, mono20_18_13_eval, mono21_15_15_eval, mono21_16_14_eval, mono21_17_13_eval]

private def slice13NormalPart0 (e f g : ℝ) : ℝ :=
  -1772790632112*g^17
  -4130593962880*e^3*g^16
  +11604549815060*e*f*g^16
  +641728186692*e^6*g^15
  +4339217114366*e^4*f*g^15
  -12106165580388*e^2*f^2*g^15
  -4130593962880*f^3*g^15
  -2001822270494*e^5*f^2*g^14
  +2984159049740*e^3*f^3*g^14
  +4339217114366*e*f^4*g^14
  +709752652300*e^4*f^4*g^13
  -2001822270494*e^2*f^5*g^13
  +641728186692*f^6*g^13

private def slice13Normal (e f g : ℝ) : ℝ :=
  slice13NormalPart0 e f g

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
-- Normalize one small symmetric slice in the elementary variables.
private theorem slice13_normal (e f g : ℝ) :
    slice13Combination e f g = slice13Normal e f g := by
  unfold slice13Combination slice13Normal slice13NormalPart0
  unfold mono19_19_13
  unfold mono20_18_13
  unfold mono21_15_15
  unfold mono21_16_14
  unfold mono21_17_13
  unfold newton0 newton0row0
  unfold newton2 newton2row0
  unfold newton3 newton3row0 newton3row1
  unfold newton4 newton4row0 newton4row1
  unfold newton5 newton5row0 newton5row1
  unfold newton6 newton6row0 newton6row1 newton6row2
  ring

private theorem slice13_eval (p q r : ℝ) :
    positiveSlice13 p q r = slice13Normal (p+q+r) (p*q+q*r+r*p) (p*q*r) :=
  (slice13Combination_eval p q r).trans (slice13_normal _ _ _)

private def slice14Combination (e f g : ℝ) : ℝ :=
  1089028517556*(mono19_18_14 e f g + mono20_16_15 e f g) +
  984611113899*(mono20_17_14 e f g)

private theorem slice14Combination_eval (p q r : ℝ) :
    positiveSlice14 p q r = slice14Combination (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold positiveSlice14 pairedMonomial slice14Combination
  norm_num only
  simp only [ite_false, ite_true, add_zero]
  rw [mono19_18_14_eval, mono20_16_15_eval, mono20_17_14_eval]

private def slice14NormalPart0 (e f g : ℝ) : ℝ :=
  -626504421942*g^17
  +4042861859253*e^3*g^16
  -2476600804398*e*f*g^16
  -1864804824141*e^4*f*g^15
  +149271884643*e^2*f^2*g^15
  +4042861859253*f^3*g^15
  +984611113899*e^3*f^3*g^14
  -1864804824141*e*f^4*g^14

private def slice14Normal (e f g : ℝ) : ℝ :=
  slice14NormalPart0 e f g

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
-- Normalize one small symmetric slice in the elementary variables.
private theorem slice14_normal (e f g : ℝ) :
    slice14Combination e f g = slice14Normal e f g := by
  unfold slice14Combination slice14Normal slice14NormalPart0
  unfold mono19_18_14
  unfold mono20_16_15
  unfold mono20_17_14
  unfold newton0 newton0row0
  unfold newton1 newton1row0
  unfold newton3 newton3row0 newton3row1
  unfold newton4 newton4row0 newton4row1
  ring

private theorem slice14_eval (p q r : ℝ) :
    positiveSlice14 p q r = slice14Normal (p+q+r) (p*q+q*r+r*p) (p*q*r) :=
  (slice14Combination_eval p q r).trans (slice14_normal _ _ _)

private def slice15Combination (e f g : ℝ) : ℝ :=
  1306480490248*(mono18_18_15 e f g + mono19_16_16 e f g) +
  1239974673312*(mono19_17_15 e f g)

private theorem slice15Combination_eval (p q r : ℝ) :
    positiveSlice15 p q r = slice15Combination (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold positiveSlice15 pairedMonomial slice15Combination
  norm_num only
  simp only [ite_false, ite_true, add_zero]
  rw [mono18_18_15_eval, mono19_16_16_eval, mono19_17_15_eval]

private def slice15NormalPart0 (e f g : ℝ) : ℝ :=
  4118958921552*g^17
  -1173468856376*e^3*g^16
  -2878984248240*e*f*g^16
  +1239974673312*e^2*f^2*g^15
  -1173468856376*f^3*g^15

private def slice15Normal (e f g : ℝ) : ℝ :=
  slice15NormalPart0 e f g

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
-- Normalize one small symmetric slice in the elementary variables.
private theorem slice15_normal (e f g : ℝ) :
    slice15Combination e f g = slice15Normal e f g := by
  unfold slice15Combination slice15Normal slice15NormalPart0
  unfold mono18_18_15
  unfold mono19_16_16
  unfold mono19_17_15
  unfold newton0 newton0row0
  unfold newton2 newton2row0
  unfold newton3 newton3row0 newton3row1
  ring

private theorem slice15_eval (p q r : ℝ) :
    positiveSlice15 p q r = slice15Normal (p+q+r) (p*q+q*r+r*p) (p*q*r) :=
  (slice15Combination_eval p q r).trans (slice15_normal _ _ _)

private def slice16Combination (e f g : ℝ) : ℝ :=
  1462001693088*(mono18_17_16 e f g)

private theorem slice16Combination_eval (p q r : ℝ) :
    positiveSlice16 p q r = slice16Combination (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold positiveSlice16 pairedMonomial slice16Combination
  norm_num only
  simp only [ite_false, ite_true, add_zero]
  rw [mono18_17_16_eval]

private def slice16NormalPart0 (e f g : ℝ) : ℝ :=
  -4386005079264*g^17
  +1462001693088*e*f*g^16

private def slice16Normal (e f g : ℝ) : ℝ :=
  slice16NormalPart0 e f g

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
-- Normalize one small symmetric slice in the elementary variables.
private theorem slice16_normal (e f g : ℝ) :
    slice16Combination e f g = slice16Normal e f g := by
  unfold slice16Combination slice16Normal slice16NormalPart0
  unfold mono18_17_16
  unfold newton0 newton0row0
  unfold newton1 newton1row0
  ring

private theorem slice16_eval (p q r : ℝ) :
    positiveSlice16 p q r = slice16Normal (p+q+r) (p*q+q*r+r*p) (p*q*r) :=
  (slice16Combination_eval p q r).trans (slice16_normal _ _ _)

private def slice17Combination (e f g : ℝ) : ℝ :=
  1562862225726*(mono17_17_17 e f g)

private theorem slice17Combination_eval (p q r : ℝ) :
    positiveSlice17 p q r = slice17Combination (p+q+r) (p*q+q*r+r*p) (p*q*r) := by
  unfold positiveSlice17 pairedMonomial slice17Combination
  norm_num only
  simp only [ite_false, ite_true, add_zero]
  rw [mono17_17_17_eval]

private def slice17NormalPart0 (e f g : ℝ) : ℝ :=
  1562862225726*g^17

private def slice17Normal (e f g : ℝ) : ℝ :=
  slice17NormalPart0 e f g

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
-- Normalize one small symmetric slice in the elementary variables.
private theorem slice17_normal (e f g : ℝ) :
    slice17Combination e f g = slice17Normal e f g := by
  unfold slice17Combination slice17Normal slice17NormalPart0
  unfold mono17_17_17
  ring

private theorem slice17_eval (p q r : ℝ) :
    positiveSlice17 p q r = slice17Normal (p+q+r) (p*q+q*r+r*p) (p*q*r) :=
  (slice17Combination_eval p q r).trans (slice17_normal _ _ _)

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 10000 in
-- Add the already normalized slices without expanding powers of spectral sums.
private theorem quotient_slices (e f g : ℝ) :
    quotientElementary e f g = boundaryNormal e f g + slice1Normal e f g + slice2Normal e f g +
      slice3Normal e f g + slice4Normal e f g + slice5Normal e f g + slice6Normal e f g +
      slice7Normal e f g + slice8Normal e f g + slice9Normal e f g + slice10Normal e f g +
      slice11Normal e f g + slice12Normal e f g + slice13Normal e f g + slice14Normal e f g +
      slice15Normal e f g + slice16Normal e f g + slice17Normal e f g := by
  unfold quotientElementary quotientElementaryPart1 quotientElementaryPart2 quotientElementaryPart3
  unfold boundaryNormal boundaryNormalPart0 boundaryNormalPart1 boundaryNormalPart2
    boundaryNormalPart3 boundaryNormalPart4 boundaryNormalPart5
  unfold slice1Normal slice1NormalPart0 slice1NormalPart1 slice1NormalPart2 slice1NormalPart3
    slice1NormalPart4
  unfold slice2Normal slice2NormalPart0 slice2NormalPart1 slice2NormalPart2 slice2NormalPart3
    slice2NormalPart4
  unfold slice3Normal slice3NormalPart0 slice3NormalPart1 slice3NormalPart2 slice3NormalPart3
  unfold slice4Normal slice4NormalPart0 slice4NormalPart1 slice4NormalPart2 slice4NormalPart3
  unfold slice5Normal slice5NormalPart0 slice5NormalPart1 slice5NormalPart2
  unfold slice6Normal slice6NormalPart0 slice6NormalPart1 slice6NormalPart2
  unfold slice7Normal slice7NormalPart0 slice7NormalPart1 slice7NormalPart2
  unfold slice8Normal slice8NormalPart0 slice8NormalPart1
  unfold slice9Normal slice9NormalPart0 slice9NormalPart1
  unfold slice10Normal slice10NormalPart0 slice10NormalPart1
  unfold slice11Normal slice11NormalPart0
  unfold slice12Normal slice12NormalPart0
  unfold slice13Normal slice13NormalPart0
  unfold slice14Normal slice14NormalPart0
  unfold slice15Normal slice15NormalPart0
  unfold slice16Normal slice16NormalPart0
  unfold slice17Normal slice17NormalPart0
  ring

private theorem quotient_positive_identity (p q r : ℝ) :
    quotientElementary (p+q+r) (p*q+q*r+r*p) (p*q*r) = positiveCertificate p q r := by
  rw [quotient_slices]
  unfold positiveCertificate
  rw [← boundary_eval p q r, ← slice1_eval p q r, ← slice2_eval p q r, ← slice3_eval p q r, ←
    slice4_eval p q r, ← slice5_eval p q r, ← slice6_eval p q r, ← slice7_eval p q r, ←
    slice8_eval p q r, ← slice9_eval p q r, ← slice10_eval p q r, ← slice11_eval p q r, ←
    slice12_eval p q r, ← slice13_eval p q r, ← slice14_eval p q r, ← slice15_eval p q r, ←
    slice16_eval p q r, ← slice17_eval p q r]

/-- The exact polynomial certificate: no radical comparison or spectral
    denominator is hidden in this identity, and collisions are retained. -/
theorem p396_identity (p q r : ℝ) :
    p396 p q r = p*q*r*(Q p q r)^2*(p-q)^2*(q-r)^2*(r-p)^2*positiveCertificate p q r := by
  let e := p+q+r
  let f := p*q+q*r+r*p
  let g := p*q*r
  have hcore := elementary_core e f g
  simp only [← Q_elementary p q r] at hcore
  have hquot := quotient_positive_identity p q r
  have hdisc := discriminant_elementary p q r
  unfold p396
  simp only [pair_scaled, triple_scaled, u_elementary]
  unfold cycleScaled
  change 4*uElementary e f g*((Q p q r)^4*g*tElementary e f g)+
    396*((Q p q r)^8*g^2*discriminant e f g*minusElementary e f g*plusElementary e f g)-
    uElementary e f g*(27*g*Q p q r*symmetricF e f g)^2 = _
  calc
    _ = g*(Q p q r)^2*(uElementary e f g*
        (4*(Q p q r)^2*tElementary e f g-729*g*(symmetricF e f g)^2)+
        396*(Q p q r)^6*g*discriminant e f g*minusElementary e f g*plusElementary e f g) := by ring
    _ = g*(Q p q r)^2*discriminant e f g*quotientElementary e f g := by rw [hcore]
    _ = _ := by rw [hquot, ← hdisc]; dsimp only [g]; ring

theorem p396_nonneg (p q r : ℝ) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) : 0 ≤ p396 p q r := by
  rw [p396_identity]
  have hcert := certificate_nonneg p q r hp.le hq.le hr.le
  positivity

theorem p396_pos (p q r : ℝ) (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (hpq : p ≠ q) (hqr : q ≠ r) (hrp : r ≠ p) : 0 < p396 p q r := by
  rw [p396_identity]
  have hcert := certificate_pos p q r hp hq hr
  have hQ := Q_pos p q r hp hq hr
  have hd1 := sq_pos_of_ne_zero (sub_ne_zero.mpr hpq)
  have hd2 := sq_pos_of_ne_zero (sub_ne_zero.mpr hqr)
  have hd3 := sq_pos_of_ne_zero (sub_ne_zero.mpr hrp)
  positivity

end D5.S3.Quantum.Matrix.HsfThreeLevelCoefficients
