/- GID: D5/S3/Combinatorics/SpectralGraph/Nikandish/BalancedPairDeterminant
   generality: G
   mirror-B: D5/B/S3/Combinatorics/SpectralGraph/BalancedPairDeterminant
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Full balanced-region determinant positivity on the actual four-cell operator. -/
import D5.S3.Combinatorics.SpectralGraph.PairedIdealIntersectionDeterminants

/-! Source: four-prime-single-pair-balanced, PR9 revision
6d491f77b35dec808fc777b69939c56cdae5dc02. The entire real domain
 a <= b <= c <= 2a-6 is retained. Complete symbolic coefficient identities
at the spectral endpoint three prove that no eigenvalue is at or below
three. All coefficients are checked by ring in Lean; this is no sampled
exponent test. The original 243-coefficient leading-minor proof remains
attributed source evidence; this representation uses the full determinant
with a nonnegative spectral shift. -/
set_option autoImplicit false
namespace D5.S3.Combinatorics.SpectralGraph.BalancedPairDeterminant
open Matrix PairedIdealIntersectionObstructions PairedIdealIntersectionDeterminants

private def C0 (d e u : ℝ) : ℝ :=
      12*d^5*e +
      24*d^5*u +
      12*d^5 +
      54*d^4*e^2 +
      148*d^4*e*u +
      344*d^4*e +
      88*d^4*u^2 +
      628*d^4*u +
      454*d^4 +
      96*d^3*e^3 +
      335*d^3*e^2*u +
      1129*d^3*e^2 +
      365*d^3*e*u^2 +
      2981*d^3*e*u +
      4247*d^3*e +
      126*d^3*u^3 +
      1725*d^3*u^2 +
      6678*d^3*u +
      5322*d^3 +
      84*d^2*e^4 +
      357*d^2*e^3*u +
      1443*d^2*e^3 +
      550*d^2*e^2*u^2 +
      4918*d^2*e^2*u +
      9076*d^2*e^2 +
      365*d^2*e*u^3 +
      5250*d^2*e*u^2 +
      22517*d^2*e*u +
      25280*d^2*e +
      88*d^2*u^4 +
      1775*d^2*u^3 +
      12500*d^2*u^2 +
      34594*d^2*u +
      27048*d^2 +
      36*d*e^5 +
      181*d*e^4*u +
      815*d*e^4 +
      357*d*e^3*u^2 +
      3405*d*e^3*u +
      7227*d*e^3 +
      345*d*e^2*u^3 +
      5163*d*e^2*u^2 +
      23799*d*e^2*u +
      31716*d*e^2 +
      163*d*e*u^4 +
      3371*d*e*u^3 +
      24716*d*e*u^2 +
      73774*d*e*u +
      69984*d*e +
      30*d*u^5 +
      798*d*u^4 +
      8144*d*u^3 +
      39180*d*u^2 +
      85872*d*u +
      62824*d +
      6*e^6 +
      35*e^5*u +
      169*e^5 +
      84*e^4*u^2 +
      840*e^4*u +
      1944*e^4 +
      106*e^3*u^3 +
      1638*e^3*u^2 +
      7960*e^3*u +
      11758*e^3 +
      74*e^2*u^4 +
      1564*e^2*u^3 +
      11852*e^2*u^2 +
      37410*e^2*u +
      39808*e^2 +
      27*e*u^5 +
      729*e*u^4 +
      7600*e*u^3 +
      37776*e*u^2 +
      87576*e*u +
      72200*e +
      4*u^6 +
      132*u^5 +
      1764*u^4 +
      12124*u^3 +
      44640*u^2 +
      81576*u +
      54880

private theorem C0_pos (d e u : ℝ) (hd : 0≤d) (he : 0≤e) (hu : 0≤u) :
    0<C0 d e u := by
  unfold C0
  positivity

private def C1 (d e u : ℝ) : ℝ :=
      48*d^6 +
      244*d^5*e +
      200*d^5*u +
      1300*d^5 +
      510*d^4*e^2 +
      840*d^4*e*u +
      5462*d^4*e +
      340*d^4*u^2 +
      4424*d^4*u +
      14292*d^4 +
      560*d^3*e^3 +
      1391*d^3*e^2*u +
      9049*d^3*e^2 +
      1133*d^3*e*u^2 +
      14753*d^3*e*u +
      47698*d^3*e +
      302*d^3*u^3 +
      5905*d^3*u^2 +
      38228*d^3*u +
      81799*d^3 +
      340*d^2*e^4 +
      1133*d^2*e^3*u +
      7375*d^2*e^3 +
      1394*d^2*e^2*u^2 +
      18167*d^2*e^2*u +
      58791*d^2*e^2 +
      749*d^2*e*u^3 +
      14661*d^2*e*u^2 +
      95027*d^2*e*u +
      203597*d^2*e +
      148*d^2*u^4 +
      3869*d^2*u^3 +
      37685*d^2*u^2 +
      161797*d^2*u +
      257934*d^2 +
      108*d*e^5 +
      453*d*e^4*u +
      2951*d*e^4 +
      749*d*e^3*u^2 +
      9771*d*e^3*u +
      31656*d*e^3 +
      609*d*e^2*u^3 +
      11935*d*e^2*u^2 +
      77463*d*e^2*u +
      166207*d*e^2 +
      243*d*e*u^4 +
      6361*d*e*u^3 +
      62051*d*e*u^2 +
      266845*d*e*u +
      426134*d*e +
      38*d*u^5 +
      1246*d*u^4 +
      16244*d*u^3 +
      105048*d*u^2 +
      336400*d*u +
      426204*d +
      14*e^6 +
      71*e^5*u +
      463*e^5 +
      148*e^4*u^2 +
      1933*e^4*u +
      6271*e^4 +
      162*e^3*u^3 +
      3179*e^3*u^2 +
      20664*e^3*u +
      44409*e^3 +
      98*e^2*u^4 +
      2569*e^2*u^3 +
      25101*e^2*u^2 +
      108135*e^2*u +
      173002*e^2 +
      31*e*u^5 +
      1018*e*u^4 +
      13294*e*u^3 +
      86130*e*u^2 +
      276364*e*u +
      350868*e +
      4*u^6 +
      158*u^5 +
      2586*u^4 +
      22404*u^3 +
      108164*u^2 +
      275532*u +
      289048

private theorem C1_pos (d e u : ℝ) (hd : 0≤d) (he : 0≤e) (hu : 0≤u) :
    0<C1 d e u := by
  unfold C1
  positivity

private def C2 (d e u : ℝ) : ℝ :=
      16*d^5 +
      68*d^4*e +
      56*d^4*u +
      392*d^4 +
      114*d^3*e^2 +
      188*d^3*e*u +
      1316*d^3*e +
      76*d^3*u^2 +
      1064*d^3*u +
      3716*d^3 +
      94*d^2*e^3 +
      233*d^2*e^2*u +
      1631*d^2*e^2 +
      189*d^2*e*u^2 +
      2646*d^2*e*u +
      9244*d^2*e +
      50*d^2*u^3 +
      1050*d^2*u^2 +
      7340*d^2*u +
      17025*d^2 +
      38*d*e^4 +
      126*d*e^3*u +
      882*d*e^3 +
      154*d*e^2*u^2 +
      2156*d*e^2*u +
      7536*d*e^2 +
      82*d*e*u^3 +
      1722*d*e*u^2 +
      12043*d*e*u +
      27955*d*e +
      16*d*u^4 +
      448*d*u^3 +
      4703*d*u^2 +
      21860*d*u +
      37806*d +
      6*e^5 +
      25*e^4*u +
      175*e^4 +
      41*e^3*u^2 +
      574*e^3*u +
      2008*e^3 +
      33*e^2*u^3 +
      693*e^2*u^2 +
      4850*e^2*u +
      11273*e^2 +
      13*e*u^4 +
      364*e*u^3 +
      3823*e*u^2 +
      17786*e*u +
      30798*e +
      2*u^5 +
      70*u^4 +
      981*u^3 +
      6856*u^2 +
      23790*u +
      32676

private theorem C2_pos (d e u : ℝ) (hd : 0≤d) (he : 0≤e) (hu : 0≤u) :
    0<C2 d e u := by
  unfold C2
  positivity

private def C3 (d e u : ℝ) : ℝ :=
      4*d^3 +
      10*d^2*e +
      8*d^2*u +
      60*d^2 +
      8*d*e^2 +
      13*d*e*u +
      98*d*e +
      5*d*u^2 +
      76*d*u +
      289*d +
      2*e^3 +
      5*e^2*u +
      38*e^2 +
      4*e*u^2 +
      61*e*u +
      233*e +
      u^3 +
      23*u^2 +
      177*u +
      442

private theorem C3_pos (d e u : ℝ) (hd : 0≤d) (he : 0≤e) (hu : 0≤u) :
    0<C3 d e u := by
  unfold C3
  positivity

/-- Exact full determinant, including every boundary of the unbounded region. -/
theorem shifted_positive (a b c x : ℝ) (hab : a≤b) (hbc : b≤c)
    (hca : c≤2*a-6) (hx : x≤3) : 0<(tensorK a b c-x • 1).det := by
  let d:=b-a
  let e:=c-b
  let u:=2*a-c-6
  let t:=3-x
  have hd : 0≤d := by dsimp [d]; linarith
  have he : 0≤e := by dsimp [e]; linarith
  have hu : 0≤u := by dsimp [u]; linarith
  have ht : 0≤t := by dsimp [t]; linarith
  have hid : (tensorK a b c-x • 1).det =
      t^4+C3 d e u*t^3+C2 d e u*t^2+C1 d e u*t+C0 d e u := by
    rw [det_tensorK_sub_scalar]
    dsimp [d,e,u,t,C0,C1,C2,C3]
    ring
  rw [hid]
  have h0:=C0_pos d e u hd he hu
  have h1:=C1_pos d e u hd he hu
  have h2:=C2_pos d e u hd he hu
  have h3:=C3_pos d e u hd he hu
  positivity

/-- Every actual tensor eigenpair is above three, without a finite range bound. -/
theorem eigenvalue_gt_three (a b c x : ℝ) (hab : a≤b) (hbc : b≤c)
    (hca : c≤2*a-6) (v : Fin 2 × Fin 2 → ℝ) (hv : v≠0)
    (hE : tensorK a b c*ᵥv=x • v) : 3<x := by
  by_contra! hle
  have hd:=(shifted_positive a b c x hab hbc hca hle).ne'
  apply hv
  apply Matrix.eq_zero_of_mulVec_eq_zero hd
  rw [sub_mulVec,hE,smul_mulVec,one_mulVec,sub_self]

end D5.S3.Combinatorics.SpectralGraph.BalancedPairDeterminant
