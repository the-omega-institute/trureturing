/- GID: D5/S0/Computability/BinaryMachine/NPPreimage
   generality: G
   mirror-B: D5/B/S0/Computability/BinaryMachine/NPPreimage
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: NP is closed under executed polynomial preimages with the original target witness bound. -/

import D5.S0.Computability.BinaryMachine.PairPreimage
import D5.S0.Computability.BinaryMachine.BoundedVerifier
import D5.S0.Computability.BinaryMachine.DecisionComposition

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace Complexity

/-- Polynomial preimages preserve NP. Target witness bounds are checked against
`|f x|` inside an executed total verifier, while source witness bounds are derived
from the physical output-size bound of the concrete transducer. -/
theorem inNP_preimage {A : Language} {f : Word → Word}
    (hA : InNP A) (hf : PolyTime f) : InNP (fun x => A (f x)) := by
  classical
  obtain ⟨M,c,e,hM,hA⟩ := hA
  obtain ⟨N,hN,hNorm⟩ := BoundedVerifier.normalize M hM c e
  obtain ⟨K,hK,hPre⟩ := DecisionComposition.preprocess (PairPreimage.polyTime_map hf) N hN
  obtain ⟨F,a,b,hF⟩ := hf
  let size := fun n => n + 2 * powerBound a b n
  have hsize : ∀ x, (f x).length ≤ size x.length := by
    intro x
    obtain ⟨t,out,ht,hr,ho⟩ := hF x
    have hl := runInput_output_length_le F t x (true,out) hr
    change out.output.length ≤ x.length + 2*t at hl
    rw [ho] at hl
    unfold size; omega
  have hpoly := (PolynomialBound.power c e).comp
    (PolynomialBound.identity.add ((PolynomialBound.constant 2).mul (PolynomialBound.power a b)))
  obtain ⟨d,l,hpoly⟩ := hpoly
  refine ⟨K,d,l,hK,?_⟩
  intro x
  have hacc (w : Word) : Accepts K (pairWords x w) ↔
      w.length ≤ powerBound c e (f x).length ∧ Accepts M (pairWords (f x) w) := by
    rw [hPre, hNorm]
    simp [BoundedVerifier.Good,PairPreimage.map]
  constructor
  · intro hx
    obtain ⟨w,hw,ha⟩ := (hA (f x)).mp hx
    refine ⟨w,?_,(hacc w).mpr ⟨hw,ha⟩⟩
    exact hw.trans ((powerBound_mono c e (hsize x)).trans (hpoly x.length))
  · rintro ⟨w,_,ha⟩
    exact (hA (f x)).mpr ⟨w,(hacc w).mp ha⟩

/-- coNP is the class of complements of languages in NP. -/
def InCoNP (A : Language) : Prop := InNP (fun x => ¬ A x)

/-- DP is the class of language intersections, with one NP and one coNP factor. -/
def InDP (A : Language) : Prop :=
  ∃ X Y : Language, InNP X ∧ InCoNP Y ∧ ∀ x, A x ↔ X x ∧ Y x

def CoNPComplete (A : Language) : Prop :=
  InCoNP A ∧ ∀ X : Language, InCoNP X → PolyRed X A

def DPComplete (A : Language) : Prop :=
  InDP A ∧ ∀ X : Language, InDP X → PolyRed X A

end Complexity
