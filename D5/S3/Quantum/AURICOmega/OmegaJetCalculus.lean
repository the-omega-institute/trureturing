/- GID: D5/S3/Quantum/AURICOmega/OmegaJetCalculus
   generality: G
   mirror-B: D5/B/S3/Quantum/AURICOmega/OmegaJetCalculus
   mirror-E: none(waiver:evidence-not-specified-by-formal-manifest)
   anchors: []
   utility: none
   digest: Rational second-order jets and differential identities of formal rational series. -/

module
prelude
public import OmegaMath.Calculus.Jet2
public import OmegaMath.Calculus.DFiniteJet

namespace D5.S3.Quantum.AURICOmega.OmegaJetCalculus

open Omega

/-- The formal increment cubes to zero in the second-order jet algebra. -/
public theorem var_cube : Jet2.Equivalent ((Jet2.var.mul Jet2.var).mul Jet2.var) Jet2.zero :=
  Omega.Jet2.var_cube

/-- A second-order jet with finite higher coefficients and invertible constant coefficient has an inverse. -/
public theorem mul_inv {a : Jet2} (h₀ : a.j0.Unit) (h₁ : a.j1.Finite) (h₂ : a.j2.Finite) :
    Jet2.Equivalent (a.mul a.inv) Jet2.one :=
  Omega.Jet2.mul_inv h₀ h₁ h₂

/-- The first and second chain rules hold at the zero shift of the inner jet. -/
public theorem chain_rule {g f : Jet2} (hg : g.Finite) (hf : f.Finite)
    (h : IntRatio.Equivalent f.j0 IntRatio.zero) :
    And (IntRatio.Equivalent (Jet2.compose g f).first (g.first.mul f.first))
      (IntRatio.Equivalent (Jet2.compose g f).second
        ((g.second.mul (f.first.mul f.first)).add (g.first.mul f.second))) :=
  Omega.Jet2.chain_rule hg hf h

/-- The fidelity jet consists of three exact rational coefficients. -/
public theorem kappa_jet (x : IntRatio) (hx : x.Finite) :
    Jet2.Equivalent (Jet2.kappaJetAt x)
      ⟨Jet2.kappa x,
        (IntRatio.two.mul x).neg.mul (((Jet2.fidelityDen x).mul (Jet2.fidelityDen x)).inv),
        ((IntRatio.three.mul (x.mul x)).sub IntRatio.one).mul
          ((((Jet2.fidelityDen x).mul (Jet2.fidelityDen x)).mul (Jet2.fidelityDen x)).inv)⟩ :=
  Omega.Jet2.kappa_jet x hx

/-- The fidelity jet at one has coefficients one half, minus one half and one quarter. -/
public theorem kappa_jet_one :
    Jet2.Equivalent (Jet2.kappaJetAt IntRatio.one)
      ⟨IntRatio.fraction Int.one Nat.zero.succ,
        IntRatio.fraction Int.one.neg Nat.zero.succ,
        IntRatio.fraction Int.one Nat.zero.succ.succ.succ⟩ :=
  Omega.Jet2.kappa_jet_one

/-- The difference between the secant slope and the fidelity jet's linear coefficient is an exact ratio. -/
public theorem kappa_secant_discrepancy (x h : IntRatio) (hx : x.Finite) (hu : h.Unit) :
    IntRatio.Equivalent
      ((((Jet2.kappa (x.add h)).sub (Jet2.kappa x)).mul h.inv).sub (Jet2.kappaJetAt x).first)
      ((h.mul (((IntRatio.three.mul (x.mul x)).add ((IntRatio.two.mul x).mul h)).sub IntRatio.one)).mul
        ((((Jet2.fidelityDen x).mul (Jet2.fidelityDen x)).mul (Jet2.fidelityDen (x.add h))).inv)) :=
  Omega.Jet2.kappa_secant_discrepancy x h hx hu

open Omega.JetSeq

/-- Leibniz's rule is valid coefficientwise through every truncation degree. -/
public theorem deriv_mul_equivAt (N : Nat) (f g : JetSeq) :
    EquivalentAt N (deriv (mul f g)) (add (mul (deriv f) g) (mul f (deriv g))) :=
  Omega.JetSeq.deriv_mul_equivAt N f g

/-- The exponential solves the scalar first-order differential equation with its parameter as rate. -/
public theorem deriv_exp (a : IntRatio) : Equivalent (deriv (Exp a)) (smul a (Exp a)) :=
  Omega.JetSeq.deriv_exp a

/-- The formal derivative of cosine is minus sine. -/
public theorem deriv_cos : Equivalent (deriv Cos) (neg Sin) :=
  Omega.JetSeq.deriv_cos

/-- The formal derivative of sine is cosine. -/
public theorem deriv_sin : Equivalent (deriv Sin) Cos :=
  Omega.JetSeq.deriv_sin

/-- Multiplying formal exponentials adds their parameters. -/
public theorem exp_add (a b : IntRatio) : Equivalent (mul (Exp a) (Exp b)) (Exp (a.add b)) :=
  Omega.JetSeq.exp_add a b

/-- Negating a finite parameter gives the multiplicative inverse of its formal exponential. -/
public theorem exp_inverse {a : IntRatio} (ha : IntRatio.Finite a) :
    Equivalent (mul (Exp a) (Exp a.neg)) one :=
  Omega.JetSeq.exp_inverse ha

/-- The squares of the formal cosine and sine sum to one. -/
public theorem cos_sq_add_sin_sq : Equivalent (add (mul Cos Cos) (mul Sin Sin)) one :=
  Omega.JetSeq.cos_sq_add_sin_sq

/-- The formal arctangent equation is `(1 + η²) A' = 1`. -/
public theorem atan_ode : Equivalent (mul (deriv Atan) oneAddEtaSq) one :=
  Omega.JetSeq.atan_ode

/-- The Cayley cosine equation is `(1 + η²) C' = -2 S`. -/
public theorem cayley_cos_ode :
    Equivalent (mul (deriv CayleyCos) oneAddEtaSq) (smul IntRatio.two.neg CayleySin) :=
  Omega.JetSeq.cayley_cos_ode

/-- The Cayley sine equation is `(1 + η²) S' = 2 C`. -/
public theorem cayley_sin_ode :
    Equivalent (mul (deriv CayleySin) oneAddEtaSq) (smul IntRatio.two CayleyCos) :=
  Omega.JetSeq.cayley_sin_ode

/-- The Cayley initial point and equations below degree N force the coefficients through degree N. -/
public theorem cayley_unique_at (N : Nat) {f g : JetSeq} (hf : Finite f) (hg : Finite g)
    (f0 : IntRatio.Equivalent (f Nat.zero) IntRatio.one)
    (g0 : IntRatio.Equivalent (g Nat.zero) IntRatio.zero)
    (odeF : ∀ k, Nat.lt k N → IntRatio.Equivalent (mul (deriv f) oneAddEtaSq k)
      (smul IntRatio.two.neg g k))
    (odeG : ∀ k, Nat.lt k N → IntRatio.Equivalent (mul (deriv g) oneAddEtaSq k)
      (smul IntRatio.two f k)) :
    And (EquivalentAt N f CayleyCos) (EquivalentAt N g CayleySin) :=
  Omega.JetSeq.cayley_unique_at N hf hg f0 g0 odeF odeG

end D5.S3.Quantum.AURICOmega.OmegaJetCalculus
