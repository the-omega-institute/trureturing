using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis;

internal sealed class NonautonomousDysonPhillipsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Continuous time-dependent bounded perturbations of a strongly continuous complex Banach contraction semigroup admit an ordered Bochner series and a unique continuous mild evolution on every finite closed time triangle.",
        H("Nonautonomous Dyson–Phillips evolution"), Blocks(
            Paragraph(Text("Let E be a complex Banach space in any universe, including the zero space. Contraction consists of bounded complex-linear maps S.operator(q) for nonnegative real q, identity at zero, the additive semigroup law, operator norm at most one, and continuous vector orbits. Its auxiliary real-time action A(t)=S.operator(Real.toNNReal(t)) agrees with the given S at every nonnegative time and equals the identity at nonpositive times. Strong continuity suffices; no operator-norm continuity of S is assumed.")),
            Paragraph(Text("Fix T>=0 and B from the reals to bounded complex-linear endomorphisms, continuous in operator norm on Icc(0,T). Every M>=0 bounding norm(B(s)) there is admissible. B has no regularity or bound outside that interval. The closed triangle has coordinates (t,r) with 0<=r<=t<=T. All integrals below are E-valued Bochner interval integrals with real Lebesgue measure volume. The absolute coefficient time s and the left order A(t-s) after B(s) are retained without a commutation assumption.")),
            Paragraph(Text("The action bounds, joint action continuity, interval extension, orbit continuity, term identities and locality, diagonal sum, additive action law and constant-coefficient identities are also available to the strongly continuous coefficient construction. Their original definitions, statements and proofs remain the shared mathematical source.")),
            new DocumentBlock.DisplayFormula(Definitions()),
            Describe.Lean(
                DescribeId.Create("causal-iterate-bound"),
                DeclarationHandle.Create("D5/S3/Quantum/Analysis/NonautonomousDysonPhillips.causal_iterate_bound"),
                H("Factorial control of actual causal iterates"),
                StatementSource.FromAuthor(IterateStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The estimate allows arbitrary real r<=T, B continuous on Icc(r,T), M>=0 bounding B there, and any continuous vector trajectory v there with norm(v(s))<=C. The constant C is real; its bound at the included endpoint r already implies C>=0. For every natural n and t in Icc(r,T), the actual recursively integrated G(n,t) has norm at most C*(M*(t-r))^n/n!, equivalently C*M^n*(t-r)^n/n! with the ordinary convention for the zeroth power.")),
                    Paragraph(Text("Continuity and integrability propagate through the causal integral. Interval projections extend B and v only for this local continuity argument and agree with the original functions throughout the integration interval. Induction dominates each actual integrand and integrates the preceding polynomial bound. No division by M or a vector norm occurs."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nonautonomous-bounded-perturbation"),
                DeclarationHandle.Create("D5/S3/Quantum/Analysis/NonautonomousDysonPhillips.nonautonomous_bounded_perturbation"),
                H("Ordered series, joint continuity and unrestricted mild uniqueness"),
                StatementSource.FromAuthor(EvolutionStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The function evolution(S,B,t,r), denoted U(t,r), is one bounded complex-linear map for each pair of times, defined independently of a horizon or chosen majorant. On every admissible triangle, the very D(n,t,r,x) terms in the displayed recurrence satisfy the factorial estimate and HasSum to U(t,r)x for every x. Vectorwise sums are linear and exponentially bounded, which assembles the single complex-linear map.")),
                    Paragraph(Text("For each fixed x, U(t,r)x is jointly continuous on the entire closed triangle, including its diagonal and T=0. Extend B by its interval projection, prove joint continuity of the parameterized integrals with both endpoints varying, and use equality of the actual terms on the triangle. A uniform exponential-series majorant passes joint continuity to the sum. Dominated summation inside the actual Bochner integral proves the mild equation.")),
                    Paragraph(Text("For every r in Icc(0,T), initial x and vector function X continuous on Icc(r,T), the mild identity alone implies X(t)=U(t,r)x there. No supplied bound, linearity, Lipschitz condition, derivative or family law on X is assumed. Its difference from the series is continuous on a compact interval and therefore has an internal finite norm bound. It equals all its own causal iterates. Applying the same factorial estimate to that residual and taking the factorial limit proves uniqueness. Splitting at an intermediate time and applying trajectory uniqueness proves the full three-time cocycle.")),
                    Paragraph(Text("Positive-order terms vanish on the diagonal and U(r,r) is the identity, including on the zero space. M=0, x=0 and T=0 are included. Zero B gives U(t,r)=A(t-r). The argument does not use norm(identity)=1. The output has an exponential operator-norm bound for every admissible M; no contractivity of U is asserted.")),
                    Paragraph(Text("Changing B outside Icc(r,t) leaves U(t,r) unchanged, even if the changed function is irregular there. This proves compatibility on overlapping finite horizons or coefficient extensions: their values agree wherever the connecting interval lies in the overlap and their coefficients agree there. For B(s)=Z on the horizon, the theorem identifies U(t,r)x with the original autonomous dysonSum(A,Z,t-r,x), using the same S and Z. Translation of each Bochner recurrence proves the term correspondence before summation. This identity holds for every finite horizon and every admissible M.")),
                    Paragraph(Text("The native contraction-semigroup action and the autonomous DysonPhillipsPerturbation construction supply the reused interfaces and series method. The latter retains Zayn Blore's Apache-2.0 source at revision ca3edfd7a5576d6c4e188501f9abb7c3f38ccd7f, CsdLean4/Mathlib/Analysis/Semigroup/BoundedPerturbation.lean, with its license in docs/reports/qmutualinfo/csd-lean4-LICENSE.txt. Mathlib supplies the scalar factorial integral, exponential series and Bochner convergence results. This is a nonautonomous extension of the classical bounded-perturbation construction. No originality claim or exact correspondence of the complete telescope with a single primary-source theorem is asserted.")),
                    Paragraph(Text("The classical nonautonomous forward core is given by Engel and Nagel, One-Parameter Semigroups for Linear Evolution Equations, Section VI.9 by Schnaubelt: Definition VI.9.2 (page 479), Theorem VI.9.19 and Corollary VI.9.20 (pages 488–489), with left mild equation (9.6). Rabiger, Rhandi, Schnaubelt and Voigt, Non-autonomous Miyadera perturbations, Theorem 3.4 (preprint pages 9–10), Corollary 3.5 and Remark 3.6 (page 15), give the finite-interval construction and left mild equation (3.9). These sources supply forward existence, joint strong continuity, identity and cocycle in their evolution-family scopes; the Engel–Nagel corollary assumes globally bounded strongly continuous coefficients. The prescribed series and sharp bounds, unrestricted vector-trajectory uniqueness, degenerate cases and same-data autonomous comparison are proved here, with no claim that those passages supply the complete combined statement.")),
                    Paragraph(Text("No bounded generator, domain, positivity, adjoint or physical interpretation enters the hypotheses or conclusions."))),
                DescribeRole.Theorem),
            Paragraph(Text("Application: the resonant two-level pulse.")),
            Paragraph(Text("This application combines existing evolution, Pauli and calculus results. Write A=M₂(ℂ), I for the identity matrix, and † for the conjugate transpose. All matrix norms are the spectral/L² operator norm induced by the Euclidean norm on ℂ². Use ℏ=1 and angular frequency ω. Fix T>=0, ω>0, a constant real phase φ, and M>=0. Let Ω and ΩPrime be real functions continuous on [0,T], with HasDerivAt Ω (ΩPrime(s)) at every s in (0,T), and assume |Ω(s)|<=M throughout [0,T]. Below Ω'(s) denotes this supplied ΩPrime(s). These C¹ interval hypotheses are stronger than mere continuity: continuity suffices for native existence, while the quantitative estimate uses the derivative and its integral. No condition outside [0,T], endpoint vanishing, or sign condition on Ω is imposed.")),
            Paragraph(Text("Let X=[[0,1],[1,0]], Y=[[0,-i],[i,0]], and Z=[[1,0],[0,-1]]. Define Hlab(t)=(ω/2)Z+Ω(t)cos(ωt+φ)X. To instantiate nonautonomous_bounded_perturbation, take its Banach space E to be A, its contraction semigroup S(q) to be the identity continuous linear map for every q, and its coefficient B_H(s)(x)=(-i)(H(s)x). Its initial vector is x=I and initial time r=0. Thus U_H(t)=NonautonomousDysonPhillips.evolution(S,B_H,t,0)(I), and U_lab=U_Hlab. The coefficient is continuous and has a finite norm bound on the compact interval, as required by the supplier. This is the original ordered evolution evaluated at I; no exponential of an integrated laboratory Hamiltonian is substituted.")),
            Paragraph(Text("The supplied ordered series and mild uniqueness give continuity on [0,T], U_H(0)=I, and U_H(t)=I+∫₀ᵗ(-i)H(s)U_H(s) ds. The fundamental theorem of calculus gives U_H'(t)=(-i)H(t)U_H(t) for 0<t<T. For Hermitian H, the star and product derivative rules give (U_H†U_H)'=(iU_H†H)U_H+U_H†(-iHU_H)=0. Continuity on the closed interval and the integral form of the fundamental theorem therefore yield U_H(t)†U_H(t)=I for every 0<=t<=T. A square finite matrix with this left inverse is unitary. In particular, the actual laboratory path is unitary; this is a consequence of the native ODE and Hermiticity, rather than an extra path assumption.")),
            Paragraph(Text("Set V(t)=exp(+iωtZ/2), U₂(t)=V(t)U_lab(t), and H₂(t)=V(t)Hlab(t)V(t)†-(ω/2)Z. The existing hamiltonianPropagator realizes V by choosing Hamiltonian -(ω/2)Z. The exponential of a skew-adjoint matrix is unitary, and V'(t)=i(ω/2)ZV(t). In the product derivative V'U_lab+VU_lab', insert V†V=I without changing factor order. This yields U₂'(t)=(-i)H₂(t)U₂(t), U₂(0)=I, and unitarity of U₂ throughout [0,T].")),
            Paragraph(Text("The diagonal representation V(t)=diag(exp(iωt/2),exp(-iωt/2)) gives VXV†=cos(ωt)X-sin(ωt)Y, while VZV†=Z. Product-to-sum identities applied to Ω(t)cos(ωt+φ)VXV† give H₂(t)=H₁(t)+Δ(t), where H₁(t)=(Ω(t)/2)Aφ, Aφ=cosφ X+sinφ Y, and Δ(t)=(Ω(t)/2)(cos(2ωt+φ)X-sin(2ωt+φ)Y). This computation keeps the laboratory frame multiplication on the left and the adjoint on the right; it does not require Hamiltonians at different times to commute.")),
            Paragraph(Text("The arbitrary constant phase matters to the axis: at φ=π/2, H₁(t)=(Ω(t)/2)Y and H₂(t)=(Ω(t)/2)((1-cos(2ωt))Y-sin(2ωt)X). Noncommuting laboratory data occur already for Ω(s)=1+s, ω=π/2, φ=0 on [0,1]: Hlab(0)Hlab(1) differs from Hlab(1)Hlab(0). The rotating frame construction and the error estimate apply to these data.")),
            Paragraph(Text("To identify the comparison evolution, put a(t)=∫₀ᵗ Ω(s)/2 ds and W(t)=exp(-ia(t)Aφ), using hamiltonianPropagator(Aφ,a(t)). The interval primitive is continuous on [0,T], has derivative Ω(t)/2 on (0,T), and vanishes at zero. The derivative of the constant-generator exponential and the chain rule give W'(t)=(-i)H₁(t)W(t), W(0)=I. Integrating this equation gives the very mild equation for coefficient B_H₁. The unrestricted uniqueness clause of nonautonomous_bounded_perturbation then identifies W(t)=U_H₁(t) for every t in [0,T]. Write this native path as U₁(t). Its pulse-area representation follows from uniqueness; it is not used to define or replace the noncommuting laboratory path.")),
            Paragraph(Text("For the comparison step, let H₁,H₂ be continuous Hermitian matrix paths and U₁,U₂ their continuous unitary solutions with Uⱼ(0)=I and Uⱼ'=(-i)HⱼUⱼ on (0,T). Define P(r)=∫₀ʳ(H₂(s)-H₁(s)) ds, so P(0)=0 and P'=H₂-H₁. For fixed t in [0,T], differentiate G(s)=U₁(t)U₁(s)†(I+iP(s))U₂(s) on (0,t). The product and star rules, with no commutation of matrices, give G'(s)=-U₁(t)U₁(s)†(H₁(s)P(s)-P(s)H₂(s))U₂(s). Its endpoints are G(0)=U₁(t) and G(t)=U₂(t)+iP(t)U₂(t).")),
            Paragraph(Text("The fundamental theorem on [0,t] therefore gives the exact integral-action identity U₂(t)-U₁(t)=(-i)P(t)U₂(t)-∫₀ᵗ U₁(t)U₁(s)†(H₁(s)P(s)-P(s)H₂(s))U₂(s) ds. Unitary multiplication preserves the spectral norm, |-i|=1, and ||H₁P-PH₂||<=||P||(||H₁||+||H₂||). Thus ||U₂(t)-U₁(t)||<=||P(t)||+∫₀ᵗ||P(s)||( ||H₁(s)||+||H₂(s)|| ) ds. The factor order H₁P-PH₂ is part of the identity, not an interchangeable scalar product.")),
            Paragraph(Text("In the pulse application H₂-H₁=Δ. Set θ(s)=2ωs+φ and Q(s)=sinθ(s)X+cosθ(s)Y=A(π/2-θ(s)). For any real α, Aα=[[0,exp(-iα)],[exp(iα),0]] is Hermitian and Aα†Aα=I, hence ||Aα||=1. Consequently ||Q(s)||=1, ||H₁(s)||=|Ω(s)|/2 and ||Δ(s)||=|Ω(s)|/2. This identifies the norms in the finite matrix representation with the intended spectral operator norms.")),
            Paragraph(Text("The scalar sine and cosine derivative rules give Q'(s)=2ω(cosθ(s)X-sinθ(s)Y), so Δ(s)=(Ω(s)/(4ω))Q'(s). Differentiate F(s)=(Ω(s)/(4ω))Q(s). Its derivative is Δ(s)+(Ω'(s)/(4ω))Q(s). Integrating F' on the closed interval gives the integration-by-parts primitive P(t)=(Ω(t)/(4ω))Q(t)-(Ω(0)/(4ω))Q(0)-∫₀ᵗ(Ω'(s)/(4ω))Q(s) ds. Both endpoints are retained.")),
            Paragraph(Text("Since 4ω>0, the endpoint and variation terms yield ||P(t)||<=(|Ω(t)|+|Ω(0)|+∫₀ᵗ|Ω'(s)| ds)/(4ω)<=(2M+∫₀ᵗ|Ω'(s)| ds)/(4ω). Put K_T=(2M+∫₀ᵀ|Ω'(s)| ds)/(4ω). Nonnegativity of |Ω'| gives ||P(s)||<=K_T for every s in [0,T]. Also H₂=H₁+Δ implies ||H₁(s)||+||H₂(s)||<=3|Ω(s)|/2. Inserting these bounds in the integral-action inequality first yields ||U₂(t)-U₁(t)||<=K_T(1+(3/2)∫₀ᵗ|Ω(s)| ds).")),
            Paragraph(Text("Extending the last nonnegative integral to T gives, for every 0<=t<=T, ||U₂(t)-U₁(t)||<=((2M+∫₀ᵀ|Ω'(s)| ds)/(4ω))(1+(3/2)∫₀ᵀ|Ω(s)| ds). Equivalently, the same error bound compares U_lab(t) with V(t)†U₁(t), by unitary invariance. For Ω(s)=1+s on [0,1], choose M=2 and Ω'=1; the integrals are 1 and 3/2, respectively, giving the explicit bound 65/(16ω) for every t in [0,1].")),
            Paragraph(Text("The closed endpoints require no extra derivative premise. At t=0 both paths are I; the horizon T=0 is included. For the zero envelope, the right-hand side is zero with M=0 and Ω'=0, and U₂(t)=U₁(t)=I throughout the interval. For fixed finite T, envelope, derivative and majorant, the displayed right-hand side tends to zero as ω tends to positive infinity, uniformly for t in [0,T]. It can exceed the trivial unitary distance bound 2 at other parameter values without contradiction; the smaller of these valid bounds is then available.")),
            Paragraph(Text("The original suppliers are NonautonomousDysonPhillips.nonautonomous_bounded_perturbation for the series, mild equation and uniqueness; ProjectionProbabilityFlow.hamiltonianGenerator and hamiltonianPropagator for the constant Hamiltonian exponential; FiniteDimensional.qubitX, qubitZ and qubit_weyl_star, the existing pauliMatrix definition, and StabilizerPovmMaximalEntanglementRefutation.pauli_hermitian for the Pauli data. Mathlib supplies intervalIntegral.continuousOn_primitive_interval', integral_hasDerivAt_right and integral_eq_sub_of_hasDerivAt_of_le, HasDerivAt.mul, HasDerivAt.star and the scalar chain rules, hasDerivAt_exp_smul_const', Matrix.exp_diagonal, Matrix.mem_unitaryGroup_iff', NormedSpace.exp_mem_unitary_of_mem_skewAdjoint, the CStarRing unitary norm identities and the interval-integral norm and monotonicity inequalities. The integral-action and oscillatory integration-by-parts steps above are applications of these providers.")),
            Paragraph(Text("The literature source is Daniel Burgarth, Paolo Facchi, Giovanni Gramegna and Kazuya Yuasa, One bound to rule them all: from Adiabatic to Zeno, arXiv:2111.08961v2 (https://arxiv.org/html/2111.08961v2), Lemma 1, equations (2.3)–(2.6), and Section 3.3.1, equations (3.27)–(3.34). The paper's S₂₁ is P here; its H₁,H₂,U₁,U₂ have the same order in the integral-action identity. For its envelope example take g=Ω, ω₀=ω and detuning δ=0; its averaged Hamiltonian is then H₁ at φ=0. The arbitrary fixed phase and the explicit C¹ endpoint/variation estimate here are derived applications, rather than literal quotations of the paper's zero-phase model. No literature novelty is claimed.")),
            Paragraph(Text("The result concerns the declared resonant two-level mathematical model with constant phase on a fixed finite horizon. It establishes no hardware implementation, detuning correction, leakage bound, arbitrary phase path, or estimate uniform on unbounded horizons. The evolution and norm correspondence above specify the exact meaning of the rotating-wave error.")))));

    private static Formula Real => Call("Real");
    private static Formula Nat => Call("Nat");
    private static Formula E => F.Id("E");
    private static Formula S => F.Id("S");
    private static Formula B => F.Id("B");
    private static Formula T => F.Id("T");
    private static Formula M => F.Id("M");
    private static Formula R => F.Id("r");
    private static Formula Time => F.Id("t");
    private static Formula X => F.Id("x");
    private static Formula Zero => new Formula.Number(0);
    private static Formula One => new Formula.Number(1);
    private static Formula Clm => Call("ComplexCLM", E, E);
    private static Formula Family => new Formula.TypeArrow(Real, Clm);
    private static Formula Curve => new Formula.TypeArrow(Real, E);
    private static Formula Interval(Formula a, Formula b) => Call("Icc",a,b);
    private static Formula All(string n, Formula d, Formula b) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), d, b);
    private static Formula At(Formula f, params Formula[] xs) => new Formula.Apply(f,[.. xs]);
    private static Formula Lam(string n, Formula d, Formula b) => Seq(Grp(F.Id(n),Colon,d),Mapsto,Sp,b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a,FormulaRelationOperator.LessThanOrEqual,b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a,FormulaLogicOperator.Implies,b);
    private static Formula Conj(params Formula[] fs)
    {
        Formula r=fs[^1];
        for(int i=fs.Length-2;i>=0;--i) r=new Formula.Logic(fs[i],FormulaLogicOperator.And,r);
        return r;
    }
    private static Formula Scope(bool complete, Formula body)
    {
        Formula scoped=All("S",Call("Contraction",E),All("B",Family,body));
        if(complete) scoped=Seq(OpenBracket,Call("CompleteSpace",E),CloseBracket,Sp,scoped);
        return All("u",Call("Universe"),All("E",Call("Type",F.Id("u")),Seq(
            OpenBracket,Call("NormedAddCommGroup",E),CloseBracket,Sp,
            OpenBracket,Call("NormedSpace",Call("Complex"),E),CloseBracket,Sp,scoped)));
    }
    private static Formula InInterval(string name, Formula a, Formula b, Formula body) =>
        All(name,Real,Imp(Call("Mem",F.Id(name),Interval(a,b)),body));
    private static Formula Action(Formula t, Formula x) => At(Call("action",S,t),x);
    private static Formula Term(Formula n, Formula t, Formula r, Formula x) => Call("term",S,B,n,t,r,x);
    private static Formula U(Formula t, Formula r) => Call("evolution",S,B,t,r);
    private static Formula Value(Formula t, Formula r, Formula x) => At(U(t,r),x);
    private static Formula Triangle(Formula t, Formula r) => Conj(Le(Zero,r),Le(r,t),Le(t,T));
    private static Formula OnTriangle(Formula body) => All("t",Real,All("r",Real,Imp(Triangle(Time,R),body)));
    private static Formula Bound(Formula a, Formula b) => InInterval("s",a,b,
        Le(new Formula.Norm(At(B,F.Id("s"))),M));
    private static Formula Integral(Formula t, Formula r, Formula values) => Call("intervalIntegral",Call("volume"),r,t,
        Lam("s",Real,Action(Subtract(t,F.Id("s")),At(At(B,F.Id("s")),values))));
    private static Formula Majorant(Formula n, Formula t, Formula r, Formula x) => Multiply(
        new Formula.Fraction(Multiply(new Formula.Power(M,n),new Formula.Power(Subtract(t,r),n)),Call("factorial",n)),
        new Formula.Norm(x));
    private static Formula Definitions()
    {
        Formula n=F.Id("n"),s=F.Id("s"),v=F.Id("v");
        Formula body=Conj(
            Equal(Call("causal",S,B,R,v,Time),Integral(Time,R,At(v,s))),
            Equal(Call("causalIterate",S,B,R,v,Zero,Time),At(v,Time)),
            Equal(Call("causalIterate",S,B,R,v,Add(n,One),Time),
                Call("causal",S,B,R,Lam("s",Real,Call("causalIterate",S,B,R,v,n,s)),Time)),
            Equal(Term(Zero,Time,R,X),Action(Subtract(Time,R),X)),
            Equal(Term(Add(n,One),Time,R,X),Integral(Time,R,Term(n,s,R,X))),
            Equal(Call("sum",S,B,Time,R,X),Call("tsum",Lam("n",Nat,Term(n,Time,R,X)))));
        return Scope(true,All("r",Real,All("t",Real,All("n",Nat,All("x",E,All("v",Curve,body))))));
    }
    private static Formula IterateStatement()
    {
        Formula c=F.Id("C"),v=F.Id("v"),n=F.Id("n");
        Formula premises=Conj(Le(R,T),Call("ContinuousOn",B,Interval(R,T)),Le(Zero,M),Bound(R,T),
            Call("ContinuousOn",v,Interval(R,T)),InInterval("s",R,T,Le(new Formula.Norm(At(v,F.Id("s"))),c)));
        Formula conclusion=All("n",Nat,InInterval("t",R,T,
            Le(new Formula.Norm(Call("causalIterate",S,B,R,v,n,Time)),Multiply(c,
                new Formula.Fraction(new Formula.Power(Multiply(M,Subtract(Time,R)),n),Call("factorial",n))))));
        return Scope(false,All("r",Real,All("T",Real,All("M",Real,All("C",Real,All("v",Curve,
            Imp(premises,conclusion)))))));
    }
    private static Formula EvolutionStatement()
    {
        Formula n=F.Id("n"),s=F.Id("s"),other=F.Id("Q"),bz=F.Id("Z");
        Formula estimate=All("n",Nat,OnTriangle(All("x",E,
            Le(new Formula.Norm(Term(n,Time,R,X)),Majorant(n,Time,R,X)))));
        Formula series=OnTriangle(All("x",E,Call("HasSum",Lam("n",Nat,Term(n,Time,R,X)),Value(Time,R,X))));
        Formula joint=All("x",E,Call("ContinuousOn",Lam("p",Call("Prod",Real,Real),
            Value(Call("fst",F.Id("p")),Call("snd",F.Id("p")),X)),Call("triangle",T)));
        Formula mild=OnTriangle(All("x",E,Equal(Value(Time,R,X),
            Add(Action(Subtract(Time,R),X),Integral(Time,R,Value(s,R,X))))));
        Formula diagonal=InInterval("r",Zero,T,Equal(U(R,R),Call("id",Call("Complex"),E)));
        Formula competitor=Conj(Call("ContinuousOn",F.Id("X"),Interval(R,T)),
            InInterval("t",R,T,Equal(At(F.Id("X"),Time),
                Add(Action(Subtract(Time,R),X),Integral(Time,R,At(F.Id("X"),s))))));
        Formula unique=InInterval("r",Zero,T,All("X",Curve,All("x",E,Imp(competitor,
            InInterval("t",R,T,Equal(At(F.Id("X"),Time),Value(Time,R,X)))))));
        Formula cocycle=All("r",Real,All("s",Real,All("t",Real,Imp(
            Conj(Le(Zero,R),Le(R,s),Le(s,Time),Le(Time,T)),Equal(Call("comp",U(Time,s),U(s,R)),U(Time,R))))));
        Formula growth=OnTriangle(Le(new Formula.Norm(U(Time,R)),Call("exp",Multiply(M,Subtract(Time,R)))));
        Formula positiveDiagonal=All("n",Nat,All("r",Real,All("x",E,Equal(Term(Add(n,One),R,R,X),Zero))));
        Formula locality=All("Q",Family,OnTriangle(Imp(Call("EqOn",B,other,Interval(R,Time)),
            Equal(U(Time,R),Call("evolution",S,other,Time,R)))));
        Formula constant=All("Z",Clm,Imp(Call("EqOn",B,Lam("s",Real,bz),Interval(Zero,T)),
            OnTriangle(All("x",E,Equal(Value(Time,R,X),
                Call("dysonSum",Call("action",S),bz,Subtract(Time,R),X))))));
        Formula zero=Imp(Call("EqOn",B,Lam("s",Real,Zero),Interval(Zero,T)),
            OnTriangle(Equal(U(Time,R),Call("action",S,Subtract(Time,R)))));
        return Scope(true,All("T",Real,All("M",Real,Imp(
            Conj(Le(Zero,T),Call("ContinuousOn",B,Interval(Zero,T)),Le(Zero,M),Bound(Zero,T)),
            Conj(estimate,series,joint,mild,diagonal,unique,cocycle,growth,positiveDiagonal,locality,constant,zero)))));
    }
}
