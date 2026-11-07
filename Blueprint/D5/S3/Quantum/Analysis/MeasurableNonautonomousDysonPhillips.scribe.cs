using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis;

internal sealed class MeasurableNonautonomousDysonPhillipsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Vectorwise almost everywhere strongly measurable bounded-operator coefficients, controlled by any nonnegative integrable scalar function, generate the original nonautonomous Dyson–Phillips evolution on arbitrary complex Banach spaces.",
        H("Measurable coefficients and the integrable Dyson–Phillips clock"), Blocks(
            Paragraph(Text("Let E be a complex normed space, in an arbitrary universe. The evolution and series assertions assume E is complete; the zero space is included. Let S be the original NonautonomousDysonPhillips.Contraction: a strongly continuous semigroup of bounded complex-linear contractions on nonnegative real times, with identity at zero. Write A(t)=S.action(t)=S.operator(Real.toNNReal(t)). All integrals use real Lebesgue measure volume and are vector Bochner integrals unless their integrand is real. No continuity of A in operator norm is assumed.")),
            Paragraph(Text("For real r<=H, write I(r,H)=Icc(r,H) and mu(r,H)=volume restricted to I(r,H). The condition Meas(B,r,H) means that s maps to B(s)x is AE strongly measurable for mu(r,H), separately for every x in E. Control(B,g,r,H) means that g is real and IntegrableOn I(r,H), and that 0<=g(s) and norm(B(s))<=g(s) at every s in that closed interval. Neither condition asserts operator-valued measurability of B. The clock G(g,r,t) is the scalar interval integral of g from r to t.")),
            new DocumentBlock.DisplayFormula(Definitions()),
            Describe.Lean(DescribeId.Create("measurable-path-evaluation"), Handle("aestronglyMeasurable_evaluation"),
                H("Evaluation along an almost everywhere strongly measurable path"),
                StatementSource.FromAuthor(Evaluation()), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The source is any measurable space alpha in any universe, with any measure mu. E need not be complete or separable. If every fixed-vector slice B(s)x is AE strongly measurable and v is AE strongly measurable for that same measure, then B(s)v(s) is AE strongly measurable. Approximate an AE representative of v by simple functions. For a simple function, measurable piecewise selection reduces evaluation to finitely many fixed-vector slices. Pointwise continuity of each bounded linear map B(s) passes the countable approximation to the limit. This uses no common exceptional set for all vectors."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("integrable-clock-moment"), Handle("clock_moment"),
                H("The exact factorial moment of an L1 clock"),
                StatementSource.FromAuthor(Moment()), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("This scalar assertion assumes only real r<=t and g integrable on Icc(r,t); g need not be nonnegative. Its primitive is absolutely continuous. Powers remain absolutely continuous by multiplication, and the almost everywhere derivative and the scalar fundamental theorem give the displayed identity. The weighted integrand is actually interval integrable. There is no division by g, so zeros of g and a zero interval require no exceptional case."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("measurable-causal-regularity"), Handle("causal_regular"),
                H("Actual integrability and continuity of causal integration"),
                StatementSource.FromAuthor(Regular()), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("On Icc(r,H), take vectorwise AE measurability of B, an integrable real g with norm(B(s))<=g(s), and a continuous vector path v. The conclusion gives continuity of the original causal output on that interval and actual IntervalIntegrable of every original integrand up to each t in the interval. There is no extra hypothesis r<=H; when the interval is empty its conclusions have their ordinary empty-domain meaning. Compactness internally bounds v. Path evaluation and scalar domination make B(s)v(s) integrable. Extend that integrable vector function by zero outside the interval and apply dominated convergence to A(t-s) acting on it, with both parameter and upper endpoint varying."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("measurable-causal-iterate-bound"), Handle("measurable_causal_iterate_bound"),
                H("Weighted factorial control of the original causal iterates"),
                StatementSource.FromAuthor(Iterate()), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For arbitrary real r<=H, Meas(B,r,H), every Control(B,g,r,H), a continuous v on Icc(r,H), and any real C bounding norm(v(s)) there, every natural n and t in Icc(r,H) satisfy the estimate for the original causalIterate. C has no supplied sign condition; evaluating its path bound at r implies C>=0. Actual causal continuity and interval integrability propagate at every stage. Induction combines contractivity, the operator majorant and the exact scalar moment. The recursion retains absolute coefficient time and the noncommuting left order A(t-s) after B(s). It never divides by C, a vector norm or g."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("measurable-original-series"), Handle("measurable_series"),
                H("Absolute norm convergence and the actual vector sum"),
                StatementSource.FromAuthor(Series()), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("With the same arbitrary ordered horizon and every admissible control, the original term sequence is norm summable and HasSum to the original sum. Apply the weighted iterate estimate to the initial orbit, whose norm is at most norm(x), and compare with the scalar exponential series. This assertion refers to the actual Bochner terms, rather than a separately postulated solution."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("measurable-residual-uniqueness"), Handle("continuous_residual_eq_zero"),
                H("Unrestricted vanishing of a continuous causal residual"),
                StatementSource.FromAuthor(Residual()), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Any continuous Y on Icc(r,H) which equals its own original causal integral vanishes there. No bound on Y is supplied. Compactness supplies an internal finite real bound, and the residual identity makes every original causal iterate agree with Y. The same weighted factorial estimate tends to zero as n grows. This provides the uniqueness mechanism independently of series convergence."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("coefficient-indexed-evolution"), Handle("measurableEvolution"),
                H("One linear family before horizons and controls"),
                StatementSource.FromAuthor(FamilyDefinition()), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For each B,t,r, choose a bounded complex-linear map whose action on every x equals the original sum whenever such a map exists; otherwise choose the zero map. Equality on all vectors makes any such realization unique. This definition takes only S,B,t,r. It has no horizon or scalar control argument and no strong-continuity gate. The construction below supplies a realization on every eligible ordered interval, using integrable linear recurrences and the exponential norm estimate."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("full-measurable-evolution"), Handle("measurable_evolution"),
                H("The full measurable-coefficient evolution family"),
                StatementSource.FromAuthor(Evolution()), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("There exists one family Phi indexed by all coefficients B before any horizon T or control g is selected. It is realized by measurableEvolution(S). For every T>=0, every Meas(B,0,T) and every Control(B,g,0,T), all the following clauses hold on the closed triangle Delta(T)={(t,r):0<=r<=t<=T}. The family consists simultaneously of bounded complex-linear maps. The original causal integrands along every continuous path and every original recursive term are actually interval integrable. The original terms satisfy the clock factorial estimate, are norm summable and HasSum to Phi(B,t,r)x.")),
                    Paragraph(Text("For each x, Phi(B,t,r)x is jointly continuous on the entire closed triangle, including its diagonal. To establish term continuity, set the coefficient and control to zero outside Icc(0,T). For this auxiliary coefficient, a finite whole-line L1 norm gives a uniform geometric bound for each fixed term index, including reversed endpoints. Dominated parameter integration proves global joint continuity of these auxiliary terms. Locality identifies them with the original terms on the triangle. The sharper factorial clock bound then gives uniform convergence there. This argument requires no operator-valued measurability, separability or common exceptional set over all vectors.")),
                    Paragraph(Text("Dominated summation inside the original vector integral proves the actual mild equation. Diagonal values are the identity and all positive-order diagonal terms vanish. Any continuous vector path X on Icc(r,T) satisfying that same mild identity with initial vector x agrees with Phi(B,t,r)x. It need not be supplied with a norm bound, linearity, a Lipschitz property, a derivative or generator-domain membership. Subtract the constructed solution and use the continuous causal residual theorem. Splitting the actual integral at s, using the original semigroup law and then this unrestricted uniqueness gives Phi(B,t,s) composed with Phi(B,s,r)=Phi(B,t,r).")),
                    Paragraph(Text("For every admissible g on this same family, norm(Phi(B,t,r))<=exp(G(g,r,t)). Since the definition has no horizon or control parameter, choices of eligible horizons and controls give the same maps on overlaps. Pointwise equality of B and any Q on the actual interval Icc(r,t) implies equality of their maps at (t,r); Q need not be regular outside that interval. Continuous-vector coefficients agree with the existing StrongNonautonomousDysonPhillips.strongEvolution on their eligible horizon. A coefficient equal to a constant Z on the horizon agrees, for the same S and Z, with the original autonomous DysonPhillipsPerturbation.dysonSum(A,Z,t-r,x). Zero coefficients recover A(t-r).")),
                    Paragraph(Text("The quantifiers include T=0, g=0, x=0, the zero Banach space and n=0, with the usual zeroth-power convention. No proof uses norm(identity)=1. In particular g=0 forces all positive-order terms to vanish and recovers the free evolution. No finite-dimensional assumption, boundedness or strict positivity of g, additional joint-measurability premise, or regularity outside the eligible horizon is present.")),
                    Paragraph(Text("The vector Bochner recurrence, time translation for constant coefficients and zero-coefficient identity are the existing NonautonomousDysonPhillips objects. The series and compact-residual method follows the Apache-2.0 Dyson–Phillips development by Zayn Blore cited in DysonPhillipsPerturbation, CsdLean4/Mathlib/Analysis/Semigroup/BoundedPerturbation.lean at revision ca3edfd7a5576d6c4e188501f9abb7c3f38ccd7f, with its license in docs/reports/qmutualinfo/csd-lean4-LICENSE.txt. Mathlib supplies AE simple approximation, Bochner dominated convergence, absolute continuity, the scalar fundamental theorem and the exponential series. This is an integrable-control extension of the classical Volterra construction; no literature-priority assertion is made."))), DescribeRole.Theorem))));

    private static DeclarationHandle Handle(string name) => DeclarationHandle.Create("D5/S3/Quantum/Analysis/MeasurableNonautonomousDysonPhillips."+name);
    private static Formula Real => Call("Real");
    private static Formula Nat => Call("Nat");
    private static Formula E => F.Id("E");
    private static Formula S => F.Id("S");
    private static Formula B => F.Id("B");
    private static Formula G => F.Id("g");
    private static Formula R => F.Id("r");
    private static Formula T => F.Id("t");
    private static Formula Hn => F.Id("H");
    private static Formula Horizon => F.Id("T");
    private static Formula X => F.Id("x");
    private static Formula Zero => new Formula.Number(0);
    private static Formula One => new Formula.Number(1);
    private static Formula Clm => Call("ComplexCLM",E,E);
    private static Formula Coeff => new Formula.TypeArrow(Real,Clm);
    private static Formula Curve => new Formula.TypeArrow(Real,E);
    private static Formula Scalar => new Formula.TypeArrow(Real,Real);
    private static Formula All(string n,Formula d,Formula b) => new Formula.Bind(FormulaQuantifier.ForAll,FormulaIdentifier.Create(n),d,b);
    private static Formula Exists(string n,Formula d,Formula b) => new Formula.Bind(FormulaQuantifier.Exists,FormulaIdentifier.Create(n),d,b);
    private static Formula Lam(string n,Formula d,Formula b) => Seq(Grp(F.Id(n),Colon,d),Mapsto,Sp,b);
    private static Formula At(Formula f,params Formula[] xs) => new Formula.Apply(f,[.. xs]);
    private static Formula Imp(Formula a,Formula b) => new Formula.Logic(a,FormulaLogicOperator.Implies,b);
    private static Formula Le(Formula a,Formula b) => new Formula.Relation(a,FormulaRelationOperator.LessThanOrEqual,b);
    private static Formula I(Formula a,Formula b) => Call("Icc",a,b);
    private static Formula In(string n,Formula a,Formula b,Formula body) => All(n,Real,Imp(Call("Mem",F.Id(n),I(a,b)),body));
    private static Formula Conj(params Formula[] fs) { Formula q=fs[^1]; for(int i=fs.Length-2;i>=0;--i) q=new Formula.Logic(fs[i],FormulaLogicOperator.And,q); return q; }
    private static Formula Scope(bool complete,Formula body) {
        Formula q=Seq(OpenBracket,Call("NormedAddCommGroup",E),CloseBracket,Sp,
            OpenBracket,Call("NormedSpace",Call("Complex"),E),CloseBracket,Sp,
            complete?Seq(OpenBracket,Call("CompleteSpace",E),CloseBracket,Sp,body):body);
        return All("u",Call("Universe"),All("E",Call("Type",F.Id("u")),q));
    }
    private static Formula SB(bool complete,Formula body) => Scope(complete,All("S",Call("Contraction",E),All("B",Coeff,body)));
    private static Formula Meas(Formula a,Formula b) => All("z",E,Call("AEStronglyMeasurable",Lam("s",Real,At(At(B,F.Id("s")),F.Id("z"))),Call("restrict",Call("volume"),I(a,b))));
    private static Formula Dom(Formula a,Formula b) => In("s",a,b,Le(new Formula.Norm(At(B,F.Id("s"))),At(G,F.Id("s"))));
    private static Formula Control(Formula a,Formula b) => Conj(Call("IntegrableOn",G,I(a,b),Call("volume")),In("s",a,b,Le(Zero,At(G,F.Id("s")))),Dom(a,b));
    private static Formula Clock(Formula a,Formula b) => Call("intervalIntegral",Call("volume"),a,b,G);
    private static Formula Weight(Formula n,Formula a,Formula b) => new Formula.Fraction(new Formula.Power(Clock(a,b),n),Call("factorial",n));
    private static Formula Action(Formula t,Formula x) => At(Call("action",S,t),x);
    private static Formula Term(Formula n,Formula t,Formula r,Formula x) => Call("term",S,B,n,t,r,x);
    private static Formula Sum(Formula t,Formula r,Formula x) => Call("sum",S,B,t,r,x);
    private static Formula U(Formula t,Formula r) => At(F.Id("Phi"),B,t,r);
    private static Formula Value(Formula t,Formula r,Formula x) => At(U(t,r),x);
    private static Formula Integrand(Formula t,Formula v) => Lam("s",Real,Action(Subtract(t,F.Id("s")),At(At(B,F.Id("s")),At(v,F.Id("s")))));
    private static Formula Integral(Formula t,Formula v) => Call("intervalIntegral",Call("volume"),R,t,Integrand(t,v));
    private static Formula Int(Formula t,Formula v) => Call("IntervalIntegrable",Integrand(t,v),Call("volume"),R,t);
    private static Formula Triangle(Formula t,Formula r) => Conj(Le(Zero,r),Le(r,t),Le(t,Horizon));
    private static Formula OnTriangle(Formula b) => All("t",Real,All("r",Real,Imp(Triangle(T,R),b)));
    private static Formula HorizonScope(Formula b) => SB(true,All("r",Real,All("H",Real,All("g",Scalar,Imp(Conj(Le(R,Hn),Meas(R,Hn),Control(R,Hn)),b)))));
    private static Formula Evaluation() {
        Formula a=F.Id("alpha"),mu=F.Id("mu"),v=F.Id("v");
        return Scope(false,All("w",Call("Universe"),All("alpha",Call("Type",F.Id("w")),Seq(
            OpenBracket,Call("MeasurableSpace",a),CloseBracket,Sp,All("mu",Call("Measure",a),
            All("B",new Formula.TypeArrow(a,Clm),All("v",new Formula.TypeArrow(a,E),Imp(Conj(
                All("x",E,Call("AEStronglyMeasurable",Lam("s",a,At(At(B,F.Id("s")),X)),mu)),
                Call("AEStronglyMeasurable",v,mu)),Call("AEStronglyMeasurable",Lam("s",a,At(At(B,F.Id("s")),At(v,F.Id("s")))),mu)))))))));
    }
    private static Formula Moment() {
        Formula n=F.Id("n"),s=F.Id("s");
        Formula f=Lam("s",Real,Multiply(At(G,s),Weight(n,R,s)));
        return All("r",Real,All("t",Real,All("g",Scalar,Imp(Conj(Le(R,T),Call("IntegrableOn",G,I(R,T),Call("volume"))),All("n",Nat,Conj(
            Call("IntervalIntegrable",f,Call("volume"),R,T),Equal(Call("intervalIntegral",Call("volume"),R,T,f),Weight(Add(n,One),R,T))))))));
    }
    private static Formula RegularConclusion(Formula end) {
        Formula v=F.Id("v");
        return All("v",Curve,Imp(Call("ContinuousOn",v,I(R,end)),Conj(Call("ContinuousOn",Call("causal",S,B,R,v),I(R,end)),In("t",R,end,Int(T,v)))));
    }
    private static Formula Regular() => SB(false,All("r",Real,All("H",Real,All("g",Scalar,Imp(Conj(Meas(R,Hn),Call("IntegrableOn",G,I(R,Hn),Call("volume")),Dom(R,Hn)),RegularConclusion(Hn))))));
    private static Formula Iterate() {
        Formula v=F.Id("v"),c=F.Id("C"),n=F.Id("n");
        return HorizonScope(All("v",Curve,All("C",Real,Imp(Conj(Call("ContinuousOn",v,I(R,Hn)),In("s",R,Hn,Le(new Formula.Norm(At(v,F.Id("s"))),c))),
            All("n",Nat,In("t",R,Hn,Le(new Formula.Norm(Call("causalIterate",S,B,R,v,n,T)),Multiply(c,Weight(n,R,T)))))))));
    }
    private static Formula Series() => HorizonScope(In("t",R,Hn,All("x",E,Conj(Call("Summable",Lam("n",Nat,new Formula.Norm(Term(F.Id("n"),T,R,X)))),Call("HasSum",Lam("n",Nat,Term(F.Id("n"),T,R,X)),Sum(T,R,X))))));
    private static Formula Residual() {
        Formula y=F.Id("Y");
        return HorizonScope(All("Y",Curve,Imp(Conj(Call("ContinuousOn",y,I(R,Hn)),In("t",R,Hn,Equal(At(y,T),Call("causal",S,B,R,y,T)))),In("t",R,Hn,Equal(At(y,T),Zero)))));
    }
    private static Formula FamilyDefinition() => SB(true,All("t",Real,All("r",Real,Equal(Call("measurableEvolution",S,B,T,R),
        Call("chooseLinearRealizationOrZero",Lam("x",E,Sum(T,R,X)))))));
    private static Formula Definitions() {
        Formula n=F.Id("n"),v=F.Id("v"),s=F.Id("s");
        Formula identities=Conj(
            Equal(Call("causal",S,B,R,v,T),Integral(T,v)),
            Equal(Call("causalIterate",S,B,R,v,Zero,T),At(v,T)),
            Equal(Call("causalIterate",S,B,R,v,Add(n,One),T),Integral(T,Lam("s",Real,Call("causalIterate",S,B,R,v,n,s)))),
            Equal(Term(n,T,R,X),Call("causalIterate",S,B,R,Lam("s",Real,Action(Subtract(s,R),X)),n,T)),
            Equal(Sum(T,R,X),Call("tsum",Lam("n",Nat,Term(n,T,R,X)))));
        return SB(true,All("r",Real,All("t",Real,All("n",Nat,All("x",E,All("v",Curve,identities))))));
    }
    private static Formula Evolution() {
        Formula n=F.Id("n"),s=F.Id("s"),y=F.Id("X"),q=F.Id("Q"),z=F.Id("Z");
        Formula integrability=In("r",Zero,Horizon,RegularConclusion(Horizon));
        Formula recursive=All("n",Nat,OnTriangle(All("x",E,Int(T,Lam("s",Real,Term(n,s,R,X))))));
        Formula estimate=All("n",Nat,OnTriangle(All("x",E,Le(new Formula.Norm(Term(n,T,R,X)),Multiply(Weight(n,R,T),new Formula.Norm(X))))));
        Formula series=OnTriangle(All("x",E,Conj(Call("Summable",Lam("n",Nat,new Formula.Norm(Term(n,T,R,X)))),Call("HasSum",Lam("n",Nat,Term(n,T,R,X)),Value(T,R,X)))));
        Formula joint=All("x",E,Call("ContinuousOn",Lam("p",Call("Prod",Real,Real),Value(Call("fst",F.Id("p")),Call("snd",F.Id("p")),X)),Call("triangle",Horizon)));
        Formula mild=OnTriangle(All("x",E,Equal(Value(T,R,X),Add(Action(Subtract(T,R),X),Integral(T,Lam("s",Real,Value(s,R,X)))))));
        Formula diagonal=In("r",Zero,Horizon,Equal(U(R,R),Call("id",Call("Complex"),E)));
        Formula unique=In("r",Zero,Horizon,All("X",Curve,All("x",E,Imp(Conj(Call("ContinuousOn",y,I(R,Horizon)),In("t",R,Horizon,Equal(At(y,T),Add(Action(Subtract(T,R),X),Integral(T,y))))),In("t",R,Horizon,Equal(At(y,T),Value(T,R,X)))))));
        Formula cocycle=All("r",Real,All("s",Real,All("t",Real,Imp(Conj(Le(Zero,R),Le(R,s),Le(s,T),Le(T,Horizon)),Equal(Call("comp",U(T,s),U(s,R)),U(T,R))))));
        Formula growth=OnTriangle(Le(new Formula.Norm(U(T,R)),Call("exp",Clock(R,T))));
        Formula diagonalTerms=All("n",Nat,All("r",Real,All("x",E,Equal(Term(Add(n,One),R,R,X),Zero))));
        Formula locality=All("Q",Coeff,OnTriangle(Imp(Call("EqOn",B,q,I(R,T)),Equal(U(T,R),At(F.Id("Phi"),q,T,R)))));
        Formula strong=Imp(All("x",E,Call("ContinuousOn",Lam("s",Real,At(At(B,s),X)),I(Zero,Horizon))),OnTriangle(Equal(U(T,R),Call("strongEvolution",S,B,T,R))));
        Formula constant=All("Z",Clm,Imp(Call("EqOn",B,Lam("s",Real,z),I(Zero,Horizon)),OnTriangle(All("x",E,Equal(Value(T,R,X),Call("dysonSum",Call("action",S),z,Subtract(T,R),X))))));
        Formula zero=Imp(Call("EqOn",B,Lam("s",Real,Zero),I(Zero,Horizon)),OnTriangle(Equal(U(T,R),Call("action",S,Subtract(T,R)))));
        Formula conclusions=Conj(integrability,recursive,estimate,series,joint,mild,diagonal,unique,cocycle,growth,diagonalTerms,locality,strong,constant,zero);
        Formula body=All("B",Coeff,All("T",Real,Imp(Conj(Le(Zero,Horizon),Meas(Zero,Horizon)),All("g",Scalar,Imp(Control(Zero,Horizon),conclusions)))));
        return Scope(true,All("S",Call("Contraction",E),Exists("Phi",new Formula.TypeArrow(Coeff,new Formula.TypeArrow(Real,new Formula.TypeArrow(Real,Clm))),body)));
    }
}
