using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis;

internal sealed class NonautonomousEvolutionStabilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Strong L1 convergence on each fixed vector, under a common integrable scalar majorant, gives uniform strong convergence of the original measurable nonautonomous Banach evolution on the full closed ordered time triangle.",
        H("Strong L1 stability of the original Dyson–Phillips evolution"), Blocks(
            Paragraph(Text("Let E be a complex normed space in any universe, with its normed additive commutative group and complex normed-space structures. The evolution assertions assume CompleteSpace E. The zero space in every universe is included. Let S be the original NonautonomousDysonPhillips.Contraction E: bounded complex-linear contractions on nonnegative real times, with identity at zero, the semigroup law and continuous vector orbits. Write A(t)=S.action(t)=S.operator(Real.toNNReal(t)). All vector integrals below are the original Bochner integrals for real Lebesgue measure volume. Scalar norm integrals are real integrals.")),
            Paragraph(Text("For T>=0, set J=Icc(0,T), mu=volume restricted to J and Delta(T)={(t,r):0<=r<=t<=T}. B_n(s) and B(s) are bounded complex-linear endomorphisms of E for each real absolute time s. Every fixed-vector slice is AE strongly measurable for mu, separately for each n and x. A single arbitrary real function g is integrable on J and satisfies 0<=g(s), norm(B_n(s))<=g(s) and norm(B(s))<=g(s) there. No hypothesis concerns their values outside J.")),
            new DocumentBlock.DisplayFormula(Recurrence()),
            Paragraph(Text("The displayed V_m is exactly NonautonomousDysonPhillips.term, and its sum is exactly NonautonomousDysonPhillips.sum. The order A(t-s) after B(s) is retained. The coefficient-indexed measurableEvolution(S,B,t,r) is the existing bounded linear realization of that sum, defined before any horizon or scalar control. Its original measurableEvolution_apply identity supplies the identification on every eligible ordered interval.")),
            Describe.Lean(DescribeId.Create("compact-range-strong-l1-evaluation"), Handle("uniform_integral_evaluation"),
                H("Uniform evaluation on compact vector ranges"),
                StatementSource.FromAuthor(CompactEvaluation()), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("This assertion needs no completeness. Alpha is any measurable space in any universe, mu is any measure, D_n(s) is a bounded complex-linear endomorphism of E and c is a real mu-integrable function. Require c>=0 almost everywhere, norm(D_n(s))<=c(s) almost everywhere for every n, and AE strong measurability of every fixed-vector slice. If the integral of norm(D_n(s)x) tends to zero for each fixed x, then the conclusion holds for every compact K in E, including the empty compact set. Every AE strongly measurable path v with v(s) in K almost everywhere has actually integrable D_n(s)v(s). For each epsilon>0 a single eventual index bounds its norm integral by epsilon for all these paths at once.")),
                    Paragraph(Text("Compactness gives a finite cover of K by balls of radius delta. For each vector in K choose one center only in the pointwise estimate. Bound norm(D_n(s)v(s)) by the sum of norm(D_n(s)y) over all cover centers y, plus c(s)*delta. Each fixed-center integral tends to zero, while the remainder is delta times the finite integral of c. The pointwise choice needs no measurability assumption, since the finite sum supplies a measurable integrable bound. Actual vector integrability follows from the existing AE strongly measurable evaluation theorem and boundedness of the compact range. This argument neither interchanges a supremum with an integral nor requires a common exceptional set for uncountably many vectors."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("uniform-original-dyson-term-convergence"), Handle("uniform_term_convergence"),
                H("Uniform convergence of each original Dyson term"),
                StatementSource.FromAuthor(EvolutionStatement(false)), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Under the stated horizon, measurability, common-majorant and fixed-vector L1 hypotheses, every fixed natural m and every fixed x satisfy convergence of V_m(B_n;t,r)x to V_m(B;t,r)x uniformly over all (t,r) in Delta(T). The eventual index can depend on m,x and epsilon, and it is independent of both endpoints.")),
                    Paragraph(Text("For the induction step, the limiting term path is s maps to V_m(B;max(s,r),r)x. The argument pair (max(s,r),r) stays in Delta(T) whenever s,r belong to J. Original joint continuity makes the image of the compact square J times J a compact subset of E. Apply compact-range L1 evaluation with D_n=B_n-B and c=2*g. This gives uniform convergence of the integral of the coefficient difference evaluated on all these paths. For r<=s the clamped path is precisely V_m(B;s,r)x.")),
                    Paragraph(Text("Subtract the original two Bochner recurrences. Inside the integrand use B_n(s)(V_m(B_n;s,r)x-V_m(B;s,r)x)+(B_n(s)-B(s))V_m(B;s,r)x. Contractivity bounds the first contribution by g(s) times the uniform previous-term error, and compact-range evaluation controls the second. Both contributions have actual integrability; the original term_integrable theorem justifies subtraction of the original integrals. Extend only the scalar upper estimate from Icc(r,t) to J using nonnegativity. Choosing the previous-term tolerance after the finite integral of g closes the induction without dividing by that integral."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("uniform-strong-measurable-evolution-stability"), Handle("measurable_evolution_stability"),
                H("Uniform strong convergence on the entire ordered triangle"),
                StatementSource.FromAuthor(EvolutionStatement(true)), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For every vector x and epsilon>0 there exists one natural N such that for every n>=N and every pair of real times 0<=r<=t<=T, the norm of measurableEvolution(S,B_n,t,r)x-measurableEvolution(S,B,t,r)x is less than epsilon. The conclusion concerns the same coefficient-indexed measurableEvolution and includes a moving initial time r, the diagonal and both boundary edges.")),
                    Paragraph(Text("The original factorial bound gives norm(V_m(Q;t,r)x)<=G^m/m!*norm(x), where G is the integral of g from 0 to T, simultaneously for every eligible Q and every (t,r) in Delta(T). Mathlib's uniform summation theorem supplies one common tail bound for B and every B_n. Uniform convergence of the finitely many original terms controls the finite sums. The three-distance estimate, with two common tails and one finite-sum error, proves uniform convergence of the original sums. The original realization identity then gives exactly the named evolution conclusion.")),
                    Paragraph(Text("The hypotheses quantify over every admissible g, including the zero control. T=0, zero coefficients and x=0 are included. Neither the argument nor the conclusion requires norm(identity)=1 or a nonzero vector. There is no assumption of operator-norm L1 convergence, convergence at individual times, separability, finite dimension, operator-valued measurability, a common uncountable-vector exceptional set or regularity outside J. The result makes no assertion about operator-norm convergence of the evolution or uniformity over unbounded horizons or all unit vectors.")),
                    Paragraph(Text("Finite compact covers, Bochner integrability, uniform convergence of series and the exponential factorial series are Mathlib supplies. The original ordered recurrences and their measurable construction are reused from NonautonomousDysonPhillips and MeasurableNonautonomousDysonPhillips. This is a classical compact-range perturbation argument; no literature-priority assertion is made. A separate integrable control for each coefficient, with uniformly bounded total masses, is a further question and is not a conclusion here."))), DescribeRole.Theorem))));

    private static DeclarationHandle Handle(string name) => DeclarationHandle.Create("D5/S3/Quantum/Analysis/NonautonomousEvolutionStability."+name);
    private static Formula R => Call("Real");
    private static Formula N => Call("Nat");
    private static Formula E => F.Id("E");
    private static Formula Z => new Formula.Number(0);
    private static Formula One => new Formula.Number(1);
    private static Formula X(string name) => F.Id(name);
    private static Formula All(string n, Formula d, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll,FormulaIdentifier.Create(n),d,b);
    private static Formula Exists(string n, Formula d, Formula b) => new Formula.Bind(FormulaQuantifier.Exists,FormulaIdentifier.Create(n),d,b);
    private static Formula At(Formula f, params Formula[] xs) => new Formula.Apply(f,[.. xs]);
    private static Formula Lam(string n, Formula d, Formula b) => Seq(Grp(X(n),Colon,d),Mapsto,Sp,b);
    private static Formula Imp(Formula a,Formula b) => new Formula.Logic(a,FormulaLogicOperator.Implies,b);
    private static Formula And(Formula a,Formula b) => new Formula.Logic(a,FormulaLogicOperator.And,b);
    private static Formula Le(Formula a,Formula b) => new Formula.Relation(a,FormulaRelationOperator.LessThanOrEqual,b);
    private static Formula Lt(Formula a,Formula b) => new Formula.Relation(a,FormulaRelationOperator.LessThan,b);
    private static Formula Norm(Formula a) => new Formula.Norm(a);
    private static Formula Arrow(Formula a,Formula b) => new Formula.TypeArrow(a,b);
    private static Formula Clm => Call("ComplexCLM",E,E);
    private static Formula Coeff => Arrow(R,Clm);
    private static Formula J => Call("Icc",Z,X("T"));
    private static Formula Mu => Call("restrict",Call("volume"),J);
    private static Formula AE(Formula mu,Formula f) => Call("AlmostEverywhere",mu,f);
    private static Formula Int(Formula mu,Formula f) => Call("integral",mu,f);
    private static Formula Meas(Formula q) => All("x",E,Call("AEStronglyMeasurable",Lam("s",R,At(At(q,X("s")),X("x"))),Mu));
    private static Formula Dom(Formula q) => All("s",R,Imp(Call("Mem",X("s"),J),Le(Norm(At(q,X("s"))),At(X("g"),X("s")))));
    private static Formula Delta => And(Le(Z,X("r")),And(Le(X("r"),X("t")),Le(X("t"),X("T"))));
    private static Formula Scope(bool complete,Formula b) => All("u",Call("Universe"),All("E",Call("Type",X("u")),
        Seq(OpenBracket,Call("NormedAddCommGroup",E),CloseBracket,Sp,OpenBracket,Call("NormedSpace",Call("Complex"),E),CloseBracket,Sp,
            complete?Seq(OpenBracket,Call("CompleteSpace",E),CloseBracket,Sp,b):b)));
    private static Formula Diff(Formula y) => At(Subtract(At(X("Bseq"),X("n"),X("s")),At(X("B"),X("s"))),y);
    private static Formula L1 => All("x",E,Call("Tendsto",Lam("n",N,
        Call("intervalIntegral",Call("volume"),Z,X("T"),Lam("s",R,Norm(Diff(X("x")))))),Call("atTop"),Call("nhds",Z)));
    private static Formula Eventual(Formula body) => Call("Eventually",Call("atTop"),Lam("n",N,body));
    private static Formula Term(Formula q,Formula m,Formula t,Formula r) => Call("term",X("S"),q,m,t,r,X("x"));
    private static Formula Value(Formula q) => Call("measurableEvolution",X("S"),q,X("t"),X("r"),X("x"));

    private static Formula CompactEvaluation()
    {
        Formula a=X("alpha"), mu=X("mu"), d=X("D"), c=X("c"), v=X("v"), k=X("K");
        Formula slice=All("n",N,All("x",E,Call("AEStronglyMeasurable",Lam("s",a,At(d,X("n"),X("s"),X("x"))),mu)));
        Formula nonneg=AE(mu,Lam("s",a,Le(Z,At(c,X("s")))));
        Formula bound=All("n",N,AE(mu,Lam("s",a,Le(Norm(At(d,X("n"),X("s"))),At(c,X("s"))))));
        Formula conv=All("x",E,Call("Tendsto",Lam("n",N,Int(mu,Lam("s",a,Norm(At(d,X("n"),X("s"),X("x")))))),Call("atTop"),Call("nhds",Z)));
        Formula path=And(Call("AEStronglyMeasurable",v,mu),AE(mu,Lam("s",a,Call("Mem",At(v,X("s")),k))));
        Formula eval=Lam("s",a,At(d,X("n"),X("s"),At(v,X("s"))));
        Formula actual=All("n",N,All("v",Arrow(a,E),Imp(path,Call("Integrable",eval,mu))));
        Formula uniform=All("epsilon",R,Imp(Lt(Z,X("epsilon")),Eventual(All("v",Arrow(a,E),Imp(path,Lt(Int(mu,Lam("s",a,Norm(At(d,X("n"),X("s"),At(v,X("s")))))),X("epsilon")))))));
        Formula result=All("K",Call("Set",E),Imp(Call("IsCompact",k),And(actual,uniform)));
        return Scope(false,All("a",Call("Universe"),All("alpha",Call("Type",X("a")),Seq(OpenBracket,Call("MeasurableSpace",a),CloseBracket,Sp,
            All("mu",Call("Measure",a),All("D",Arrow(N,Arrow(a,Clm)),All("c",Arrow(a,R),
                Imp(slice,Imp(Call("Integrable",c,mu),Imp(nonneg,Imp(bound,Imp(conv,result))))))))))));
    }

    private static Formula EvolutionStatement(bool evolution)
    {
        Formula error=evolution?Norm(Subtract(Value(At(X("Bseq"),X("n"))),Value(X("B")))):
            Norm(Subtract(Term(At(X("Bseq"),X("n")),X("m"),X("t"),X("r")),Term(X("B"),X("m"),X("t"),X("r"))));
        Formula times=All("r",R,All("t",R,Imp(Delta,Lt(error,X("epsilon")))));
        Formula convergence=evolution?Exists("N",N,All("n",N,Imp(Le(X("N"),X("n")),times))):Eventual(times);
        Formula result=All("x",E,All("epsilon",R,Imp(Lt(Z,X("epsilon")),convergence)));
        if(!evolution) result=All("m",N,result);
        Formula premises=Imp(All("n",N,Meas(At(X("Bseq"),X("n")))),Imp(Meas(X("B")),
            All("g",Arrow(R,R),Imp(Call("IntegrableOn",X("g"),J,Call("volume")),
                Imp(All("s",R,Imp(Call("Mem",X("s"),J),Le(Z,At(X("g"),X("s"))))),
                    Imp(All("n",N,Dom(At(X("Bseq"),X("n")))),Imp(Dom(X("B")),Imp(L1,result))))))));
        return Scope(true,All("S",Call("Contraction",E),All("T",R,Imp(Le(Z,X("T")),
            All("Bseq",Arrow(N,Coeff),All("B",Coeff,premises))))));
    }

    private static Formula Recurrence()
    {
        Formula t=X("t"),r=X("r"),s=X("s"),q=X("B"),m=X("m");
        Formula baseTerm=Eq(Term(q,Z,t,r),Call("action",X("S"),Subtract(t,r),X("x")));
        Formula next=Eq(Term(q,Add(m,One),t,r),Call("intervalIntegral",Call("volume"),r,t,
            Lam("s",R,Call("action",X("S"),Subtract(t,s),At(At(q,s),Term(q,m,s,r))))));
        return Scope(true,All("S",Call("Contraction",E),All("B",Coeff,All("x",E,All("t",R,All("r",R,And(baseTerm,All("m",N,next))))))));
    }
}
