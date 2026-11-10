using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis;

internal sealed class VaryingBackgroundEvolutionStabilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Compact-time strong convergence of contraction backgrounds and fixed-vector L1 convergence of separately controlled measurable coefficients imply uniform strong convergence of the original nonautonomous evolution on the full closed ordered time triangle.",
        H("Varying contraction backgrounds and measurable evolution"), Blocks(
            Paragraph(Text("Let E be a complex normed space in any universe. The assertions about Dyson terms and evolution assume completeness; the compact-range integral assertion does not. The zero space is included. A contraction background is the original NonautonomousDysonPhillips.Contraction E, with complex-linear contraction operators on nonnegative times, identity at zero, the semigroup law and continuous vector orbits. Write A(h)=S.action(h)=S.operator(Real.toNNReal(h)), and A_n(h)=(Sseq n).action(h). Strong convergence on a compact time interval means that for every fixed x and epsilon>0 one eventual index controls norm(A_n(h)x-A(h)x) for every 0<=h<=T. There is no uniformity over the unit ball.")),
            new DocumentBlock.DisplayFormula(Recurrence()),
            Paragraph(Text("The displayed terms and vector Bochner integrals are exactly the original NonautonomousDysonPhillips.term. Coefficients are evaluated at absolute time s, and A(t-s) acts after B(s). The evolution is the original coefficient-indexed MeasurableNonautonomousDysonPhillips.measurableEvolution. Its existing realization identity identifies it with the original sum of these terms on every admissible ordered interval.")),
            Describe.Lean(DescribeId.Create("compact-time-integral-background-action"), Handle("uniform_integral_background_action"),
                H("Uniform integrals of background action differences"),
                StatementSource.FromAuthor(BackgroundStatement()), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Alpha is any measurable space in any universe, mu is any measure, and T is any real number. B(s) is a bounded complex-linear endomorphism with every fixed-vector slice AE strongly measurable for mu. The real function g is mu-integrable, nonnegative almost everywhere, and dominates norm(B(s)) almost everywhere. K is any compact subset of E, including the empty set. For every n, every AE strongly measurable v valued in K almost everywhere, and every AE strongly measurable real h, the difference A_n(h(s))B(s)v(s)-A(h(s))B(s)v(s) is Bochner integrable. This integrability assertion places no interval restriction on h. If h belongs to Icc(0,T) almost everywhere, then for every epsilon>0 a single eventual n bounds the integral of the norm of this difference by epsilon, uniformly over all such v and h.")),
                    Paragraph(Text("Use the continuous linear map U_n from E to C(Icc(0,T),E) that sends x to the continuous compact-time function h maps to A_n(h)x-A(h)x. Contractivity gives norm(U_n x)<=2*norm(x), and the assumed compact-time convergence gives U_n x tending to zero for each fixed x. Dominated convergence, with majorant 2*g(s)*norm(x), gives the integral of norm(U_n(B(s)x)) tending to zero. Apply SeparateMassEvolutionStability.uniform_integral_evaluation_of_mass to the endomorphism (x,f) maps to (0,U_n(B(s)x)) of E times C(Icc(0,T),E), with control 2*g and compact set K times the zero function. The supremum norm bounds every measurable choice of h in the interval. Actual vector integrability follows from the existing integrable evaluated-path theorem and continuity of the actions. Only the pre-B path range is compact; no compactness of the merely measurable post-B range is asserted."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("varying-background-original-term-convergence"), Handle("uniform_term_convergence_of_mass"),
                H("Uniform convergence of the original finite-order terms"),
                StatementSource.FromAuthor(EvolutionStatement(false)), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Let T>=0, J=Icc(0,T), and Delta(T)={(t,r):0<=r<=t<=T}. Every fixed-vector slice of B_n and B is AE strongly measurable for volume restricted to J. Each n has a separate real integrable control g_n on J; B has another control g. At every s in J these controls are nonnegative and bound the corresponding operator norms. A real C>=0 bounds every integral of g_n and the integral of g from 0 to T. For each fixed x, the integral from 0 to T of norm((B_n(s)-B(s))x) tends to zero. Under these hypotheses and compact-time strong convergence of the backgrounds, for every natural m, vector x and epsilon>0 there is one N such that all n>=N and all (t,r) in Delta(T) have term discrepancy less than epsilon.")),
                    Paragraph(Text("For the limiting path v_r(s)=term(S,B,m,max(s,r),r,x), original joint continuity makes its range over J times J compact. The existing coefficient path error theorem controls the integral of norm((B_n(s)-B(s))v_r(s)) uniformly in r, using the separate mass bound for g_n+g. Apply the background integral assertion with h_t(s)=max(t-s,0). This continuous time choice lies in J for s,t in J. For r<=s<=t, both clamps agree with the original recurrence arguments.")),
                    Paragraph(Text("The successor discrepancy is the integral of three contributions: A_n(t-s)B_n(s) times the previous-term difference; A_n(t-s)(B_n(s)-B(s)) times the limiting term; and (A_n(t-s)-A(t-s))B(s) times that same limiting term. Original term_integrable justifies subtraction of the two original Bochner integrals. Contractivity and the coefficient norm bound give g_n(s)*eta for the first contribution, whose integral is at most C*eta. The two uniform integral assertions control the other contributions. Choose eta>0 with C*eta<epsilon/3 and each other tolerance epsilon/3. This uses no division by C. The base term uses precisely the assumed compact-time background convergence."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("varying-background-original-evolution-stability"), Handle("measurable_evolution_stability_of_mass"),
                H("Uniform strong convergence of the original evolutions"),
                StatementSource.FromAuthor(EvolutionStatement(true)), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Under exactly the finite-order theorem's hypotheses, every fixed vector x and epsilon>0 admit a single natural N that works for every n>=N and every pair of real times 0<=r<=t<=T. The norm of measurableEvolution(Sseq n,Bseq n,t,r,x)-measurableEvolution(S,B,t,r,x) is then less than epsilon.")),
                    Paragraph(Text("For every contraction background U and coefficient Q with an admissible separate control of mass at most C, the original term_bound gives norm(term(U,Q,m,t,r,x))<=C^m/m!*norm(x). The exponential factorial series is summable, so the existing uniform-series theorem supplies a common tail bound over all these backgrounds, coefficients and endpoints. The finite head converges uniformly by the finite-order theorem. Two tails and the finite-head estimate give convergence of the original sums. Apply measurableEvolution_apply separately to the sequence background Sseq n with coefficient Bseq n and to the limiting background S with coefficient B.")),
                    Paragraph(Text("The full closed triangle, its diagonal, T=0, C=0, x=0, zero controls and zero Banach spaces are included. No common integrable pointwise envelope for g_n and g, operator-norm convergence, finite dimension, separability, nonzero vector, generator comparison, forcing term or regularity outside J is assumed. The conclusion is uniform in the two endpoints for each fixed vector, with no assertion of operator-norm convergence or uniformity over unbounded horizons. The proof uses the original measurable Dyson construction, compact-path coefficient evaluation, dominated convergence and uniform summation; it makes no claim of literature priority."))), DescribeRole.Theorem))));

    private static DeclarationHandle Handle(string name) => DeclarationHandle.Create("D5/S3/Quantum/Analysis/VaryingBackgroundEvolutionStability."+name);
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
    private static Formula Equal(Formula a,Formula b) => new Formula.Relation(a,FormulaRelationOperator.Equal,b);
    private static Formula Norm(Formula a) => new Formula.Norm(a);
    private static Formula Arrow(Formula a,Formula b) => new Formula.TypeArrow(a,b);
    private static Formula Clm => Call("ComplexCLM",E,E);
    private static Formula Coeff => Arrow(R,Clm);
    private static Formula J => Call("Icc",Z,X("T"));
    private static Formula Mu => Call("restrict",Call("volume"),J);
    private static Formula AE(Formula mu,Formula f) => Call("AlmostEverywhere",mu,f);
    private static Formula Int(Formula mu,Formula f) => Call("integral",mu,f);
    private static Formula Meas(Formula q) => All("x",E,Call("AEStronglyMeasurable",Lam("s",R,At(At(q,X("s")),X("x"))),Mu));
    private static Formula Dom(Formula q, Formula c) => All("s",R,Imp(Call("Mem",X("s"),J),Le(Norm(At(q,X("s"))),At(c,X("s")))));
    private static Formula Delta => And(Le(Z,X("r")),And(Le(X("r"),X("t")),Le(X("t"),X("T"))));
    private static Formula Scope(bool complete,Formula b) => All("u",Call("Universe"),All("E",Call("Type",X("u")),
        Seq(OpenBracket,Call("NormedAddCommGroup",E),CloseBracket,Sp,OpenBracket,Call("NormedSpace",Call("Complex"),E),CloseBracket,Sp,
            complete?Seq(OpenBracket,Call("CompleteSpace",E),CloseBracket,Sp,b):b)));
    private static Formula Diff(Formula y) => At(Subtract(At(X("Bseq"),X("n"),X("s")),At(X("B"),X("s"))),y);
    private static Formula L1 => All("x",E,Call("Tendsto",Lam("n",N,
        Call("intervalIntegral",Call("volume"),Z,X("T"),Lam("s",R,Norm(Diff(X("x")))))),Call("atTop"),Call("nhds",Z)));
    private static Formula Eventual(Formula body) => Call("Eventually",Call("atTop"),Lam("n",N,body));
    private static Formula Term(Formula a,Formula q,Formula m,Formula t,Formula r) => Call("term",a,q,m,t,r,X("x"));
    private static Formula Value(Formula a,Formula q) => Call("measurableEvolution",a,q,X("t"),X("r"),X("x"));

    private static Formula Slim => All("x",E,All("epsilon",R,Imp(Lt(Z,X("epsilon")),
        Exists("N",N,All("n",N,Imp(Le(X("N"),X("n")),All("h",R,
            Imp(And(Le(Z,X("h")),Le(X("h"),X("T"))),
                Lt(Norm(Subtract(Call("action",At(X("Sseq"),X("n")),X("h"),X("x")),
                    Call("action",X("S"),X("h"),X("x")))),X("epsilon"))))))))));

    private static Formula BackgroundStatement()
    {
        Formula a=X("alpha"),mu=X("mu"),v=X("v"),h=X("h"),k=X("K");
        Formula bv=At(At(X("B"),X("s")),At(v,X("s")));
        Formula difference=Subtract(Call("action",At(X("Sseq"),X("n")),At(h,X("s")),bv),
            Call("action",X("S"),At(h,X("s")),bv));
        Formula path=And(Call("AEStronglyMeasurable",v,mu),
            AE(mu,Lam("s",a,Call("Mem",At(v,X("s")),k))));
        Formula measTime=Call("AEStronglyMeasurable",h,mu);
        Formula actual=All("n",N,All("v",Arrow(a,E),All("h",Arrow(a,R),
            Imp(path,Imp(measTime,Call("Integrable",Lam("s",a,difference),mu))))));
        Formula time=AE(mu,Lam("s",a,Call("Mem",At(h,X("s")),J)));
        Formula small=All("epsilon",R,Imp(Lt(Z,X("epsilon")),Eventual(
            All("v",Arrow(a,E),All("h",Arrow(a,R),Imp(path,Imp(measTime,
                Imp(time,Lt(Int(mu,Lam("s",a,Norm(difference))),X("epsilon"))))))))));
        Formula result=All("K",Call("Set",E),Imp(Call("IsCompact",k),And(actual,small)));
        Formula premises=Imp(All("x",E,Call("AEStronglyMeasurable",
            Lam("s",a,At(At(X("B"),X("s")),X("x"))),mu)),
            All("g",Arrow(a,R),Imp(Call("Integrable",X("g"),mu),
                Imp(AE(mu,Lam("s",a,Le(Z,At(X("g"),X("s"))))),
                    Imp(AE(mu,Lam("s",a,Le(Norm(At(X("B"),X("s"))),At(X("g"),X("s"))))),result)))));
        return Scope(false,All("a",Call("Universe"),All("alpha",Call("Type",X("a")),
            Seq(OpenBracket,Call("MeasurableSpace",a),CloseBracket,Sp,
                All("mu",Call("Measure",a),All("Sseq",Arrow(N,Call("Contraction",E)),
                    All("S",Call("Contraction",E),All("T",R,Imp(Slim,
                        All("B",Arrow(a,Clm),premises))))))))));
    }

    private static Formula EvolutionStatement(bool evolution)
    {
        Formula an=At(X("Sseq"),X("n")),bn=At(X("Bseq"),X("n"));
        Formula error=evolution?Norm(Subtract(Value(an,bn),Value(X("S"),X("B")))):
            Norm(Subtract(Term(an,bn,X("m"),X("t"),X("r")),
                Term(X("S"),X("B"),X("m"),X("t"),X("r"))));
        Formula times=All("r",R,All("t",R,Imp(Delta,Lt(error,X("epsilon")))));
        Formula convergence=Exists("N",N,All("n",N,Imp(Le(X("N"),X("n")),times)));
        Formula result=All("x",E,All("epsilon",R,Imp(Lt(Z,X("epsilon")),convergence)));
        if(!evolution) result=All("m",N,result);
        Formula gn=At(X("gn"),X("n")),g=X("g");
        Formula scalarIntegral(Formula f) => Call("intervalIntegral",Call("volume"),Z,X("T"),Lam("s",R,At(f,X("s"))));
        Formula nonneg(Formula f) => All("s",R,Imp(Call("Mem",X("s"),J),Le(Z,At(f,X("s")))));
        Formula masses=Imp(Le(Z,X("C")),Imp(All("n",N,Le(scalarIntegral(gn),X("C"))),
            Imp(Le(scalarIntegral(g),X("C")),Imp(L1,result))));
        Formula controls=All("gn",Arrow(N,Arrow(R,R)),All("g",Arrow(R,R),
            Imp(All("n",N,Call("IntegrableOn",gn,J,Call("volume"))),Imp(Call("IntegrableOn",g,J,Call("volume")),
                Imp(All("n",N,nonneg(gn)),Imp(nonneg(g),
                    Imp(All("n",N,Dom(At(X("Bseq"),X("n")),gn)),Imp(Dom(X("B"),g),All("C",R,masses)))))))));
        Formula premises=Imp(All("n",N,Meas(At(X("Bseq"),X("n")))),Imp(Meas(X("B")),controls));
        return Scope(true,All("Sseq",Arrow(N,Call("Contraction",E)),All("S",Call("Contraction",E),
            All("T",R,Imp(Le(Z,X("T")),Imp(Slim,
                All("Bseq",Arrow(N,Coeff),All("B",Coeff,premises))))))));
    }

    private static Formula Recurrence()
    {
        Formula t=X("t"),r=X("r"),s=X("s"),q=X("B"),m=X("m"),a=X("S");
        Formula baseTerm=Equal(Term(a,q,Z,t,r),Call("action",a,Subtract(t,r),X("x")));
        Formula next=Equal(Term(a,q,Add(m,One),t,r),Call("intervalIntegral",Call("volume"),r,t,
            Lam("s",R,Call("action",a,Subtract(t,s),At(At(q,s),Term(a,q,m,s,r))))));
        return Scope(true,All("S",Call("Contraction",E),All("B",Coeff,All("x",E,
            All("t",R,All("r",R,And(baseTerm,All("m",N,next))))))));
    }
}
