using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FinitePhase;

internal sealed class ResidualWindowDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FinitePhase/ResidualWindow.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite stochastic matrix admits a short near-return phase, with a uniform bound for nonresonant moving averages.",
        H("Finite stochastic phase residuals and moving averages"), Blocks(
            Paragraph(Text("Let I be any finite nonempty state type, S its cardinality, and P a real matrix with nonnegative entries and each row summing to one. complexMatrix(P) is the same matrix acting on complex columns. The norm of a column is its maximum coordinate modulus. In the formulas, FiniteNonempty(I) means finite and nonempty; residual(P,w,v) is v-w complexMatrix(P)v, and normInf is the column maximum norm. All sums over I use the whole state type. No irreducibility, aperiodicity, normality, mixing, or lower bound on a positive transition is assumed.")),
            Describe.Lean(DescribeId.Create("finite-stochastic-phase-residual"),
                DeclarationHandle.Create(Prefix + "phase_residual"),
                H("A short return phase controls the residual"),
                StatementSource.FromAuthor(Disp(CoreStatement())), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For every unit complex w and nonzero complex column v, one natural return length r between 1 and S satisfies |1-w^r|^2 times the maximum norm of v at most 8S times the maximum norm of v-wP(v). Roots of unity and w=1 are included. In particular, a zero residual forces a return phase among the first S powers.")),
                    Paragraph(Text("Choose a coordinate c of v with maximal modulus M>0, and put E equal to the maximum residual modulus. At time t, consider the real part of w^t v(i) conjugate(c). A stochastic weighted average is bounded above by one of its coordinates. The residual identity therefore propagates a supporting value of at least M^2-tME to some coordinate at every natural time t.")),
                    Paragraph(Text("The selected coordinate at time t has squared distance from c, after multiplication by w^t, at most 2tME. Among times 0 through S, two selected coordinates coincide, at a<b. With r=b-a, subtracting their two deviations after rotation gives c(w^r-1). The squared triangle bound and a+b at most 2S yield M^2|1-w^r|^2 at most 8SME. Cancellation of the positive M proves the result."))),
                DescribeRole.Theorem),
            Paragraph(Text("ProbabilityRow(alpha) means nonnegative real coordinates summing to one, and ReportBox(b) means every real coordinate lies in [0,1]. For a real probability row alpha and a real report b with every coordinate in [0,1], write q(n)=alpha dot (P^n b). For an integer j, including negative j, phaseWindow is exactly N^{-1} times the sum, for 0<=k<N, of z^{j(m+k)} q(m+k). The displayed absolute value is the complex modulus. The starting time m is arbitrary and N is a positive natural number.")),
            Describe.Lean(DescribeId.Create("finite-stochastic-phase-window"),
                DeclarationHandle.Create(Prefix + "window_average"),
                H("A positive phase gap bounds every moving window"),
                StatementSource.FromAuthor(Disp(WindowStatement())), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Assume |z|=1, j is a nonzero integer, and gamma>0 is a lower bound for |1-z^{jr}| for every natural r between 1 and S. Then the modulus of phaseWindow is at most 16S/(N gamma^2), uniformly in m. Taking z=w and j=1 gives the bound for any unit phase w. Taking gamma to be the positive minimum of the finitely many phase gaps gives the usual minimum-gap formulation.")),
                    Paragraph(Text("Set w=z^j and u(t)=P^t b on complex columns. Stochasticity gives maximum norm at most one for every u(t), and the probability row alpha has functional norm at most one. Apply the preceding residual estimate to V=sum_{k<N} w^k u(m+k). Its residual is exactly u(m)-w^N u(m+N), so it has norm at most two. The case V=0 is handled directly; otherwise the short return length and the gamma hypothesis give gamma^2 times the norm of V at most 16S.")),
                    Paragraph(Text("The original real matrix powers and real dot product agree exactly with their complex casts. Integer powers satisfy (z^j)^t=z^{jt} for every natural t, including negative j. Thus the unnormalized original sum is w^m alpha(V); its modulus is at most the norm of V. Division by the positive N completes the estimate. A zero phase gap is excluded by the explicit positive hypothesis, and no inverse operator is needed."))),
                DescribeRole.Theorem),
            Paragraph(Text("These estimates concern finite stochastic readouts and phase averages. They establish neither the complete native finite-memory separation theorem, the algebraic phase gap for the original system, nor its original state realization.")))));
    private static Formula A(string name, params Formula[] args)
    {
        var parts = new List<Formula> { F.Id(name), Open };
        for (int k=0; k<args.Length; k++) {
            if (k>0) parts.Add(Comma);
            parts.Add(args[k]);
        }
        parts.Add(Close);
        return Seq(parts.ToArray());
    }
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, F.Id(name), Colon, type, Comma, Sp, Open, body, Close);
    private static Formula Ex(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, F.Id(name), Colon, type, Comma, Sp, Open, body, Close);
    private static Formula Imp(Formula p, Formula q) => Seq(Open,p,Close,Implies,Sp,Open,q,Close);
    private static Formula And(params Formula[] clauses)
    {
        var parts = new List<Formula>();
        for (int k=0; k<clauses.Length; k++) {
            if (k>0) parts.Add(Land);
            parts.Add(Seq(Open,clauses[k],Close));
        }
        return Seq(parts.ToArray());
    }
    private static Formula Power(Formula x, Formula n) => Seq(Open,x,Close,Caret,Grp(n));
    private static Formula Abs(Formula x) => Seq(Lvert,Sp,x,Rvert,Sp);
    private static Formula Product(params Formula[] xs)
    {
        var parts = new List<Formula>();
        for (int k=0; k<xs.Length; k++) {
            if (k>0) parts.Add(Cdot);
            parts.Add(Seq(Open,xs[k],Close));
        }
        return Seq(parts.ToArray());
    }
    private static Formula CoreStatement()
    {
        var I=F.Id("I"); var P=F.Id("P"); var w=F.Id("w"); var v=F.Id("v");
        var r=F.Id("r"); var real=Seq(Mathbb,Grp(F.Id("R")));
        var complex=Seq(Mathbb,Grp(F.Id("C"))); var nat=Seq(Mathbb,Grp(F.Id("N")));
        var conclusion=Ex("r",nat,And(Seq(D(1),Leq,Sp,r),Seq(r,Leq,Sp,A("card",I)),
            Seq(Product(Power(Abs(Seq(D(1),Minus,Power(w,r))),D(2)),A("normInf",v)),Leq,Sp,
                Product(D(8),A("card",I),A("normInf",A("residual",P,w,v))))));
        var body=All("v",Seq(I,To,complex),Imp(Seq(v,Neq,D(0)),conclusion));
        body=All("w",complex,Imp(Seq(Abs(w),Eq,D(1)),body));
        body=All("P",A("Matrix",I,I,real),Imp(A("RowStochastic",P),body));
        return All("I",F.Id("Type"),Imp(A("FiniteNonempty",I),body));
    }
    private static Formula WindowStatement()
    {
        var I=F.Id("I"); var P=F.Id("P"); var z=F.Id("z"); var j=F.Id("j");
        var g=F.Id("gamma"); var a=F.Id("alpha"); var b=F.Id("b"); var m=F.Id("m");
        var N=F.Id("N"); var r=F.Id("r");
        var real=Seq(Mathbb,Grp(F.Id("R"))); var complex=Seq(Mathbb,Grp(F.Id("C")));
        var nat=Seq(Mathbb,Grp(F.Id("N"))); var integer=Seq(Mathbb,Grp(F.Id("Z")));
        var gap=All("r",nat,Imp(And(Seq(D(1),Leq,Sp,r),Seq(r,Leq,Sp,A("card",I))),
            Seq(g,Leq,Sp,Abs(Seq(D(1),Minus,Power(z,Product(j,r)))))));
        var bound=Seq(Abs(A("phaseWindow",P,a,b,z,j,m,N)),Leq,Sp,
            Frac,Grp(Product(D(1,6),A("card",I))),Grp(Product(N,Power(g,D(2)))));
        var body=All("alpha",Seq(I,To,real),All("b",Seq(I,To,real),
            Imp(And(A("ProbabilityRow",F.Id("alpha")),A("ReportBox",b)),
            All("m",nat,All("N",nat,Imp(Seq(D(0),Lt,N),bound))))));
        body=Imp(gap,body);
        body=All("gamma",real,Imp(Seq(D(0),Lt,g),body));
        body=All("j",integer,Imp(Seq(j,Neq,D(0)),body));
        body=All("z",complex,Imp(Seq(Abs(z),Eq,D(1)),body));
        body=All("P",A("Matrix",I,I,real),Imp(A("RowStochastic",P),body));
        return All("I",F.Id("Type"),Imp(A("FiniteNonempty",I),body));
    }

}
