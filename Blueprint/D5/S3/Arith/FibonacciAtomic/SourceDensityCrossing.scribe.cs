using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class SourceDensityCrossingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/SourceDensityCrossing.";
    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula Par(Formula body) => Seq(Open, body, Close);
    private static Formula LtOf(Formula left, Formula right) => Seq(left, Sp, Lt, Sp, right);
    private static Formula LeOf(Formula left, Formula right) => Seq(left, Sp, Leq, Sp, right);
    private static Formula Both(params Formula[] clauses) => Seq(clauses.SelectMany((clause, i) =>
        i == 0 ? new[] { Par(clause) } : new[] { Sp, Land, Sp, Par(clause) }).ToArray());
    private static DocumentBlock Def(string name, string title, string prose) => Describe.Lean(
        DescribeId.Create("source-density-" + (name == "a" ? "coordinate-a" : name.ToLowerInvariant())),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Each real finite-product ratio increases strictly and crosses one at a unique bounded point.",
        H("Real Extension of Fibonacci Source Density Ratios"),
        Blocks(
            Paragraph(Text("F denotes the natural Fibonacci sequence with F(0)=0 and F(1)=1. "
                + "Fix natural k>=1 and j. Put d=3k. Nonintegral t is an auxiliary real "
                + "parameter of finite products; it does not represent a nonintegral number of tree leaves. "
                + "E,A,D,L,a,b,n,H,q,c,g and lowerEnvelope are the real extension defined in "
                + "SourceDensityMonotonicity.")),
            Def("sourceDensity", "Composition count ratio", "sourceDensity(k,t,i) is the ratio of "
                + "fiberCount(t-i,i) to fiberCount(step iterated 3k times on (t-i,i)). "
                + "The subtraction is natural subtraction. Its interpretation as a density on the t-leaf "
                + "source grid requires t>=1 and i<=t. The definition still has values outside this "
                + "domain, for example fiberCount(0,0)=1. The theorem uses only t>=j+1 "
                + "with i=j or i=j+1."),
            Paragraph(Text("In the displayed statement, logQ(k,j) denotes the function "
                + "t maps to log(q(k,j,t)), and qOverT(k,j) denotes t maps to q(k,j,t)/t. "
                + "R and N denote the real numbers and natural numbers.")),
            Describe.Lean(DescribeId.Create("source-density-estimate"),
                DeclarationHandle.Create(Prefix + "result"), H("Strict increase and unique crossing"),
                StatementSource.FromAuthor(ResultFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The statement combines the analytic bounds, the integer "
                    + "bridge, and the actual density comparisons. The derivative is taken on the whole real line at each "
                    + "legal t, including the endpoint j+1. The reciprocal endpoint bounds "
                    + "follow from the logarithmic-mean kernel sandwich. Cassini's squared "
                    + "determinant identity links the three affine coordinates, so their "
                    + "logarithmic errors are estimated together.")),
                    Paragraph(Text("The finite-product factor H decreases strictly to c and lies "
                        + "strictly between c and one on the legal half-line. Hence q(2j+1)<1 "
                        + "and q(j+(j+1)/c)>1. Continuity gives the crossing between these two "
                        + "points. The decrease of H and its limit c give the strict lower bound H>c. "
                        + "Strict increase gives uniqueness and the three integer "
                        + "comparison equivalences for the real finite-product ratio and actual density ratio. "
                        + "For i=j or j+1 at a legal integer t, the iterated Fibonacci step has coordinates "
                        + "(At+Ei,Dt+Ai). The Catalan and binomial factorial identities give "
                        + "the adjacent fiber-count ratio. Pairing consecutive factors in "
                        + "rising(2n-1,2D)=4^D rising(n-1/2,D) rising(n,D) then gives the integer bridge."))), DescribeRole.Theorem))));

    private static Formula ResultFormula()
    {
        var k = V("k"); var j = V("j"); var t = V("t");
        var tau = F.Tau; var z = V("z");
        var qt = Call("q", k, j, t); var gt = Call("g", k, j, t);
        var qtau = Call("q", k, j, tau);
        var densityRatio = new Formula.Fraction(Call("sourceDensity", k, t, Add(j, D(1))),
            Call("sourceDensity", k, t, j));
        var legalRoot = Both(LeOf(Add(j, D(1)), tau), Seq(qtau, Sp, Eq, Sp, D(1)));
        var uniqueRoot = Seq(Exists, Sp, tau, Sp, InMacro, Sp, V("R"), Comma, Sp,
            Both(legalRoot, Seq(Forall, Sp, z, Sp, InMacro, Sp, V("R"), Comma, Sp,
                Par(Both(LeOf(Add(j, D(1)), z), Seq(Call("q", k, j, z), Sp, Eq, Sp, D(1)))),
                Sp, Implies, Sp, z, Sp, Eq, Sp, tau)));
        var comparisons = Seq(Forall, Sp, t, Sp, InMacro, Sp, V("N"), Comma, Sp,
            Par(LeOf(Add(j, D(1)), t)), Sp, Implies, Sp,
            Both(Seq(Par(LtOf(qt, D(1))), Sp, Iff, Sp, Par(LtOf(t, tau))),
                Seq(Par(Seq(qt, Sp, Eq, Sp, D(1))), Sp, Iff, Sp, Par(Seq(t, Sp, Eq, Sp, tau))),
                Seq(Par(LtOf(D(1), qt)), Sp, Iff, Sp, Par(LtOf(tau, t))),
                Seq(Par(LtOf(densityRatio, D(1))), Sp, Iff, Sp, Par(LtOf(t, tau))),
                Seq(Par(Seq(densityRatio, Sp, Eq, Sp, D(1))), Sp, Iff, Sp,
                    Par(Seq(t, Sp, Eq, Sp, tau))),
                Seq(Par(LtOf(D(1), densityRatio)), Sp, Iff, Sp, Par(LtOf(tau, t)))));
        var bridge = Seq(Forall, Sp, t, Sp, InMacro, Sp, V("N"), Comma, Sp,
            Par(LeOf(Add(j, D(1)), t)), Sp, Implies, Sp, qt, Sp, Eq, Sp, densityRatio);
        var boundedRoot = Seq(Exists, Sp, tau, Sp, InMacro, Sp, V("R"), Comma, Sp,
            Both(legalRoot, LtOf(Add(Seq(D(2), j), D(1)), tau),
                LtOf(tau, Add(j, new Formula.Fraction(Add(j, D(1)), Call("c", k)))), comparisons));
        var analytic = Seq(Forall, Sp, t, Sp, InMacro, Sp, V("R"), Comma, Sp,
            Par(LeOf(Add(j, D(1)), t)), Sp, Implies, Sp,
            Both(LtOf(D(0), qt), Call("HasDerivAt", Call("logQ", k, j), gt, t),
                LeOf(Call("lowerEnvelope", k, j, t), gt)));
        return Disp(Seq(Forall, Sp, k, Comma, j, Sp, InMacro, Sp, V("N"), Comma, Sp,
            Par(LeOf(D(1), k)), Sp, Implies, Sp,
            Both(LtOf(D(0), Call("c", k)), analytic,
                Call("StrictMonoOn", Call("q", k, j), Call("Ici", Add(j, D(1)))),
                Call("Tendsto", Call("qOverT", k, j), Call("atTop"),
                    Call("nhds", new Formula.Fraction(Call("c", k), Add(j, D(1))))),
                uniqueRoot, boundedRoot, bridge)));
    }
}
