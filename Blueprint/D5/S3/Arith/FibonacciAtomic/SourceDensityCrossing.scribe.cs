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
        DescribeId.Create("source-density-" + name.ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The real finite-product ratio is strictly increasing and has a positive asymptotic slope.",
        H("Real Extension of Fibonacci Source Density Ratios"),
        Blocks(
            Paragraph(Text("F denotes the natural Fibonacci sequence with F(0)=0 and F(1)=1. "
                + "Fix natural k>=1 and j. Put d=3k. Nonintegral t is an auxiliary real "
                + "parameter of finite products; it does not represent a nonintegral number of tree leaves.")),
            Def("E", "First numerator length", "E(k)=F(3k-2), with truncated natural subtraction."),
            Def("A", "Second numerator length", "A(k)=F(3k-1)."),
            Def("D", "Denominator length", "D(k)=F(3k)=E(k)+A(k) for k>=1."),
            Def("L", "Total composition coefficient", "L(k)=F(3k+1)=A(k)+D(k) for k>=1."),
            Def("a", "First affine target coordinate", "a(k,j,t)=A(k)t+E(k)j."),
            Def("b", "Second affine target coordinate", "b(k,j,t)=D(k)t+A(k)j."),
            Def("n", "Total affine target coordinate", "n(k,j,t)=L(k)t+D(k)j."),
            Def("rising", "Rising finite product", "rising(x,m) is the product of x+i over "
                + "natural 0<=i<m. The empty product is one."),
            Def("H", "Finite-product factor", "H(k,j,t)=rising(a+1,E) rising(b+1,A) "
                + "/ (4^D rising(n-1/2,D)), where all coefficients and coordinates have the same k,j,t."),
            Def("q", "Real extension", "q(k,j,t)=(t-j)H(k,j,t)/(j+1)."),
            Def("c", "Leading coefficient", "c(k)=A(k)^E(k) D(k)^A(k)/(4^D(k) L(k)^D(k))."),
            Def("g", "Logarithmic derivative", "g(k,j,t)=1/(t-j)+A sum(1/(a+1+i),i<E) "
                + "+D sum(1/(b+1+i),i<A)-L sum(1/(n-1/2+i),i<D)."),
            Def("lowerEnvelope", "Three-block lower envelope", "The lower envelope is "
                + "1/(t-j)-(j+1/2)/(LADt^2)-AE/(2a(a+E))-DA/(2b(b+A)) "
                + "-LD/((n-1/2)(n+D-1/2)). Its coordinates share the same k,j,t."),
            Describe.Lean(DescribeId.Create("source-density-estimate"),
                DeclarationHandle.Create(Prefix + "result"), H("Strict increase and asymptotic slope"),
                StatementSource.FromAuthor(ResultFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The derivative is taken on the whole real line at each "
                    + "legal t, including the endpoint j+1. The reciprocal endpoint bounds "
                    + "follow from the logarithmic-mean kernel sandwich. Cassini's squared "
                    + "determinant identity links the three affine coordinates, so their "
                    + "logarithmic errors are estimated together."))), DescribeRole.Theorem))));

    private static Formula ResultFormula()
    {
        var k = V("k"); var j = V("j"); var t = V("t");
        var qt = Call("q", k, j, t); var gt = Call("g", k, j, t);
        var analytic = Seq(Forall, Sp, t, Sp, InMacro, Sp, V("R"), Comma, Sp,
            Par(LeOf(Add(j, D(1)), t)), Sp, Implies, Sp,
            Both(LtOf(D(0), qt), Call("HasDerivAt", Call("log_q", k, j), gt, t),
                LeOf(Call("lowerEnvelope", k, j, t), gt)));
        return Disp(Seq(Forall, Sp, k, Comma, j, Sp, InMacro, Sp, V("N"), Comma, Sp,
            Par(LeOf(D(1), k)), Sp, Implies, Sp,
            Both(LtOf(D(0), Call("c", k)), analytic,
                Call("StrictMonoOn", Call("q", k, j), Call("Ici", Add(j, D(1)))),
                Call("Tendsto", Call("q_over_t", k, j), Call("atTop"),
                    Call("nhds", new Formula.Fraction(Call("c", k), Add(j, D(1))))))));;
    }
}
