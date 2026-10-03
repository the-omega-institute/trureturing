using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class SourceDensityMonotonicityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/SourceDensityMonotonicity.";
    private static DocumentBlock Def(string name, string title, string prose) => Describe.Lean(
        DescribeId.Create("source-density-monotonicity-" + (name == "a" ? "coordinate-a" : name.ToLowerInvariant())),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Shared definitions for the real finite-product extension of Fibonacci source density ratios.",
        H("Definitions of Fibonacci Source Density Ratios"),
        Blocks(
            Paragraph(Text("F denotes the natural Fibonacci sequence with F(0)=0 and F(1)=1. "
                + "Fix natural k>=1 and j. Put d=3k. Nonintegral t is an auxiliary real "
                + "parameter of finite products; it does not represent a nonintegral number of tree leaves.")),
            Def("E", "First numerator length", "E(k)=F(3k-2), with truncated natural subtraction."),
            Def("A", "Second numerator length", "A(k)=F(3k-1)."),
            Def("D", "Denominator length", "D(k)=F(3k)."),
            Def("L", "Total composition coefficient", "L(k)=F(3k+1)."),
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
                + "-LD/((n-1/2)(n+D-1/2)). Its coordinates share the same k,j,t."))));
}
