using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.Jensen;

internal sealed class OriginalTailDerivativeVectorSourcesDocument : IScribeDocumentDefinition
{
    private static DocumentBlock Definition(string id, string declaration, string title, string text) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create("D5/S3/Zeros/Jensen/OriginalTailDerivativeVectorSources." + declaration),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Definition);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Parameter and source identities for the complete original tail derivative vector.",
        H("The original tail parameter and source identities"),
        Blocks(
            Definition("original-parameter-derivative", "originalb", "The true fixed-degree derivative",
                "For a natural n and real t,x, b_n(t,x) is the finite sum from k=0 to n " +
                "of c_(n,k)*k*t^(k-1)*x^(2*k), where " +
                "c_(n,k)=(-1)^k*(n)_k/(n^k*(2*k)!). The exponent k-1 is natural " +
                "subtraction and the k=0 summand is zero. This is the actual partial " +
                "derivative in t of the existing originalB, with n fixed."),
            Definition("raw-derivative", "rawD", "A raw half-line derivative component",
                "For n,t and a real function h, rawD(n,t,h)=integral over x>0 of b_n(t,x)*h(x)."),
            Definition("raw-second-moment", "rawM2", "A raw half-line second spatial moment",
                "For n,t,h, rawM2(n,t,h)=integral over x>0 of x^2*originalB(n,t,x)*h(x)."),
            Definition("raw-adjacent-extraction", "rawG", "A raw adjacent-degree extraction",
                "For n,t,h, rawG=(2*n*rawD-rawM2/2)/(2*n+1)."),
            Definition("full-derivative", "fullD", "The normalized full-source derivative",
                "For n,t, fullD=integral over the real line of b_n(t,x)*sourceThetaDensity(x)."),
            Definition("full-second-moment", "fullM2", "The normalized full-source second moment",
                "For n,t, fullM2=integral over the real line of x^2*originalB(n,t,x)*sourceThetaDensity(x)."),
            Definition("full-adjacent-extraction", "fullG", "The normalized full-source extraction",
                "For n,t, fullG=(2*n*fullD-fullM2/2)/(2*n+1). There is no additional normalization."),
            Describe.Lean(
                DescribeId.Create("spatial-derivative-bound"),
                DeclarationHandle.Create(
                    "D5/S3/Zeros/Jensen/OriginalTailDerivativeVectorSources.spatial_derivative_bound"),
                H("The spatial derivative estimate for the parameter response"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For n>=1, t>0 and x>=0, put alpha=t/(2*n) and let p be the " +
                    "original finite polynomial with p(x)=originalB(n,t,x). Then " +
                    "|p'(x)|<=t*x*exp(alpha*x^2/2). The integrating factor " +
                    "exp(-alpha*x^2/2) converts the polynomial differential equation " +
                    "to an integral from zero, and the original energy bound controls " +
                    "its integrand. The coefficientwise identity 2*t*b_n=x*p' gives " +
                    "|b_n(t,x)|<=x^2*exp(alpha*x^2/2)/2, which pairs the parameter " +
                    "response with the weighted second residual in the complete tail " +
                    "derivative vector. Finite moments, five Green pairings, the common " +
                    "2/Z source transports and reflected-node identities connect the " +
                    "same vector to the actual source. No full-source product sign or " +
                    "node existence follows from these identities."))),
                DescribeRole.Lemma)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Zeros/Jensen/OriginalTailDerivativeVectorResiduals")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Zeros/Jensen/SourceJensenIntegralExtension")),
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S3/Zeros/Jensen/SourceJensenPositiveExtension"))
        ]));
}
