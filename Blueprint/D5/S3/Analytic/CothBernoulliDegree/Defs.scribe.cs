using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.CothBernoulliDegree;

internal sealed class DefsDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Asymptotics/zhu2020completelymonotonicdegrees");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A Bernoulli remainder and two consecutive derivative signs.",
        H("The hyperbolic cotangent remainder"), Blocks(
            Entry("coth-bernoulli-remainder", "p", "The remainder",
                "For a natural n, subtract from cosh(t)/sinh(t)/t the sum over k from zero through n of 2^(2k) B_(2k) t^(2k-2)/(2k)!. The powers of t in this finite sum are integer powers. Only even Bernoulli indices occur."),
            Entry("coth-bernoulli-weighted", "P", "The weighted remainder",
                "For natural m and n, P(m,n,t) is (-1)^n times t^m times the remainder p(n,t)."),
            Entry("coth-bernoulli-sign-claim", "claim", "Two consecutive derivative orders",
                "For every natural m at least one and natural n at least two, the derivative of P(m,n) of order m+2n-2 is strictly positive at every positive real t. The derivative of order m+2n-1 is not strictly positive at every positive real t."))));

    private static DocumentBlock Entry(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create("D5/S3/Analytic/CothBernoulliDegree/Defs." + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(text))), DescribeRole.Definition);
}
