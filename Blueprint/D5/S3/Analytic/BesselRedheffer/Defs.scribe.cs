using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.BesselRedheffer;

internal sealed class DefsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The normalized Bessel series and the conjectured Redheffer lower bound.",
        H("Normalized Bessel functions"), Blocks(
            Entry("bessel-function", "nbessel", "The normalized series",
                "For real order nu and argument x, the function is the sum of (-x squared/4) to the power k divided by k factorial and the rising factorial of nu+1 of order k."),
            Entry("bessel-first-zero", "firstZero", "The first positive zero",
                "The first zero is the infimum of the set of positive real arguments where the normalized series vanishes. Existence and positivity require separate proofs."),
            Entry("bessel-lower-bound", "claim", "The conjectured lower bound",
                "For every nu greater than -1 and every real x with absolute value less than the first positive zero j, the real power of j squared divided by j squared minus x squared, with exponent j squared divided by 4(nu+1)(nu+2), is at most the ratio of the normalized series of orders nu+1 and nu."))));

    private static DocumentBlock Entry(string id, string name, string title, string text) =>
        Describe.Lean(DescribeId.Create(id),
            DeclarationHandle.Create("D5/S3/Analytic/BesselRedheffer/Defs." + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), DescribeRole.Definition);
}
