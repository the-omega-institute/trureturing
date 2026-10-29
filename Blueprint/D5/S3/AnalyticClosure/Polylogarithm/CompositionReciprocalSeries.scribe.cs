using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.AnalyticClosure.Polylogarithm;

internal sealed class CompositionReciprocalSeriesDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/AnalyticClosure/Polylogarithm/CompositionReciprocalSeries.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The real ordinary formal inverse represents the actual normalized analytic reciprocal.",
        H("CompositionReciprocalSeries"), Blocks(
            Describe.Lean(DescribeId.Create("ordinary-reciprocal-series"),
                DeclarationHandle.Create(Prefix + "ordinarySeries"),
                H("The ordinary formal inverse"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/AnalyticClosure/xu2026rational")),
                Blocks(Paragraph(Text(
                    "For head : PNat, tail : List PNat and ell : PNat, ordinarySeries is the "
                    + "inverse of the ell-th power of PowerSeries.mk applied to the actual "
                    + "CompositionDisk.coefficient head tail. The composition is head :: tail; "
                    + "tail may be empty and may contain any finite block of leading ones."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("ordinary-reciprocal-coefficient"),
                DeclarationHandle.Create(Prefix + "ordinaryCoefficient"),
                H("Ordinary real coefficients"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/AnalyticClosure/xu2026rational")),
                Blocks(Paragraph(Text(
                    "ordinaryCoefficient is the n-th real PowerSeries coefficient of ordinarySeries. "
                    + "It uses ordinary powers z^n, with no exponential-generating factorial."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actual-analytic-reciprocal"),
                DeclarationHandle.Create(Prefix + "reciprocal"),
                H("The actual analytic reciprocal"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/AnalyticClosure/xu2026rational")),
                Blocks(Paragraph(Text(
                    "reciprocal inverts the ell-th power of "
                    + "CompositionZeroFreeCollar.normalizedContinuation. That continuation removes "
                    + "the source zero of order CompositionDisk.depth tail at the origin. "
                    + "The local scalar power series of reciprocal has exactly the complex casts "
                    + "of ordinaryCoefficient: the Cauchy product with the source series power "
                    + "equals one, and uniqueness identifies its coefficients with the real formal "
                    + "inverse. Its n-th coefficient is the Cauchy integral on the circle of radius "
                    + "one half, divided by 2 pi i."))),
                DescribeRole.Definition))));
}
