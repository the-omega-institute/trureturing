using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.RefinedBMV.PositiveCenter;

internal sealed class RefinedBMVPositiveCenterLeftStripGeometricSignDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/HilbertOperators/hagele2026refinedbmv");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The mixed derivative of the refined BMV left strip from gap one",
        H("Strict mixed derivative negativity on the left strip from gap one"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("refined-bmv-positive-center-left-strip-separated-gap"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Analysis/RefinedBMV/PositiveCenter/LeftStripGeometricSign.leftStrip_logKernel_mixed_lt_ge_one"),
                H("Strict negativity for gaps at least one"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For every natural degree p at least eleven and logarithmic coordinates u and v " +
                    "with 0 < u ≤ 1/2 and v − u ≥ 1, the v derivative of the u derivative of the original " +
                    "logarithmic kernel is strictly negative. Geometric reduction bounds the weighted " +
                    "derivative using a scalar whose positivity is checked by outward-rounded Taylor " +
                    "models up to integration gap 7/2. The analytic tail estimate covers larger " +
                    "integration gaps pointwise in the derivative identity."))),
                DescribeRole.Theorem))));
}
