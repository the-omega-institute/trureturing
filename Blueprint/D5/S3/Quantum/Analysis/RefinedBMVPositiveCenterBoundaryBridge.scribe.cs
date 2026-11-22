using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis;

internal sealed class RefinedBMVPositiveCenterBoundaryBridgeDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/HilbertOperators/hagele2026refinedbmv");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A mixed derivative criterion for refined BMV",
        H("A mixed derivative criterion for refined BMV with three copies of the second factor"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("refined-bmv-positive-center-mixed-derivative-criterion"),
                DeclarationHandle.Create("D5/S3/Quantum/Analysis/RefinedBMVPositiveCenterBoundaryBridge.upperPSD_of_logKernel_mixed"),
                H("The normalized kernel controls every finite spectral sample"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For a fixed positive integer first degree, suppose the mixed derivative of the normalized upper kernel " +
                    "is nonpositive at every ordered pair of positive logarithmic coordinates. The two endpoint limits give " +
                    "the missing edge inequalities for the interval Gram decomposition. This proves positive semidefiniteness " +
                    "on arbitrary finite samples at positive centers, including repeated points. For a fixed sample, continuity " +
                    "of the unnormalized kernel and closedness of the positive semidefinite cone give the result at a zero center. " +
                    "The criterion supplies the upper block in the existing product and exponential trace comparisons."))),
                DescribeRole.Theorem))));
}
