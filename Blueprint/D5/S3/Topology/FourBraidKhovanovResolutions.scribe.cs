using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology;

internal sealed class FourBraidKhovanovResolutionsDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Topology/FourBraidKhovanovResolutions.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Quantum grading of the four-braid resolution cube",
        H("Quantum grading of the four-braid resolution cube"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("four-braid-top-quantum-bound"),
                DeclarationHandle.Create(Owner + "upperQuantum_bound"),
                H("Bounds from all smoothing choices"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The closed braid contains eleven signed crossings. Each smoothing choice "
                    + "selects one matching at each crossing and closes the last slice onto the "
                    + "first. The normalized quantum degree of the all-one label on any smoothing "
                    + "is odd and at most 21. The verified finite computation uses the actual "
                    + "circles from the matching graph. Changing a circle label to X decreases "
                    + "the quantum degree by two."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("four-braid-no-basis-in-higher-grading"),
                DeclarationHandle.Create(Owner + "basis_empty_of_above_or_even"),
                H("Higher and even quantum gradings have empty bases"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every cohomological degree has an empty basis in any even quantum grading "
                    + "and in every quantum grading above 21. Thus the comparison with the first "
                    + "nonzero row starting at the diagram's potential top needs only the odd "
                    + "gradings 21, 19 and 17."))),
                DescribeRole.Theorem))));
}
