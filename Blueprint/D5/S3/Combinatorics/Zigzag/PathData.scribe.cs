using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Zigzag;

internal sealed class PathDataDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Zigzag/PathData.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite two-sector path type retains every form label, charge, and parity-specific boundary needed for the literal count.",
        H("Labelled Retirement Path Data"),
        Blocks(
            Describe.Lean(DescribeId.Create("shared-state-topology"),
                DeclarationHandle.Create(Prefix + "stepTargets"), H("Five states and twelve exits"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "States A, D, E, H, I have respectively four, four, two, one, and one possible next states. This topology is shared by the positive and negative imbalance sectors; it does not identify their directed form labels."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("positive-labelled-steps"),
                DeclarationHandle.Create(Prefix + "positiveStepLabel"), H("Positive-sector transition labels"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every one of the twelve exits carries an explicit low form, high form, and integer change of imbalance at +1. In state A, for example, the four charges are 1, 2, 0, -1. Separate indices preserve equal-weight but differently labelled transitions."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("negative-labelled-steps"),
                DeclarationHandle.Create(Prefix + "negativeStepLabel"), H("Negative-sector transition labels"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The negative sector has twelve separately listed form pairs and charges on the same target indices. Its state-A charges are -1, -2, 0, 1; a reciprocal weight symmetry alone cannot recover these labels for the inverse choice map."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("parity-dependent-path-types"),
                DeclarationHandle.Create(Prefix + "OddPath"), H("The singleton-ended path type"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Both path types begin with one of two sector-specific class-two labels and recursively choose indexed interior steps. OddPath ends with a single form, while EvenPath ends with an antipodal form pair. The corresponding terminal tables exist only in states A and D; charges add through the complete path."))),
                DescribeRole.Definition)), []));
}
