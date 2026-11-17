using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.DiophantineApproximation;

internal sealed class SimultaneousPhaseAlignmentDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/DiophantineApproximation/SimultaneousPhaseAlignment.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Simultaneous Dirichlet approximation aligns finitely many real phases and yields a cosine-alignment scale.",
        H("Simultaneous Phase Alignment"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("simultaneous-dirichlet"),
                DeclarationHandle.Create(Prefix + "simultaneous_dirichlet"),
                H("Simultaneous Dirichlet approximation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a positive integer Q and a finite family of real numbers indexed by Fin d, "
                    + "there is a positive integer q at most Q^d such that every q times a family member "
                    + "is within 1/Q of an integer. The same q works for all coordinates."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("simultaneous-cos-alignment"),
                DeclarationHandle.Create(Prefix + "simultaneous_cos_alignment"),
                H("Simultaneous cosine alignment"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a finite family of real frequencies and a real scale L at least one, "
                    + "there is a real y between L and L times 8^d such that every frequency phase "
                    + "has cosine at least cos(pi/4)."))),
                DescribeRole.Theorem))));
}
