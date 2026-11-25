using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Partitions;

internal sealed class BilgiciThetaGradingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Partitions/BilgiciThetaGrading.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Fourier/bilgici2026ninecolored");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Character projection in the theta quotient.",
        H("Character projection in the theta quotient"),
        Blocks(
            Describe.Lean(DescribeId.Create("bilgici-t-p"),
                DeclarationHandle.Create(Prefix + "T_P"), H("The projector lands in character four"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The nine signed doubling iterates define a linear projector. Shifting the index in the "
                    + "sum multiplies it by four."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("bilgici-eigengrade-exact"),
                DeclarationHandle.Create(Prefix + "eigengrade_exact"), H("Projected homogeneous representatives"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("In centered degree and weight the image of the projected homogeneous subspace is "
                    + "exactly the doubling eigenspace inside that quotient grade."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("bilgici-theta-annihilated"),
                DeclarationHandle.Create(Prefix + "theta_annihilated"), H("Signed field relations descend to zero"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The signed integer indices give a field-indexed re-pairing relation. Its projected "
                    + "class vanishes in the global theta quotient."))), DescribeRole.Theorem))));
}
