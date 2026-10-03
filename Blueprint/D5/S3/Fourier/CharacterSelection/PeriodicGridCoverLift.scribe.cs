using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.CharacterSelection;

internal sealed class PeriodicGridCoverLiftDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Fourier/CharacterSelection/PeriodicGridCoverLift.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Flat periodic binary labels lift uniquely to a twisted integer covering grid.",
        H("Periodic Grid Cover Lift"),
        Blocks(
            Describe.Lean(DescribeId.Create("pulled-horizontal"),
                DeclarationHandle.Create(Prefix + "pulledHorizontal"),
                H("Pulled-back horizontal label"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At integer coordinates (i,j), evaluate the periodic horizontal label "
                    + "at the residues of i modulo M and j modulo N."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("pulled-vertical"),
                DeclarationHandle.Create(Prefix + "pulledVertical"),
                H("Pulled-back vertical label"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At integer coordinates (i,j), evaluate the periodic vertical label "
                    + "at the residues of i modulo M and j modulo N."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("cover-lift"),
                DeclarationHandle.Create(Prefix + "IsCoverLift"),
                H("Anchored twisted cover lift"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A binary vertex field on all of Z x Z has the prescribed anchor, "
                    + "the two pulled-back adjacent edge differences, and horizontal and "
                    + "vertical period shifts equal to the two holonomies."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("flat-unique-cover-lift"),
                DeclarationHandle.Create(Prefix + "flat_unique_cover_lift"),
                H("Unique twisted lift of a flat periodic label"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For M,N at least three, every flat periodic ZMod 2 edge label and "
                    + "every binary anchor have exactly one lift to the integer grid. "
                    + "The lift has the pulled-back edge differences and gains the row "
                    + "or column holonomy under the corresponding period translation. "
                    + "The construction integrates the two seam terms using integer "
                    + "quotients; uniqueness follows from connectivity by unit steps.")),
                Paragraph(Text(
                    "The parity-independent horizontal seam with holonomy (1,0) "
                    + "and no periodic vertex gradient is already proved by "
                    + "PeriodicGridHolonomy.horizontal_seam_counterexample."))),
                DescribeRole.Theorem))));
}
