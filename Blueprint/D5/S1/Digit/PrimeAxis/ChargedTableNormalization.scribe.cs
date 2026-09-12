using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit.PrimeAxis;

internal sealed class ChargedTableNormalizationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Charged Table Normalization.",
        H("Charged Table Normalization"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("chargedtablenormalization-exists-tablepath-rownormalize"),
                DeclarationHandle.Create("D5/S1/Digit/PrimeAxis/ChargedTableNormalization.exists_tablePath_rowNormalize"),
                H("A finite sequence normalizes the entire table"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every finitely supported prime-indexed raw table reaches its rowwise normal form "
                    + "by one finite sequence of single-row carry steps. Each step acts on one prime row "
                    + "and leaves every other row unchanged. The charge is a finitely supported "
                    + "prime-indexed integer function, obtained by adding each step's charge at its "
                    + "selected prime. Empty tables and empty paths are included."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("chargedtablenormalization-tablepath-project"),
                DeclarationHandle.Create("D5/S1/Digit/PrimeAxis/ChargedTableNormalization.tablePath_project"),
                H("Projection preserves the charge at each prime"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every finite table path and every prime, the source row reduces to the "
                    + "endpoint row by a finite charged raw carry path. Its total charge is exactly "
                    + "the table path's charge at that prime. Steps acting on another row leave "
                    + "both this row and its accumulated charge unchanged."))),
                DescribeRole.Theorem))));
}
