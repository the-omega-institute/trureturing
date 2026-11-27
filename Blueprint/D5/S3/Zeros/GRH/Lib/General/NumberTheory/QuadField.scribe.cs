using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.General.NumberTheory;

internal sealed class QuadFieldDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Quad Field", H("Quad Field"),
        Blocks(
            Paragraph(Text("Imaginary quadratic field Q(√-d): degree, CM structure, integers, different, quadratic character.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/General/NumberTheory/QuadField.totient_mul_totient_le_finrank"),
                H("totient_mul_totient_le_finrank"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("If a number field M contains primitive roots of unity of coprime orders n and d, then its degree over ℚ is at least φ(d)φ(n).")))))));
}
