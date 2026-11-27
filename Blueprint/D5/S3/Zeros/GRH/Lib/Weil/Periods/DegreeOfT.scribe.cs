using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Weil.Periods;

internal sealed class DegreeOfTDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Degree Of T", H("Degree Of T"),
        Blocks(
            Paragraph(Text("Minus the additive valuation, −ord_w, of a finite idele. The base point T: degree, invariance modulo degree zero, T*T equals the shift.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Weil/Periods/DegreeOfT.formAdjoint_stringMap_mul_stringMap"),
                H("formAdjoint_stringMap_mul_stringMap"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For s' = s − 1, 𝖳*𝖳 is the shift Grading.shift of Y (X ↦ 0, e_i ↦ c·e_{i+1}, times −N at grade 0 and −Nc at grade 1); if Y, Y' have the same c, 𝖳𝖳* is the shift of Y'.")))))));
}
