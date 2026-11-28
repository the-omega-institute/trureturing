using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Shimura.TraceFormula;

internal sealed class MarkedEqDefiniteDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Marked Eq Definite", H("Marked Eq Definite"),
        Blocks(
            Paragraph(Text("Non-elliptic terms vanish for a cuspidal type, so marked and definite counts agree.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Shimura/TraceFormula/MarkedEqDefinite.sum_countTerm_marked_eq_definite"),
                H("sum_countTerm_marked_eq_definite"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let E⁺ ≠ ℚ, n odd, 𝔑 neat, f a regular Hecke function of level K(𝔑), χ-eigen under left translation by J at w₀ with χ cuspidal, both unweighted counts finite modulo GL_n(E). Then for any weight w the marked and definite orbit sums agree.")))))));
}
