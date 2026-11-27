using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Shimura.Transfer;

internal sealed class MarkedPairsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Marked Pairs", H("Marked Pairs"),
        Blocks(
            Paragraph(Text("Conjugation invariance of the count; reflections commuting with a regular matrix.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Shimura/Transfer/MarkedPairs.isReflection_eigenReflection"),
                H("isReflection_eigenReflection"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let P = det(X − y) be separable, J_ν = eigenReflection True y ν. For roots μ of Φ_{v₀}P, J_μ is a reflection; each reflection J commuting with Φ_{v₀}(y) has a root μ: Φ_{v₀}(y)(J+1) = μ(J+1), and J = J_ν iff ν = μ.")))))));
}
