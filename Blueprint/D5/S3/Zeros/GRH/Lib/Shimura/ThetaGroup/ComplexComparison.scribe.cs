using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Shimura.ThetaGroup;

internal sealed class ComplexComparisonDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complex Comparison", H("Complex Comparison"),
        Blocks(
            Paragraph(Text("Sections over a valuation ring as theta functions; lifted translations, commutators, orbit lattices.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Shimura/ThetaGroup/ComplexComparison.exists_sections_of_translation_stable"),
                H("exists_sections_of_translation_stable"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let N, an O-module of sections containing the coordinates, be stable under lifts of translations by Λ^∨; nΛ^∨ ⊂ Λ, n a unit, B positive. Finitely many theta functions f_j, not all zero, have multiples γf_j in N, γ ≠ 0, not all vanishing on any Λ^∨-orbit of a field-valued point.")))))));
}
