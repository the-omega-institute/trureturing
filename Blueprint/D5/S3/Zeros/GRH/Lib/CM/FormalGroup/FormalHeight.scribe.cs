using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.CM.FormalGroup;

internal sealed class FormalHeightDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Formal Height", H("Formal Height"),
        Blocks(
            Paragraph(Text("Chowla-Selberg area formula for conjugates; soft CM main theorem; sums over ideal classes. Vanishing Hasse invariant forces a non-split prime and a large coefficient. Endomorphism of odd degree q has a unit coefficient in degree at most q.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/CM/FormalGroup/FormalHeight.exists_unit_coeff_degree_le"),
                H("exists_unit_coeff_degree_le"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let Z = X + ⋯ with f(Z) integral for all f ∈ 𝔬[[φ]], let aΛ ⊂ Λ with aā = q odd, and let g be integral without constant term, Z(g) = ι(a)Z. Then g has a unit coefficient in some degree ≤ q.")))))));
}
