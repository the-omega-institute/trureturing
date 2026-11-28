using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Selmer;

internal sealed class ValueFamiliesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Value Families", H("Value Families"),
        Blocks(
            Paragraph(Text("Group-ring interpolation of twisted Hecke values, carried to the Galois side as families.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Selmer/ValueFamilies.exists_isFamily"),
                H("exists_isFamily"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For chosen w ∤ ℓ with tame generator σ, ramified p and a sign s, some family (ν, L) (IsFamily) has all v(ν_i(σ) − 1) ≤ v(Nw − 1), and vL(Q, avatar of τ⁻¹) ≤ c + vL(∅,1) implies v(ιρ) ≤ c, for c ≥ 0, twists τ with Q auxiliary, ρ = Data.Pair.ratio p τ s.")))))));
}
