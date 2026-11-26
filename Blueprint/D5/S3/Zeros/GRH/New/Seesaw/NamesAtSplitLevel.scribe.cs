using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.Seesaw;

internal sealed class NamesAtSplitLevelDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Names At Split Level", H("Names At Split Level"),
        Blocks(
            Paragraph(Text("Abstract lift laws mod N; Gauss-sum Hecke operator slides through a chain of lifts. Jointly invariant chain of lifts is a plain sum over tuples of classes. Translates with denominator N on a pair rewritten as named data modulo N.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/Seesaw/NamesAtSplitLevel.translateSum_eq_sum_name"),
                H("translateSum_eq_sum_name"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Let P, S satisfy IsSplitLevel for N with P ∪ P̄ = S ∪ S̄, and u, u' be the projections Space.projOn S of v, v'. Then τ_N(u ⊗ u') at S is ∑_z (𝐛_z(·D) ⊗ v) ⊗ (𝐜_z(D'·) ⊗ v'), names at P, with D, D' = diag(1, …, 1, N) on P ∩ S, P ∖ S.")))))));
}
