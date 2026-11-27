using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.New.RealPlace;

internal sealed class LocalTheoremDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Local Theorem", H("Local Theorem"),
        Blocks(
            Paragraph(Text("Local theorem: weighted bounds for pairings of cut Bessel kernels, descent between floors.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/New/RealPlace/LocalTheorem.formModulus_sq_le_of_heads"),
                H("formModulus_sq_le_of_heads"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("Local theorem, unequal heads. Let 𝖬 be Haar, W cut, p a head of length j, 1 ≤ j ≤ ϱ, x a position. If the unit ξ equals (1/p_j − 1/q_j)/g for the last entries, then 𝖥_j(x; 1)² ≤ (c/md ξ)^{|ι|} 𝖣_j(x).")))))));
}
