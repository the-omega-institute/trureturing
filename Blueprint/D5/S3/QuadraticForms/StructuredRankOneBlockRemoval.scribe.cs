using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuadraticForms;

internal sealed class StructuredRankOneBlockRemovalDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuadraticForms/mazhang2026scaleddowndate");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Removing a nondegenerate block A X G⁻¹ Xᵀ A subtracts the inertia of G, raises the nullity by k, and splits the kernel as ker A ⊕ im X.",
        H("Nondegenerate block removal"),
        Blocks(
            Describe.Lean(DescribeId.Create("block-removal-kernel-split"),
                DeclarationHandle.Create("D5/S3/QuadraticForms/StructuredRankOneBlockRemoval.kernel_split"),
                H("Kernel and rank after block removal, over any field"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Let A be any square matrix over a field and X a matrix with G = Xᵀ A X invertible, "
                    + "and put N = A − A X G⁻¹ Xᵀ A. Then X is injective, ker A and im X intersect "
                    + "trivially, ker N = ker A + im X, dim ker N = dim ker A + k and rank N + k = rank A. "
                    + "No symmetry is needed: N v = A(v − X c) with c = G⁻¹ Xᵀ A v, N vanishes on ker A and "
                    + "on im X, and X c ∈ ker A forces G c = 0."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("block-removal-result"),
                DeclarationHandle.Create("D5/S3/QuadraticForms/StructuredRankOneBlockRemoval.result"),
                H("Inertia, kernel and rank after block removal"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text(
                        "Let A be a real symmetric n × n matrix and X a real n × k matrix with G = Xᵀ A X "
                        + "invertible, and put N = A − A X G⁻¹ Xᵀ A. Then N and G are symmetric, "
                        + "n₊(A) = n₊(N) + n₊(G), n₋(A) = n₋(N) + n₋(G), and n₀(N) = n₀(A) + k. Moreover X is "
                        + "injective, ker A and im X intersect trivially, ker N = ker A + im X, and "
                        + "rank N + k = rank A.")),
                    Paragraph(Text(
                        "The block matrix A ⊕ 0 is congruent, by the unipotent matrix with X in its corner, "
                        + "to the matrix with blocks A, A X, Xᵀ A and G. Eliminating the off-diagonal blocks "
                        + "with G⁻¹ makes that matrix congruent to N ⊕ G. Sylvester's law of inertia and "
                        + "additivity over blocks give the positive and negative counts. N v = A(v − X c) with "
                        + "c = G⁻¹ Xᵀ A v, which shows ker N ⊆ ker A + im X; N vanishes on ker A and on "
                        + "im X since G⁻¹ G = 1; and X c ∈ ker A forces G c = 0, so c = 0. Dimension counting "
                        + "gives the nullity and rank. This is Corollary 3 of H. Ma and W. Zhang "
                        + "(DOI 10.5281/zenodo.23920598) on MathOverflow 513954, revision 2, extending Lucid's "
                        + "block-congruence mechanism (CC BY-SA 4.0) from one vector to a block."))),
                DescribeRole.Theorem))));
}
