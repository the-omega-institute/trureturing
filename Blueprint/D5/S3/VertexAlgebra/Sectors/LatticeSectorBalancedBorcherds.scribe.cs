using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Sectors;

internal sealed class LatticeSectorBalancedBorcherdsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/Sectors/LatticeSectorBalancedBorcherds.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Coupled balanced Jacobi cancellation", H("Coupled balanced Jacobi cancellation"), Blocks(
            Describe.Lean(DescribeId.Create("latticesectorbalancedborcherds-balanced"),
                DeclarationHandle.Create(Prefix + "balanced"),
                H("The actual balanced tree"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual coefficient is canonical(α+β,γ+δ)(canonical(α,β)u(-s-1)v)(-x-1)(canonical(γ,δ)t(-z-1)w). The coefficient order is [s,x,z]."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("latticesectorbalancedborcherds-clearedbalanced"),
                DeclarationHandle.Create(Prefix + "clearedBalanced"),
                H("Literal original clearing"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The finite j,l sum has coefficients (-1)^(j+l) binom(k,j) binom(k,l), and applies clearIterate k (a0+k-j) (a1+k-l) to the balanced coefficient at z-a2-j-l. It is exactly the expansion of (s+x)^a0 x^a1 z^a2 s^k (s+x-z)^k (x-z)^k. The full integer Borcherds identity is used. For fixed l and Jacobi offset i, the j-sum of its second term is the original u/t locality sum. Moving u past t places u directly on w at mode a0+k-j+i, where the original a0 cutoff kills it. No cutoff of u on t_z w is assumed or chosen. All finite-sum exchanges retain their actual finite-support proofs. Suppliers retain Bakalov--Kac, Matsuo--Nagatomo and Carnahan attribution."))), DescribeRole.Definition))));
}
