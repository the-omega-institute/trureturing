using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.HardCore;

internal sealed class IndependentPartitionDeletionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The hard-core partition is a sum over Mathlib independent subsets of the actual finite domain.",
        H("Independent-set partition and deletion"),
        Blocks(
            Describe.Lean(DescribeId.Create("hc-independent-configurations"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/IndependentPartitionDeletion.configurations"),
                H("Actual independent configurations"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Filter the powerset of the actual finite vertex domain using Mathlib IsIndepSet. The ambient graph can have infinitely many vertices."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("hc-weighted-partition"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/IndependentPartitionDeletion.partition"),
                H("Multivariate partition sum"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Sum the product of the activities of the occupied vertices. This definition does not use a deletion recursion or an external count oracle."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("hc-closed-complement"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/IndependentPartitionDeletion.closedComplement"),
                H("Delete the closed neighborhood"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Remove the root and its neighbors within the actual finite domain."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("hc-partition-delete"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/IndependentPartitionDeletion.partition_delete"),
                H("Denominator-free deletion identity"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Split independent configurations according to root occupancy. Insertion of the root is an injective map from configurations on the closed-complement domain. The resulting identity holds in every commutative semiring, including polynomial rings and complex numbers, without assuming any partition nonzero."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("hc-partition-empty"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/IndependentPartitionDeletion.partition_empty"),
                H("Empty-domain normalization"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The only configuration on the empty domain is the empty set, with weight one."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("hc-map-partition"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/IndependentPartitionDeletion.map_partition"),
                H("Scalar evaluation preserves configurations"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A semiring homomorphism changes the activities while preserving the exact family of independent sets."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("hc-independence-polynomial"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/IndependentPartitionDeletion.independencePolynomial"),
                H("The independence polynomial"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Assign the polynomial variable to every vertex in the weighted partition sum over integer polynomials."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("hc-independence-polynomial-eval"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/IndependentPartitionDeletion.independencePolynomial_eval"),
                H("Complex evaluation is the actual partition"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Evaluation at a complex activity gives exactly the finite independent-set sum to which the deletion identity applies."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("hc-one-le-partition"),
                DeclarationHandle.Create("D5/S3/StatisticalMechanics/HardCore/IndependentPartitionDeletion.one_le_partition"),
                H("Nonnegative real activities"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("All configuration weights are nonnegative and the empty configuration contributes one. This supplies the real-domain normalization used before complex continuation."))), DescribeRole.Theorem),
            Paragraph(Text("The deletion identity is classical. This source supplies the actual configuration semantics needed by the hard-core research lane. The proof scripts are logically reviewed candidates; Lean elaboration and Scribe emission have not been executed in the authoring runtime.")))));
}
