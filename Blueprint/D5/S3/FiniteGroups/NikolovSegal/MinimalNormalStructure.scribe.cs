using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal;

internal sealed class MinimalNormalStructureDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A nonabelian minimal nontrivial normal subgroup of a finite ambient group is perfect and centerless, and its canonical internal product of actual minimal normal factors is isomorphic to it.",
        H("Elementary minimal normal structure"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("nikolov-segal-minimalnormalstructure-characteristic-subgroup-of-minimal-normal"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/MinimalNormalStructure.characteristic_subgroup_of_minimal_normal"),
                H("Characteristic subgroups are trivial or full"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any group G and minimal nontrivial normal subgroup N, every characteristic subgroup K of N is bottom or top. Its image in G is normal, and minimal normality of N applies. No finiteness or nonabelian hypothesis is required."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-minimalnormalstructure-perfect-centerless-minimal-normal"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/MinimalNormalStructure.perfect_centerless_minimal_normal"),
                H("Nonabelian minimal normal subgroups are perfect and centerless"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any group G and nonabelian minimal nontrivial normal subgroup N, the commutator subgroup of N is top and its center is bottom. Both are characteristic; their opposite possibilities would make N commutative."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-minimalnormalstructure-socle-of-finite-minimal-normal"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/MinimalNormalStructure.socle_of_finite_minimal_normal"),
                H("The finite minimal normal subgroup has full socle"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every finite ambient group G and minimal nontrivial normal subgroup N, the socle of N is top, including when N is abelian. A finite nontrivial group has a minimal nontrivial normal subgroup, so the characteristic socle cannot be bottom."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-minimalnormalstructure-socleproductequiv"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/MinimalNormalStructure.socleProductEquiv"),
                H("The canonical internal product is an isomorphism"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a finite group G with full socle and bottom center, socleProductEquiv maps the product of its actual minimal normal factors isomorphically onto G. The index family and each factor are finite. The canonical product homomorphism is surjective by the full socle and injective by full supremum independence."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-minimalnormalstructure-minimal-normal-nonabelian-direct-product"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/MinimalNormalStructure.minimal_normal_nonabelian_direct_product"),
                H("The elementary nonabelian decomposition"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every finite ambient group G and nonabelian minimal nontrivial normal subgroup N, N is perfect and centerless, every actual minimal normal factor of N is nonabelian simple, and the internal product of these factors is isomorphic to N. The proof uses characteristic subgroups, the socle and internal products; no classification of finite simple groups or power bound is assumed."))),
                DescribeRole.Theorem))));
}
