using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal;

internal sealed class LargeMinimalNormalStructureDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A fixed factorial cutoff and large alternating-section degree force every actual factor of a finite minimal normal subgroup to be nonabelian simple of order above the cutoff.",
        H("Large minimal normal subgroups"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("nikolov-segal-largeminimalnormalstructure-commutative-section"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/LargeMinimalNormalStructure.commutative_section"),
                H("Sections of commutative groups are commutative"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For arbitrary groups G and A, if G is commutative and A is a section of G, then A is commutative. Lift any two elements through the section surjection and use commutativity in its arbitrary subgroup."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-largeminimalnormalstructure-noncommutative-of-large-alpha"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/LargeMinimalNormalStructure.noncommutative_of_large_alpha"),
                H("Large alternating-section degree implies noncommutativity"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every finite group G and natural k with four at most k, alpha(G) greater than k implies G is noncommutative. A commutative alternating section has degree at most three, contradicting the bound. Here alpha is the largest degree of an alternating section formed from an arbitrary subgroup."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-largeminimalnormalstructure-large-minimal-normal-structure"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/LargeMinimalNormalStructure.large_minimal_normal_structure"),
                H("Every factor exceeds the fixed cutoff"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For arbitrary natural C and k with four at most k and twice C less than k factorial, every finite ambient group G and minimal nontrivial normal subgroup N with alpha(N) greater than k satisfies: N is perfect and its center is bottom; every actual minimal normal factor of N is nonabelian simple and has order greater than C; their internal product is isomorphic to N. The actual factor family and factors are finite. An alternating section of degree alpha(N) occurs in one factor and bounds its order from below; ambient factor conjugacy transfers that bound to every factor. No decomposition or conjugacy premise is assumed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-largeminimalnormalstructure-large-minimal-normal-proposition2-data"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/LargeMinimalNormalStructure.large_minimal_normal_proposition2_data"),
                H("The central quotient has the required large simple factors"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Under the same fixed C and k, finite ambient G, minimal nontrivial normal N and alpha(N) greater than k, N is perfect, every actual factor is nonabelian simple of order greater than C, and N modulo its center is isomorphic to the actual product of those factors. This supplies the elementary structural hypotheses preceding the coset-power theorem. Uniform prescribed-coset power surjectivity remains an additional unproved input; this conclusion gives no uniform absorption, power width or strong completeness theorem."))),
                DescribeRole.Theorem))));
}
