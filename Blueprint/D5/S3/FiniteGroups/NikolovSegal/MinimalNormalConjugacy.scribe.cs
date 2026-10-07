using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal;

internal sealed class MinimalNormalConjugacyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ambient conjugates of a nontrivial subgroup fill a minimal normal subgroup; ambient conjugation is transitive on its nonabelian simple factors.",
        H("Ambient conjugacy of the actual factors"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("nikolov-segal-minimalnormalconjugacy-conjugate-join-of-minimal-normal"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/MinimalNormalConjugacy.conjugate_join_of_minimal_normal"),
                H("Ambient conjugates join to the whole subgroup"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any group G, normal minimal nontrivial subgroup N, and nontrivial subgroup M of N, the join of M mapped by the restrictions of conjugation by all g in G is top in N. The image of that join in G is normal and nontrivial, so minimal normality applies."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-minimalnormalconjugacy-minimal-normal-factors-conjugate"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/MinimalNormalConjugacy.minimal_normal_factors_conjugate"),
                H("Ambient conjugation is transitive on factors"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every finite group G and normal minimal nontrivial subgroup N that is nonabelian, any two actual minimal normal factors of N are conjugate by an element of G. If all conjugates of one factor differed from the other, their full join would centralize the other, contradicting centerlessness."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-minimalnormalconjugacy-minimal-normal-factors-isomorphic"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/MinimalNormalConjugacy.minimal_normal_factors_isomorphic"),
                H("All factors are isomorphic"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Under the same finite ambient group, minimal normality and nonabelian hypotheses, any two actual factors are isomorphic via ambient conjugation. Their orders therefore agree."))),
                DescribeRole.Lemma))));
}
