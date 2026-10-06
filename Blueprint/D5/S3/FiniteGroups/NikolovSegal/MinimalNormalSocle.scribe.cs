using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal;

internal sealed class MinimalNormalSocleDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual minimal normal subgroups form a characteristic socle. When that socle fills a centerless group, its factors are nonabelian simple and fully independent.",
        H("Minimal normal factors and the socle"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("nikolov-segal-minimalnormalsocle-minimalnormalfactor"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/MinimalNormalSocle.MinimalNormalFactor"),
                H("Actual minimal normal factors"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any group G, MinimalNormalFactor G consists of subgroups M minimal for the predicate that M is normal and not the bottom subgroup. The factors are actual subgroups of G."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-minimalnormalsocle-minimalnormalsocle"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/MinimalNormalSocle.minimalNormalSocle"),
                H("The socle is the join of the factors"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any group G, minimalNormalSocle G is the supremum of all its actual minimal nontrivial normal subgroups."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-minimalnormalsocle-minimal-normal-map-equiv"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/MinimalNormalSocle.minimal_normal_map_equiv"),
                H("Isomorphisms transport minimal normality"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For arbitrary groups G and Q, an isomorphism e from G to Q maps a minimal nontrivial normal subgroup of G to one of Q. Pullback and pushforward preserve nontriviality and the complete minimality condition."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-minimalnormalsocle-minimalnormalsocle-characteristic"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/MinimalNormalSocle.minimalNormalSocle_characteristic"),
                H("The socle is characteristic"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every automorphism permutes the actual minimal normal factors, so their join is characteristic. No finiteness assumption is needed."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-minimalnormalsocle-minimal-normal-factors-commute"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/MinimalNormalSocle.minimal_normal_factors_commute"),
                H("Distinct factors commute"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("In any group G, distinct minimal nontrivial normal subgroups intersect trivially. Their commutator subgroup lies in that intersection, so every element of one commutes with every element of the other."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-minimalnormalsocle-simple-minimal-normal-factor-of-socle-eq-top"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/MinimalNormalSocle.simple_minimal_normal_factor_of_socle_eq_top"),
                H("A full socle makes each factor simple"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If the socle of any group G is the top subgroup, every actual minimal normal factor is simple. A subgroup normal within one factor is normalized by that factor and centralized by every other factor, hence normalized by the full socle. Minimal normality then makes it trivial or the entire factor."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-minimalnormalsocle-minimal-normal-factors-independent"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/MinimalNormalSocle.minimal_normal_factors_independent"),
                H("Centerlessness gives full independence"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any group G with full socle and bottom center, each factor is disjoint from the join of all other factors. An element in the intersection commutes with every factor and hence belongs to the bottom center. This is full supremum independence, which is stronger than pairwise disjointness."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-minimalnormalsocle-noncommutative-minimal-normal-factor-of-socle-eq-top"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/MinimalNormalSocle.noncommutative_minimal_normal_factor_of_socle_eq_top"),
                H("Every factor is nonabelian"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any group G with full socle and bottom center, no minimal normal factor is commutative. A commutative factor would commute both with itself and with all other factors, placing it in the center and contradicting nontriviality."))),
                DescribeRole.Lemma))));
}
