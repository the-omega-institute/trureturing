using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal.TypeA.CharacteristicTwo;

internal sealed class PartIISLnF2PivotPathDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Type-A SLn F2 Pivot Path.",
        H("Type-A SLn F2 Pivot Path"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("typea-partiislnf2pivotpath-strict-mul-second"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/CharacteristicTwo/PartIISLnF2PivotPath.strict_mul_second"),
                H("strict mul second"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual second superdiagonal of a product of strict upper matrices."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-partiislnf2pivotpath-commuting-simple-wedge"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/CharacteristicTwo/PartIISLnF2PivotPath.commuting_simple_wedge"),
                H("commuting simple wedge"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Genuine commutation forces the two adjacent simple coordinates to have zero wedge; this is a literal matrix-entry computation."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-partiislnf2pivotpath-simple-roots-commute"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/CharacteristicTwo/PartIISLnF2PivotPath.simple_roots_commute"),
                H("simple roots commute"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Nonadjacent actual simple root elements commute."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-partiislnf2pivotpath-normalized-pivots-identity-or-reflection"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/CharacteristicTwo/PartIISLnF2PivotPath.normalized_pivots_identity_or_reflection"),
                H("normalized pivots identity or reflection"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The pivot permutation derived from a bare U-normalized automorphism is identity or reflection. No root-image or path-preservation premise is used."))),
                DescribeRole.Theorem),
            Paragraph(Text("Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics165 (2007),171-238, DOI10.4007/annals.2007.165.171, Section10, Proposition10.2 and equations(45)-(50). PartII: Products in quasisimple groups, Annals of Mathematics165 (2007),239-273, DOI10.4007/annals.2007.165.239, Theorem1.2, Lemma4.1, Sections2,5,6 and9, Proposition6.2, Propositions6.5 and6.7, and equation(13). The type-A arguments use explicit matrix and central-quotient geometry, finite-field arithmetic, Sylow conjugacy and constructive ordered class products. They establish the untwisted projective type-A family above uniform group-cardinality cutoffs. They do not establish exhaustion of all finite simple groups, general central covers, general width/RBP or strong completeness. The explicit fixed-power class and supported-factor width proofs replace the cited Section5 [SW]/[LS2] inputs in this type-A application. No originality claim or redistribution of the papers is made.")))));
}
