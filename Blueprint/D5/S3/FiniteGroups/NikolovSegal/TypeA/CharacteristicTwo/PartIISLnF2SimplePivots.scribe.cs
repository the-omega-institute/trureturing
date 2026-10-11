using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal.TypeA.CharacteristicTwo;

internal sealed class PartIISLnF2SimplePivotsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Type-A SLn F2 Simple Pivots.",
        H("Type-A SLn F2 Simple Pivots"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("typea-partiislnf2simplepivots-minor-simple-unique"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/CharacteristicTwo/PartIISLnF2SimplePivots.minor_simple_unique"),
                H("minor simple unique"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A genuine rank-one upper-unitriangular matrix has at most one nonzero simple-root pivot, including characteristic two."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-partiislnf2simplepivots-simpleentry-mul"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/CharacteristicTwo/PartIISLnF2SimplePivots.simpleEntry_mul"),
                H("simpleEntry mul"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Literal simple coordinates add under multiplication of actual U matrices."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-partiislnf2simplepivots-uplus-le-of-simple-roots"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/CharacteristicTwo/PartIISLnF2SimplePivots.Uplus_le_of_simple_roots"),
                H("Uplus le of simple roots"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Subgroup form of the simple-root generation argument. It consumes the Gaussian U generation and actual commutator relation."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-partiislnf2simplepivots-simple-image-column-coverage"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/CharacteristicTwo/PartIISLnF2SimplePivots.simple_image_column_coverage"),
                H("simple image column coverage"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Surjectivity on actual U and its genuine simple-root generation imply that every target simple coordinate occurs in an actual simple-root image."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-partiislnf2simplepivots-normalized-simple-pivot-permutation"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/CharacteristicTwo/PartIISLnF2SimplePivots.normalized_simple_pivot_permutation"),
                H("normalized simple pivot permutation"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every normalized bare automorphism has a genuine permutation of all simple pivots. No root-subgroup-image premise is introduced."))),
                DescribeRole.Theorem),
            Paragraph(Text("Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics165 (2007),171-238, DOI10.4007/annals.2007.165.171, Section10, Proposition10.2 and equations(45)-(50). PartII: Products in quasisimple groups, Annals of Mathematics165 (2007),239-273, DOI10.4007/annals.2007.165.239, Theorem1.2, Lemma4.1, Sections2,5,6 and9, Proposition6.2, Propositions6.5 and6.7, and equation(13). The type-A arguments use explicit matrix and central-quotient geometry, finite-field arithmetic, Sylow conjugacy and constructive ordered class products. They establish the untwisted projective type-A family above uniform group-cardinality cutoffs. They do not establish exhaustion of all finite simple groups, general central covers, general width/RBP or strong completeness. The explicit fixed-power class and supported-factor width proofs replace the cited Section5 [SW]/[LS2] inputs in this type-A application. No originality claim or redistribution of the papers is made.")))));
}
