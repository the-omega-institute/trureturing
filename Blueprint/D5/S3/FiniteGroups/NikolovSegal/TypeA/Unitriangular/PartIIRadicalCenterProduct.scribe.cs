using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal.TypeA.Unitriangular;

internal sealed class PartIIRadicalCenterProductDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Type-A Radical Center Product.",
        H("Type-A Radical Center Product"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("typea-partiiradicalcenterproduct-actual-top-layer-radical"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIRadicalCenterProduct.actual_top_layer_radical"),
                H("actual top layer radical"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual top layer is the corner subgroup of V."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-partiiradicalcenterproduct-actual-zero-noncorner-top"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIRadicalCenterProduct.actual_zero_noncorner_top"),
                H("actual zero noncorner top"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every radical with zero noncorner coordinates is an actual corner matrix, retaining its arbitrary corner."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-partiiradicalcenterproduct-actual-inner-radical-center-product"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIRadicalCenterProduct.actual_inner_radical_center_product"),
                H("actual inner radical center product"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Genuine corner product. The highest-layer supplier is consumed with an actual determinant-one correction, original d powers, and exact equality (the next layer is zero)."))),
                DescribeRole.Theorem),
            Paragraph(Text("Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics165 (2007),171-238, DOI10.4007/annals.2007.165.171, Section10, Proposition10.2 and equations(45)-(50). PartII: Products in quasisimple groups, Annals of Mathematics165 (2007),239-273, DOI10.4007/annals.2007.165.239, Theorem1.2, Lemma4.1, Sections2,5,6 and9, Proposition6.2, Propositions6.5 and6.7, and equation(13). The type-A arguments use explicit matrix and central-quotient geometry, finite-field arithmetic, Sylow conjugacy and constructive ordered class products. They establish the untwisted projective type-A family above uniform group-cardinality cutoffs. They do not establish exhaustion of all finite simple groups, general central covers, general width/RBP or strong completeness. The explicit fixed-power class and supported-factor width proofs replace the cited Section5 [SW]/[LS2] inputs in this type-A application. No originality claim or redistribution of the papers is made.")))));
}
