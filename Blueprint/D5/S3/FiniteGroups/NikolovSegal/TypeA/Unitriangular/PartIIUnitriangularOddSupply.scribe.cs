using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal.TypeA.Unitriangular;

internal sealed class PartIIUnitriangularOddSupplyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Type-A Unitriangular Odd Supply.",
        H("Type-A Unitriangular Odd Supply"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("typea-partiiunitriangularoddsupply-paritytorus"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularOddSupply.parityTorus"),
                H("parityTorus"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Alternating actual diagonal torus; every odd-height root has weight lambda or lambda^-1, independently of rank and height."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("typea-partiiunitriangularoddsupply-actual-uniform-field-odd-layer-product"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularOddSupply.actual_uniform_field_odd_layer_product"),
                H("actual uniform field odd layer product"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Rank-independent odd-layer value coverage, the field-action branch of printed PartII Lemma9.2. Two genuine alternating diagonal tuples are fixed before every odd height and every actual matrix target. The published field lemma is proved and consumed; there is no layer-coverage premise. Both scalar signs, all unused coordinates and the noncommutative product are retained. Graph-action layers and full even-layer induction remain separate obligations."))),
                DescribeRole.Theorem),
            Paragraph(Text("Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics165 (2007),171-238, DOI10.4007/annals.2007.165.171, Section10, Proposition10.2 and equations(45)-(50). PartII: Products in quasisimple groups, Annals of Mathematics165 (2007),239-273, DOI10.4007/annals.2007.165.239, Theorem1.2, Lemma4.1, Sections2,5,6 and9, Proposition6.2, Propositions6.5 and6.7, and equation(13). The type-A arguments use explicit matrix and central-quotient geometry, finite-field arithmetic, Sylow conjugacy and constructive ordered class products. They establish the untwisted projective type-A family above uniform group-cardinality cutoffs. They do not establish exhaustion of all finite simple groups, general central covers, general width/RBP or strong completeness. The explicit fixed-power class and supported-factor width proofs replace the cited Section5 [SW]/[LS2] inputs in this type-A application. No originality claim or redistribution of the papers is made.")))));
}
