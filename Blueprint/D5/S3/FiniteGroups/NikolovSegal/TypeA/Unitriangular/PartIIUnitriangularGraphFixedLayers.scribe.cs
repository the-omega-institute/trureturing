using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal.TypeA.Unitriangular;

internal sealed class PartIIUnitriangularGraphFixedLayersDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Type-A Unitriangular Graph Fixed Layers.",
        H("Type-A Unitriangular Graph Fixed Layers"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("typea-partiiunitriangulargraphfixedlayers-actual-uniform-field-graph-fixed-layer-product"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularGraphFixedLayers.actual_uniform_field_graph_fixed_layer_product"),
                H("actual uniform field graph fixed layer product"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Actual fixed-layer product for arbitrary field/positive-graph tuples. It consumes doubled-exponent Lemma7.1 and actual norm witnesses to supply the PRESCRIBED divisor powers. Both printed leading-layer batches follow, including graph reversal signs in characteristic two. Corrections precede every target and the quantitative constants are independent of rank."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-partiiunitriangulargraphfixedlayers-actual-uniform-field-graph-u-product"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularGraphFixedLayers.actual_uniform_field_graph_U_product"),
                H("actual uniform field graph U product"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Full printed Proposition6.5 for actual prescribed field/positive-graph tuples on arbitrary-rank SL. Four ordered batches and one proper final correction cover the ENTIRE U. All divisor powers, reflection signs and noncommutative accumulation are genuine. The single correction tuple precedes every target; length 4M+1 and the cutoff are uniform in rank. Bare automorphism normalization and full group assembly remain separate."))),
                DescribeRole.Theorem),
            Paragraph(Text("Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics165 (2007),171-238, DOI10.4007/annals.2007.165.171, Section10, Proposition10.2 and equations(45)-(50). PartII: Products in quasisimple groups, Annals of Mathematics165 (2007),239-273, DOI10.4007/annals.2007.165.239, Theorem1.2, Lemma4.1, Sections2,5,6 and9, Proposition6.2, Propositions6.5 and6.7, and equation(13). The type-A arguments use explicit matrix and central-quotient geometry, finite-field arithmetic, Sylow conjugacy and constructive ordered class products. They establish the untwisted projective type-A family above uniform group-cardinality cutoffs. They do not establish exhaustion of all finite simple groups, general central covers, general width/RBP or strong completeness. The explicit fixed-power class and supported-factor width proofs replace the cited Section5 [SW]/[LS2] inputs in this type-A application. No originality claim or redistribution of the papers is made.")))));
}
