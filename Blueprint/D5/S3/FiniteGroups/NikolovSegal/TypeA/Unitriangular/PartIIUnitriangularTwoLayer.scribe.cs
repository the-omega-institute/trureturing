using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal.TypeA.Unitriangular;

internal sealed class PartIIUnitriangularTwoLayerDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Type-A Unitriangular Two Layer.",
        H("Type-A Unitriangular Two Layer"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("typea-partiiunitriangulartwolayer-actual-uniform-field-two-layer-lift"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIUnitriangularTwoLayer.actual_uniform_field_two_layer_lift"),
                H("actual uniform field two layer lift"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Genuine two-layer equation(16) lift, PartII pp266--267, for arbitrary prescribed FIELD tuples. Actual scalar product arithmetic fixes alternating corrections before all heights/targets. The real Lemma9.1 correction supplies the adjacent even coordinate; its noncommutative final factor is retained. This proves simultaneous kth/(k+1)st equations modulo U(k+2), not full U3 coverage, graph-tuple coverage or the all-simple uniform supplier."))),
                DescribeRole.Theorem),
            Paragraph(Text("Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics165 (2007),171-238, DOI10.4007/annals.2007.165.171, Section10, Proposition10.2 and equations(45)-(50). PartII: Products in quasisimple groups, Annals of Mathematics165 (2007),239-273, DOI10.4007/annals.2007.165.239, Theorem1.2, Lemma4.1, Sections2,5,6 and9, Proposition6.2, Propositions6.5 and6.7, and equation(13). The type-A arguments use explicit matrix and central-quotient geometry, finite-field arithmetic, Sylow conjugacy and constructive ordered class products. They establish the untwisted projective type-A family above uniform group-cardinality cutoffs. They do not establish exhaustion of all finite simple groups, general central covers, general width/RBP or strong completeness. The explicit fixed-power class and supported-factor width proofs replace the cited Section5 [SW]/[LS2] inputs in this type-A application. No originality claim or redistribution of the papers is made.")))));
}
