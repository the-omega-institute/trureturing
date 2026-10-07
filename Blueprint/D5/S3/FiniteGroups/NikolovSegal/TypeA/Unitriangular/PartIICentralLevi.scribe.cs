using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal.TypeA.Unitriangular;

internal sealed class PartIICentralLeviDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Type-A Central Levi.",
        H("Type-A Central Levi"),
        Blocks(
            Paragraph(Text("Part II p255: actual central SL(n-2), with full diagonal actions implemented by determinant-one ambient inner corrections.")),
            Describe.Lean(
                DescribeId.Create("typea-partiicentrallevi-embed"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIICentralLevi.embed"),
                H("embed"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The genuine central Levi embedding, fixing the first and last factors."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("typea-partiicentrallevi-actual-central-levi-action"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIICentralLevi.actual_central_levi_action"),
                H("actual central levi action"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Full actual ambient field/graph/diagonal action intertwines with the central action, including inverse-transpose and its signs."))),
                DescribeRole.Theorem),
            Paragraph(Text("Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics165 (2007),171-238, DOI10.4007/annals.2007.165.171, Section10, Proposition10.2 and equations(45)-(50). PartII: Products in quasisimple groups, Annals of Mathematics165 (2007),239-273, DOI10.4007/annals.2007.165.239, Theorem1.2, Lemma4.1, Sections2,5,6 and9, Proposition6.2, Propositions6.5 and6.7, and equation(13). The type-A arguments use explicit matrix and central-quotient geometry, finite-field arithmetic, Sylow conjugacy and constructive ordered class products. They establish the untwisted projective type-A family above uniform group-cardinality cutoffs. They do not establish exhaustion of all finite simple groups, general central covers, general width/RBP or strong completeness. The explicit fixed-power class and supported-factor width proofs replace the cited Section5 [SW]/[LS2] inputs in this type-A application. No originality claim or redistribution of the papers is made.")))));
}
