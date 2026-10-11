using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal.TypeA.Unitriangular;

internal sealed class PartIIAmbientUnipotentDecompositionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Type-A Ambient Unipotent Decomposition.",
        H("Type-A Ambient Unipotent Decomposition"),
        Blocks(
            Paragraph(Text("Part II p255: the actual matrix equality U = U1 V.")),
            Describe.Lean(
                DescribeId.Create("typea-partiiambientunipotentdecomposition-centralpart"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIAmbientUnipotentDecomposition.centralPart"),
                H("centralPart"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Actual central principal SL block of an arbitrary ambient U target."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("typea-partiiambientunipotentdecomposition-actual-central-embed-unitriangular"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIAmbientUnipotentDecomposition.actual_central_embed_unitriangular"),
                H("actual central embed unitriangular"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The genuine Levi embedding preserves upper unitriangularity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-partiiambientunipotentdecomposition-actual-ambient-u-decomposition"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/PartIIAmbientUnipotentDecomposition.actual_ambient_U_decomposition"),
                H("actual ambient U decomposition"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact p255 decomposition. The middle block is constructed from b; the true ordered group residual is proved to belong to V."))),
                DescribeRole.Theorem),
            Paragraph(Text("Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics165 (2007),171-238, DOI10.4007/annals.2007.165.171, Section10, Proposition10.2 and equations(45)-(50). PartII: Products in quasisimple groups, Annals of Mathematics165 (2007),239-273, DOI10.4007/annals.2007.165.239, Theorem1.2, Lemma4.1, Sections2,5,6 and9, Proposition6.2, Propositions6.5 and6.7, and equation(13). The type-A arguments use explicit matrix and central-quotient geometry, finite-field arithmetic, Sylow conjugacy and constructive ordered class products. They establish the untwisted projective type-A family above uniform group-cardinality cutoffs. They do not establish exhaustion of all finite simple groups, general central covers, general width/RBP or strong completeness. The explicit fixed-power class and supported-factor width proofs replace the cited Section5 [SW]/[LS2] inputs in this type-A application. No originality claim or redistribution of the papers is made.")))));
}
