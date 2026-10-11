using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal.TypeA.Unitriangular;

internal sealed class SLnUnipotentBlocksDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Type-A SLn Unipotent Blocks.",
        H("Type-A SLn Unipotent Blocks"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("typea-slnunipotentblocks-embed"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/SLnUnipotentBlocks.embed"),
                H("embed"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Genuine determinant-one Levi embedding, with the last coordinate fixed."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("typea-slnunipotentblocks-upperrad"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/SLnUnipotentBlocks.upperRad"),
                H("upperRad"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Actual last-column upper unipotent matrices."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("typea-slnunipotentblocks-lowerrad"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/SLnUnipotentBlocks.lowerRad"),
                H("lowerRad"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Actual last-row lower unipotent matrices."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("typea-slnunipotentblocks-embed-conjugate-upperrad"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/SLnUnipotentBlocks.embed_conjugate_upperRad"),
                H("embed conjugate upperRad"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every actual Levi element normalizes the full last-column radical."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-slnunipotentblocks-embed-conjugate-lowerrad"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/SLnUnipotentBlocks.embed_conjugate_lowerRad"),
                H("embed conjugate lowerRad"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every actual Levi element normalizes the full last-row radical."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-slnunipotentblocks-embed-mul-upper"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Unitriangular/SLnUnipotentBlocks.embed_mul_upper"),
                H("embed mul upper"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Upper-triangular Levi factors and upper radicals remain literally upper unitriangular in the canonical Fin(r+1) coordinates."))),
                DescribeRole.Theorem),
            Paragraph(Text("Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics165 (2007),171-238, DOI10.4007/annals.2007.165.171, Section10, Proposition10.2 and equations(45)-(50). PartII: Products in quasisimple groups, Annals of Mathematics165 (2007),239-273, DOI10.4007/annals.2007.165.239, Theorem1.2, Lemma4.1, Sections2,5,6 and9, Proposition6.2, Propositions6.5 and6.7, and equation(13). The type-A arguments use explicit matrix and central-quotient geometry, finite-field arithmetic, Sylow conjugacy and constructive ordered class products. They establish the untwisted projective type-A family above uniform group-cardinality cutoffs. They do not establish exhaustion of all finite simple groups, general central covers, general width/RBP or strong completeness. The explicit fixed-power class and supported-factor width proofs replace the cited Section5 [SW]/[LS2] inputs in this type-A application. No originality claim or redistribution of the papers is made.")))));
}
