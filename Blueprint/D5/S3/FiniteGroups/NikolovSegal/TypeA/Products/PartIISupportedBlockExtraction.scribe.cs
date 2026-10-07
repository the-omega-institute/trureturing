using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal.TypeA.Products;

internal sealed class PartIISupportedBlockExtractionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Type-A Supported Block Extraction.",
        H("Type-A Supported Block Extraction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("typea-partiisupportedblockextraction-principalupper"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Products/PartIISupportedBlockExtraction.principalUpper"),
                H("principalUpper"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Extract the genuine ordered principal submatrix; determinant1 follows from the actual ambient unitriangular entries, including d=0."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("typea-partiisupportedblockextraction-pad-double-support-first"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Products/PartIISupportedBlockExtraction.pad_double_support_first"),
                H("pad double support first"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The auxiliary second block really is identity: the embedded double matrix is supported ONLY on the first d selected coordinates."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("typea-partiisupportedblockextraction-supported-ext"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/TypeA/Products/PartIISupportedBlockExtraction.supported_ext"),
                H("supported ext"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Equality of supported matrices is determined by the ACTUAL principal entries; this includes empty coordinate supports."))),
                DescribeRole.Theorem),
            Paragraph(Text("Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics165 (2007),171-238, DOI10.4007/annals.2007.165.171, Section10, Proposition10.2 and equations(45)-(50). PartII: Products in quasisimple groups, Annals of Mathematics165 (2007),239-273, DOI10.4007/annals.2007.165.239, Theorem1.2, Lemma4.1, Sections2,5,6 and9, Proposition6.2, Propositions6.5 and6.7, and equation(13). The type-A arguments use explicit matrix and central-quotient geometry, finite-field arithmetic, Sylow conjugacy and constructive ordered class products. They establish the untwisted projective type-A family above uniform group-cardinality cutoffs. They do not establish exhaustion of all finite simple groups, general central covers, general width/RBP or strong completeness. The explicit fixed-power class and supported-factor width proofs replace the cited Section5 [SW]/[LS2] inputs in this type-A application. No originality claim or redistribution of the papers is made.")))));
}
