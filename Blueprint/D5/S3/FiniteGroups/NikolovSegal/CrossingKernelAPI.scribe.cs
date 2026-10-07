using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal;

internal sealed class CrossingKernelAPIDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Proposition 8.4 and normalized-value inputs.",
        H("Proposition 8.4 and normalized-value inputs"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("nikolov-segal-crossingkernelapi-proposition8-4"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/CrossingKernelAPI.proposition8_4"),
                H("proposition8 4"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Balance, compressed colour bound n and support at least n+2D give a genuine D-step extraction, exactly 2D distinct selected keys, exact support loss, and a final residual avoiding those keys."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-crossingkernelapi-extraction-from-owner-counts"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/CrossingKernelAPI.extraction_from_owner_counts"),
                H("extraction from owner counts"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The proved normalized signed count formula and actual colour bound instantiate the literal extraction theorem on the actual root residual."))),
                DescribeRole.Theorem),
            Paragraph(Text("Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics 165 (2007), 171-238, DOI 10.4007/annals.2007.165.171, Section 8, Lemma 8.3 and Proposition 8.4, Section 9, Proposition 9.1 (pages 223-226), and Section 10, Proposition 10.2 and equations (45)-(50) (pages 228-232). Part II: Products in quasisimple groups, Annals of Mathematics 165 (2007), 239-273, DOI 10.4007/annals.2007.165.239, Theorem 1.2 and Lemma 4.1 (pages 247-248). These are formal adaptations and conditional consequences of published mathematics, with elementary finite-set growth supporting bounded-small coverage; no originality claim or redistribution of the papers is made. Large-simple scalar PRODUCT existence, quasisimple central covers, all-length Proposition 10.2, uniform width and restricted Burnside bounds, and full strong completeness remain unproved.")))));
}
