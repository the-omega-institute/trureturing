using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal;

internal sealed class QuantitativeExtractionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Quantitative literal extraction.",
        H("Quantitative literal extraction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("nikolov-segal-quantitativeextraction-balanced-colour-crossing"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/QuantitativeExtraction.balanced_colour_crossing"),
                H("balanced colour crossing"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A balanced literal word with more keys than its compressed colour bound contains a crossing whose ADCBE remainder retains that bound."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-quantitativeextraction-extraction-exists"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/QuantitativeExtraction.extraction_exists"),
                H("extraction exists"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Support at least n+2D and colour bound n construct an actual D-step extraction. Balance and the same colour bound survive, and final support plus 2D equals the initial support."))),
                DescribeRole.Theorem),
            Paragraph(Text("Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics 165 (2007), 171-238, DOI 10.4007/annals.2007.165.171, Section 8, Lemma 8.3 and Proposition 8.4, Section 9, Proposition 9.1 (pages 223-226), and Section 10, Proposition 10.2 and equations (45)-(50) (pages 228-232). Part II: Products in quasisimple groups, Annals of Mathematics 165 (2007), 239-273, DOI 10.4007/annals.2007.165.239, Theorem 1.2 and Lemma 4.1 (pages 247-248). These are formal adaptations and conditional consequences of published mathematics, with elementary finite-set growth supporting bounded-small coverage; no originality claim or redistribution of the papers is made. Large-simple scalar PRODUCT existence, quasisimple central covers, all-length Proposition 10.2, uniform width and restricted Burnside bounds, and full strong completeness remain unproved.")))));
}
