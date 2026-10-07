using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal;

internal sealed class Equation47ColoursDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Compressed colour rank and crossing surgery.",
        H("Compressed colour rank and crossing surgery"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("nikolov-segal-equation47colours-ascendingrank-iff"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Equation47Colours.ascendingRank_iff"),
                H("ascendingRank iff"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The ascending rank is at most n exactly when the compressed generator list embeds as a sublist in colourBound(m,n)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-equation47colours-signedrank-link"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Equation47Colours.signedRank_link"),
                H("signedRank link"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Joining words along opposite occurrences bounds the new rank by the sum of their ranks."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-equation47colours-signedrank-cancel"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Equation47Colours.signedRank_cancel"),
                H("signedRank cancel"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Deleting adjacent opposite occurrences lowers the signed rank by at least one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-equation47colours-signedrank-crossing"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Equation47Colours.signedRank_crossing"),
                H("signedRank crossing"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The ordered ADCBE remainder of a literal crossing has no larger signed rank than the original word, with arbitrary generator colours and signs."))),
                DescribeRole.Theorem),
            Paragraph(Text("Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics 165 (2007), 171-238, DOI 10.4007/annals.2007.165.171, Section 8, Lemma 8.3 and Proposition 8.4, Section 9, Proposition 9.1 (pages 223-226), and Section 10, Proposition 10.2 and equations (45)-(50) (pages 228-232). Part II: Products in quasisimple groups, Annals of Mathematics 165 (2007), 239-273, DOI 10.4007/annals.2007.165.239, Theorem 1.2 and Lemma 4.1 (pages 247-248). These are formal adaptations and conditional consequences of published mathematics, with elementary finite-set growth supporting bounded-small coverage; no originality claim or redistribution of the papers is made. Large-simple scalar PRODUCT existence, quasisimple central covers, all-length Proposition 10.2, uniform width and restricted Burnside bounds, and full strong completeness remain unproved.")))));
}
