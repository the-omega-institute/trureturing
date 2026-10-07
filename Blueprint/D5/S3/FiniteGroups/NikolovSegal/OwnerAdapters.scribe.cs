using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal;

internal sealed class OwnerAdaptersDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Signed-word and normalized-value correspondence.",
        H("Signed-word and normalized-value correspondence"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("nikolov-segal-owneradapters-balanced-of-owner-counts"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/OwnerAdapters.balanced_of_owner_counts"),
                H("balanced of owner counts"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual normalized signed occurrence formula implies balance of the literal signed word."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-owneradapters-support-eq-of-owner-counts"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/OwnerAdapters.support_eq_of_owner_counts"),
                H("support eq of owner counts"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("When each sign occurs once precisely on Y, the literal support equals Y."))),
                DescribeRole.Theorem),
            Paragraph(Text("Nikolov and Segal, On finitely generated profinite groups, I: Strong completeness and uniform bounds, Annals of Mathematics 165 (2007), 171-238, DOI 10.4007/annals.2007.165.171, Section 8, Lemma 8.3 and Proposition 8.4, Section 9, Proposition 9.1 (pages 223-226), and Section 10, Proposition 10.2 and equations (45)-(50) (pages 228-232). Part II: Products in quasisimple groups, Annals of Mathematics 165 (2007), 239-273, DOI 10.4007/annals.2007.165.239, Theorem 1.2 and Lemma 4.1 (pages 247-248). These are formal adaptations and conditional consequences of published mathematics, with elementary finite-set growth supporting bounded-small coverage; no originality claim or redistribution of the papers is made. Large-simple scalar PRODUCT existence, quasisimple central covers, all-length Proposition 10.2, uniform width and restricted Burnside bounds, and full strong completeness remain unproved.")))));
}
