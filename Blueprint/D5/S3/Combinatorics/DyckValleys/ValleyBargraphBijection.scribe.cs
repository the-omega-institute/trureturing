using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.DyckValleys;

internal sealed class ValleyBargraphBijectionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/DyckValleys/ValleyBargraphBijection.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The boundary-level list operations behind the Mu–Welker bargraph/Dyck-path correspondence are literal inverses.",
        H("Mu–Welker valley/profile inverse core"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("mu-welker-bijection-expand-contract"),
                DeclarationHandle.Create(Prefix + "expand_contract"),
                H("Expansion and contraction are inverse on words"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Expand replaces each profile horizontal edge by the valley DU, while contract replaces each DU factor by one horizontal edge. The two operations are inverse on every Dyck-step list."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("mu-welker-bijection-contract-expand"),
                DeclarationHandle.Create(Prefix + "contract_expand"),
                H("Contraction followed by expansion recovers a profile"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If a profile has no adjacent D,U steps, contracting the expanded profile recovers the original profile exactly."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("mu-welker-bijection-valley-count-expand"),
                DeclarationHandle.Create(Prefix + "valleyCount_expand"),
                H("Expansion counts profile horizontal edges as valleys"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Under the profile no-adjacent-DU condition, the number of valleys after expansion equals the number of horizontal profile edges."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("mu-welker-bijection-source-valleys"),
                DeclarationHandle.Create(Prefix + "sourceValleys_eq_valleyCount"),
                H("The source valley count agrees with the kernel count"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The project’s zipped adjacent-pair definition of valleys agrees with the kernel count obtained by contracting DU factors."))),
                DescribeRole.Theorem))),
        []));
}
