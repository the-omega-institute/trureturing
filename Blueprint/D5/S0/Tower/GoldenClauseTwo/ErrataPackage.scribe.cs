using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Tower.GoldenClauseTwo;

internal sealed class ErrataPackageDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        var championValue = Equal(
            Id("goldenChampionLiminf"),
            Id("goldenThreshold"));

        return DocumentDefinition.Create(ScribeNode.Create(
            "The golden tower clause carries its sixteen proved sentences together with "
                + "explicit refutations of the three that are false as stated.",
            H("Golden Tower Clause Two Erratum Package"),
            Blocks(
                Paragraph(Text(
                    "Sixteen source sentences are discharged by their frozen theorems. Three "
                        + "further source sentences are false: the unrestricted supremum claim, "
                        + "its corollary for arbitrary x, and the assertion that the closed "
                        + "permanent set is the four point ring. Those three appear in the "
                        + "package as explicit refutations rather than silent replacements, and "
                        + "the strict-side emptiness that stands in place of the third is "
                        + "conjoined beside them.")),
                Describe.Lean(
                    DescribeId.Create("golden-clause-two-carries-its-own-errata"),
                    DeclarationHandle.Create(
                        "D5/S0/Tower/GoldenClauseTwo/ErrataPackage."
                            + "golden_clause_two_errata_package"),
                    H("The golden clause with its errata"),
                    StatementSource.FromAuthor(FormulaDsl.Disp(championValue)),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "The displayed identity is the champion value the ring attains. The "
                            + "package itself is the conjunction of that identity with the "
                            + "remaining fifteen proved sentences and the three refutations."))),
                    DescribeRole.Theorem)),
            [
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S0/Tower/Champions/GoldenPermanentSurvivors")),
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S0/Tower/ErgodicBridge/Golden")),
                DocumentEdge.Dependency.Create(
                    GidRef.Create("D5/S0/Tower/GoldenPeriodicTwelve/EnumerationTwelve")),
            ]));
    }
}
