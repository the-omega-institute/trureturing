using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.ZeroDivisor;

internal sealed class MekeraRankIntegrationDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/mekerasomeryesil2026annihilatordigraphs");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Block ranks characterize ordered arcs in full matrix rings over fields.",
        H("Rank tests for ordered annihilator-digraph arcs"),
        Blocks(
            Describe.Lean(DescribeId.Create("ordered-arc-rank"),
                DeclarationHandle.Create(
                    "D5/S3/Combinatorics/Graph/ZeroDivisor/MekeraRankIntegration.arc_iff_rank"),
                H("The ordered arc rank criterion"), StatementSource.FromLean(),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Mekera, Somer and Yeşil ask in the second paragraph of Section 7 "
                        + "how the arcs of the annihilator digraph of the full matrix ring can be "
                        + "characterized in terms of matrix ranks. Let F be any field, n at least "
                        + "two, and A and B distinct nonzero singular n-by-n matrices over F. "
                        + "Nonzero singular matrices are exactly the vertices of the digraph.")),
                    Paragraph(Text(
                        "Write C = AB. The left witness exists exactly when the rank of C is "
                        + "strictly below both the rank of A and the rank of the horizontal block "
                        + "formed by adjoining the columns of B to C. The right witness exists "
                        + "exactly when the rank of C is strictly below both the rank of B and "
                        + "the rank of the vertical block formed by stacking the rows of A below C. "
                        + "Either witness suffices for the arc from A to B. The reverse arc uses BA "
                        + "with the endpoint roles exchanged.")),
                    Paragraph(Text(
                        "The right witness requires a vector in the kernel of C outside both "
                        + "endpoint kernels. Two proper subspaces cannot cover the kernel of C, "
                        + "even over the binary field. Rank–nullity converts the resulting strict "
                        + "kernel inclusions into the two right-witness inequalities. Transposing "
                        + "and exchanging the endpoints gives the left-witness inequalities."))),
                DescribeRole.Theorem))));
}
