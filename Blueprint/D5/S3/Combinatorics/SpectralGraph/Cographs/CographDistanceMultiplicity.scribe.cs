using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph.Cographs;

internal sealed class CographDistanceMultiplicityDocument : IScribeDocumentDefinition
{
    private const string Owner =
        "D5/S3/Combinatorics/SpectralGraph/Cographs/CographDistanceMultiplicity.result";
    private static readonly LibraryNoteRef Survey =
        LibraryNoteRef.Create("D5/L/QuadraticForms/mannamandaltura2026cographdistance");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The connected cographs attaining the eligible distance multiplicity bound and an explicit infinite family.",
        H("Equality in the cograph distance multiplicity bound"),
        Blocks(Describe.Lean(
            DescribeId.Create("cograph-distance-multiplicity-result"),
            DeclarationHandle.Create(Owner),
            H("Characterization and explicit infinite family"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(Survey),
            Blocks(
                Paragraph(Text("Open Problem 14.2(ii) asks which connected cographs attain the "
                    + "ordinary distance multiplicity bound at a real shift other than −1 and −2, "
                    + "and asks for an explicit infinite family. The width is the least number "
                    + "of chains for the vicinal preorder.")),
                Paragraph(Text("Every width-one connected cograph attains. At greater width the "
                    + "normalized join root must have exactly one nonleaf child and at least one "
                    + "leaf child. Attainment holds exactly when an eligible real guard root gives "
                    + "a nullity deficit of one in the nonleaf child and its scalar response g "
                    + "satisfies 1 + g − ℓ/(x+1) = 0, where ℓ counts the leaf children. "
                    + "The guard polynomials give a mathematically exact finite candidate set, "
                    + "with the scalar recursion valid also at poles and coincident roots. "
                    + "Executable root isolation lies outside this statement.")),
                Paragraph(Text("For every integer s ≥ 2, join a clique of size 3(s−1) to the "
                    + "disjoint union of the complete bipartite graph with parts of size s and "
                    + "s isolated vertices. Its order is 6s−3, its width is two, and its ordinary "
                    + "distance multiplicity is two at the eligible shift s−2. Strictly increasing "
                    + "orders give pairwise nonisomorphic connected cographs."))),
            DescribeRole.Theorem))));
}
