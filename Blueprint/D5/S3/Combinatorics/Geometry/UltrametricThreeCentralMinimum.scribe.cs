using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry;

internal sealed class UltrametricThreeCentralMinimumDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Geometry/UltrametricThreeCentralMinimum.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Topology/mazhang2026centraledges");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A three-central ultrametric on n ≥ 4 points has at least 2n−4+⌈n/2⌉ central edges, "
            + "with an explicit equality criterion and an attaining space.",
        H("The sharp three-central ultrametric minimum"),
        Blocks(
            Describe.Lean(DescribeId.Create("ultrametric-three-central-minimum-tree"),
                DeclarationHandle.Create(Prefix + "Tree"),
                H("The attaining ultrametric"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Tree n is the point set {0,…,n−1} split into a part A={0,1} and a part B. "
                    + "B consists of the pairs {2k,2k+1} and, for odd n, the triple "
                    + "{n−3,n−2,n−1} with n−3 designated. Points in different parts are at "
                    + "distance 2, in different components of the same part at 3/2, at "
                    + "different positions of one component at 1, and the two undesignated "
                    + "points of the triple at 1/2. Distances depend only on the first level "
                    + "where two points differ and decrease along the levels, so the metric is "
                    + "an ultrametric. Its center is {0,1,2}: the row of 0 contains only these "
                    + "values, and every point has a neighbour at 1 and one at 2."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("ultrametric-three-central-minimum-result"),
                DeclarationHandle.Create(Prefix + "ultra_three_central_minimum"),
                H("The minimum and its equality criterion"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For n ≥ 4 every three-central ultrametric on n points has at least "
                    + "2n−4+⌈n/2⌉ central edges. Its center is {0,a,D} with D the maximum "
                    + "distance, which is central and equal to the diameter. The points at "
                    + "distance below D from a fixed point form a class S; by the ultrametric "
                    + "inequality every point of S is at distance D from every point outside "
                    + "S, and S and its complement each contain a point with its a-neighbour, "
                    + "so there are at least |S|(n−|S|) ≥ 2(n−2) edges of length D, while the "
                    + "length a has at least ⌈n/2⌉ edges. Equality holds exactly when the "
                    + "diametrical graph is complete bipartite with a part of two points and "
                    + "the non-diametrical central edges number ⌈n/2⌉, and Tree n attains it. "
                    + "This is Theorem 4 of H. Ma and W. Zhang; the centrality of D agrees with "
                    + "Theorem 2.15 of O. Dovgoshey and O. Rovenska."))),
                DescribeRole.Theorem))));
}
