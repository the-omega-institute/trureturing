using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.AdmissibleWords;

internal sealed class PathStableSetPolytopeDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S1/Words/AdmissibleWords/PathStableSetPolytope.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The occupancy means of binary words with no adjacent ones form the polytope "
            + "defined by coordinate bounds and adjacent-sum inequalities. In three "
            + "coordinates this is a square-based pyramid.",
        H("Occupancy means on a finite path"),
        Blocks(
            Result("hull", "convexHull_vertices", "The path stable set polytope",
                "For every natural number n, a vector is a convex mixture of admissible "
                    + "binary words exactly when each coordinate lies in [0,1] and each "
                    + "adjacent pair sums to at most one. The empty path is included. "
                    + "For a single vertex, the coordinate upper bound is essential.",
                Eqn(Call("conv", Sub(F.Id("W"), F.Id("n"))), Sub(F.Id("P"), F.Id("n"))),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Words/chvatal1975polytopes"))),
            Result("pyramid", "convexHull_three_pyramid", "The three-coordinate pyramid",
                "For three coordinates, nonnegativity and the two adjacent-sum inequalities "
                    + "already imply the coordinate upper bounds. Every point is a mixture "
                    + "of (u,0,v), with u and v in [0,1], and the apex (0,1,0). "
                    + "The mixing coefficient t is the middle occupancy x1. Thus the base "
                    + "is the unit square in the plane x1=0 and the apex has x1=1.",
                Eqn(F.Id("x"), Seq(Seq(Open, Num(1), Minus, F.Id("t"), Close), Sp,
                    Tuple(F.Id("u"), Num(0), F.Id("v")), Sp, Plus, Sp, F.Id("t"), Sp,
                    Tuple(Num(0), Num(1), Num(0)))),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Words/standard2026pathpyramid"))),
            Paragraph(Text(
                "The induction keeps the entire tail mixture. On each tail word it prepends "
                    + "either zero or the complement of the first tail bit. At the level of "
                    + "means these are the affine maps y mapped to (0,y) and (1-y0,y). "
                    + "If x1 is below one, set t=x0/(1-x1); their mixture with coefficient t "
                    + "has the prescribed mean x. If x1 is one, x0 is zero and the first "
                    + "map suffices. A tail component of weight p therefore gives two "
                    + "components of weights (1-t)p and tp, preserving all tail correlations.")))));

    private static DocumentBlock Result(string id, string declaration, string title,
        string prose, Formula formula, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create("path-stable-set-" + id),
            DeclarationHandle.Create(Module + declaration), H(title),
            StatementSource.FromAuthor(formula),
            provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static Formula Sub(Formula a, Formula b) => Seq(a, Underscore, Grp(b));
    private static Formula Eqn(Formula a, Formula b) => Disp(Seq(a, Sp, Eq, Sp, b));
    private static Formula Tuple(Formula a, Formula b, Formula c) =>
        Seq(Open, a, Comma, b, Comma, c, Close);
}
