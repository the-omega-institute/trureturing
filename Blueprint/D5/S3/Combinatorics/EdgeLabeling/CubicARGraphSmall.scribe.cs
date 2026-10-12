using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.EdgeLabeling;

internal sealed class CubicARGraphSmallDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Degree and cardinality determine the small cubic graph forms.",
        H("The small cubic graphs"),
        Blocks(
            Describe.Lean(DescribeId.Create("degree-two-six-presentation"),
                DeclarationHandle.Create("D5/S3/Combinatorics/EdgeLabeling/CubicARGraphSmall.two_regular_six_presentation"),
                H("Six vertices of degree two"),
                StatementSource.FromAuthor(Disp(Seq(
                    Call("card", F.Id("V")), Sp, Eq, Sp, D(6), Sp, Land, Sp,
                    Forall, Sp, F.Id("v"), Comma, Sp,
                    Call("degree", F.Id("H"), F.Id("v")), Sp, Eq, Sp, D(2), Sp, Implies, Sp,
                    Call("TwoTrianglesOrSixCycle", F.Id("H"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every simple graph on six vertices in which every vertex has degree two "
                    + "has a listing of six distinct vertices covering the vertex set. Its "
                    + "neighbor sets in that listing are either those of two disjoint triangles "
                    + "or those of a six-cycle. A triangle exhausts the two neighbors of each "
                    + "of its vertices, and forces the remaining three vertices to form a triangle. "
                    + "Without a triangle, two extensions from the neighbors of one vertex "
                    + "must be distinct. Closing them early would leave at most two vertices "
                    + "of degree two, which is impossible. They therefore close through the "
                    + "unique remaining vertex to give a six-cycle."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("six-vertex-equivalence"),
                DeclarationHandle.Create("D5/S3/Combinatorics/EdgeLabeling/CubicARGraphSmall.six_listing_equiv"),
                H("A listing as an equivalence"),
                StatementSource.FromAuthor(Disp(Seq(
                    Call("PairwiseDistinct", F.Id("a"), F.Id("b"), F.Id("c"), F.Id("d"), F.Id("e"), F.Id("f")),
                    Sp, Land, Sp, F.Id("V"), Sp, Eq, Sp,
                    Call("ListingSet", F.Id("a"), F.Id("b"), F.Id("c"), F.Id("d"), F.Id("e"), F.Id("f")),
                    Sp, Implies, Sp, Exists, Sp, F.Id("q"), Colon, Sp,
                    Call("Equiv", Call("Fin", D(6)), F.Id("V")), Comma, Sp,
                    Call("MatchesListing", F.Id("q"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Any pairwise distinct listing a,b,c,d,e,f covering a finite vertex type "
                    + "gives an equivalence q from Fin 6 to that type, with q(0)=a, q(1)=b, "
                    + "q(2)=c, q(3)=d, q(4)=e, and q(5)=f."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("four-vertex-completeness"),
                DeclarationHandle.Create("D5/S3/Combinatorics/EdgeLabeling/CubicARGraphSmall.cubic_four_complete"),
                H("Four-vertex cubic graphs"),
                StatementSource.FromAuthor(Disp(Seq(
                    Call("card", F.Id("V")), Sp, Eq, Sp, D(4), Sp, Land, Sp,
                    Forall, Sp, F.Id("v"), Comma, Sp,
                    Call("degree", F.Id("G"), F.Id("v")), Sp, Eq, Sp, D(3), Sp, Implies, Sp,
                    Forall, Sp, F.Id("x"), Comma, Sp, F.Id("y"), Comma, Sp,
                    Call("Adj", F.Id("G"), F.Id("x"), F.Id("y")), Sp, Iff, Sp,
                    F.Id("x"), Sp, Neq, Sp, F.Id("y")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a simple cubic graph with four vertices, adjacency is precisely "
                    + "inequality. Each neighbor set has three elements and is contained in "
                    + "the other three vertices, so equality follows by cardinality."))), DescribeRole.Theorem)),
        []));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
}
