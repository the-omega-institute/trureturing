using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Geometry;

internal sealed class UltrametricCenterSphereEightDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Geometry/UltrametricCenterSphereEight.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every two prescribed distances strictly between zero and one, an eight-point ultrametric has the exact distance center and sphere counts required for sharpness.",
        H("An eight-point model with two prescribed gap distances"),
        Blocks(
            Paragraph(Text("Throughout, u and v are arbitrary real numbers satisfying "),
                Math(In(Seq(D(0), Sp, Lt, Sp, F.Id("u"), Sp, Lt, Sp, F.Id("v"), Sp, Lt, Sp, D(1)))),
                Text(". Write E for Eight u v hu huv hv, with the metric and ultrametric instances inherited from the constant cross-distance join. Every statement below holds for every such pair, and every point p is arbitrary in E.")),
            Describe.Remark(DescribeId.Create("eight-construction"), DeclarationHandle.Create(Prefix + "Eight"),
                H("The nested join construction"), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A Pair joins two singleton spaces at its weight. A Block joins two such pairs at distance one. Eight joins two blocks at distance two; the first block uses weight u and the second uses weight v. Thus the two prescribed gap distances are kept separate between the blocks.")),
                    Paragraph(Text("The component order calculations are "), Ref(Prefix + "pair_card"), Text(" and "),
                        Ref(Prefix + "block_card"), Text(". Their strict bounds are "), Ref(Prefix + "pair_dist_lt_one"),
                        Text(" and "), Ref(Prefix + "block_dist_lt_two"), Text(".")))),
            Node("eight-points", "The carrier has eight points", "eight_card",
                Disp(Seq(Call("card", F.Id("E")), Sp, Eq, Sp, D(8))),
                "The order follows by summing two four-point blocks, each consisting of two two-point pairs."),
            Node("zero-sphere", "Every zero sphere has one point", "sphere_zero_card", Count(0, 1),
                "The zero sphere is the singleton consisting of its center, by identity of indiscernibles."),
            Node("one-sphere", "Every sphere at one has two points", "sphere_one_card", Count(1, 2),
                "At distance one, p sees exactly the other pair in its own block. Its own pair lies strictly below one; the other block lies at distance two."),
            Node("two-sphere", "Every sphere at two has four points", "sphere_two_card", Count(2, 4),
                "At distance two, p sees exactly the four points of the other block. All distances within its own block are strictly below two."),
            Node("exact-center", "The original distance center is exactly zero, one and two", "eight_center",
                Disp(Seq(Call("center", F.Id("E")), Sp, Eq, Sp, Set(D(0), D(1), D(2)))),
                "The center is the project's distance-center predicate, with nonnegative radii and a witness at every point. The three prescribed radii are central by their pointwise sphere counts. A gap distance from one block is absent at every point in the other block; distinctness of u and v excludes an additional central radius."),
            Node("distance-support", "The construction introduces no other distances", "distance_values",
                Disp(Seq(Call("dist", F.Id("p"), F.Id("q")), Sp, InMacro, Sp,
                    Set(D(0), F.Id("u"), F.Id("v"), D(1), D(2)))),
                "For every p and q in E, the distance lies in the displayed set. In particular no distance strictly between one and two is introduced. Exact occurrence of both prescribed gap values is established in the sharpness module by eight_exact_distance_values."))));

    private static DocumentBlock Node(string id, string title, string name, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static Formula Count(byte radius, byte count) => Disp(Seq(
        Call("card", Call("sphere", F.Id("p"), D(radius))), Sp, Eq, Sp, D(count)));
    private static Formula Set(Formula a, Formula b, Formula c) =>
        Seq(OpenBrace, a, Comma, b, Comma, c, CloseBrace);
    private static Formula Set(Formula a, Formula b, Formula c, Formula d, Formula e) =>
        Seq(OpenBrace, a, Comma, b, Comma, c, Comma, d, Comma, e, CloseBrace);
}
