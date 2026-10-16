using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Geometry;

internal sealed class NativeAncestryDefectCubeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Geometry/NativeAncestryDefectCube.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A three-leaf bracket defect has a common coordinate exterior in every native context.",
        H("Contextual Ancestor Coordinate Defect"), Blocks(
            Paragraph(Text("Source is the existing FreeMagma Bool algebra of nonempty ordered binary trees. "
                + "The false leaf is beta and the true leaf is alpha. Coordinates list the products of "
                + "the two child leaf counts at the inorder gaps.")),
            Def("defectB", "Left-associated three-leaf source",
                "defectB is pair(pair(beta,alpha),beta), the three-leaf source on the substitution ray."),
            Def("defectD", "Right-associated three-leaf source",
                "defectD is pair(beta,pair(alpha,beta)); it has the same leaf word and leaf count as defectB."),
            Def("listSquaredDistance", "Coordinate-list squared distance",
                "For two natural lists of equal length, listSquaredDistance sums the squared integer "
                + "differences at corresponding positions."),
            Def("normalizedListDistance", "Normalized coordinate-list distance",
                "normalizedListDistance divides the square-root distance by the binomial total pair count."),
            Describe.Lean(DescribeId.Create("native-area-cube"),
                DeclarationHandle.Create(Prefix + "native_area_cube"),
                H("The contextual two-coordinate displacement"),
                StatementSource.FromAuthor(NativeFormula()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Every output context has two natural lists L and R such that plugging "
                        + "defectB gives L followed by [1,2] followed by R, while plugging defectD gives "
                        + "the same exterior with [2,1]. The prefix length is the leaf offset of the context "
                        + "hole. The two changed coordinates therefore have squared distance two.")),
                    Paragraph(Text("The proof is structural induction on the context. A left sibling appends "
                        + "its root product and its coordinates to R; a right sibling prepends its coordinates "
                        + "and root product to L. Equal plugged lengths synchronize the root products."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("normalized-cube-diameter"),
                DeclarationHandle.Create(Prefix + "normalized_cube_diameter"),
                H("The normalized contextual edge"),
                StatementSource.FromAuthor(NormalizedFormula()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The same two coordinate lists have normalized distance equal to the "
                    + "square root of two divided by the total number of leaf pairs. The statement is for "
                    + "one actual context edge and does not identify a multi-position source family."))),
                DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);
    private static Formula Nats() => Seq(Mathbb, Grp(V("N")));
    private static Formula Ints() => Seq(Mathbb, Grp(V("Z")));
    private static Formula Reals() => Seq(Mathbb, Grp(V("R")));
    private static Formula Op(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Op(name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, Par(body));
    private static Formula Exists(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, V(name), Colon, Sp, type, Comma, Sp, Par(body));
    private static Formula Par(Formula value) => Seq(Open, value, Close);
    private static Formula EqOf(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula And(Formula a, Formula b) => Seq(Par(a), Sp, Land, Sp, Par(b));
    private static Formula ListOf(params Formula[] values)
    {
        var items = new List<Formula> { OpenBracket };
        for (var i = 0; i < values.Length; i++)
        {
            if (i > 0) items.AddRange([Comma, Sp]);
            items.Add(values[i]);
        }
        items.Add(CloseBracket);
        return Seq([.. items]);
    }
    private static Formula Append(Formula a, Formula b) => Call("append", a, b);
    private static Formula Plug(Formula c, Formula x) => Call("plug", c, x);
    private static Formula Coordinates(Formula x) => Call("coordinates", x);
    private static Formula ListType() => Call("List", Nats());
    private static Formula Pair12() => ListOf(D(1), D(2));
    private static Formula Pair21() => ListOf(D(2), D(1));
    private static Formula Exterior(Formula l, Formula pair, Formula r) =>
        Append(l, Append(pair, r));

    private static Formula NativeFormula()
    {
        Formula c = V("C"), l = V("L"), r = V("R");
        Formula b = Op("defectB"), d = Op("defectD");
        Formula bx = Coordinates(Plug(c, b));
        Formula dx = Coordinates(Plug(c, d));
        Formula common = And(EqOf(bx, Exterior(l, Pair12(), r)),
            And(EqOf(dx, Exterior(l, Pair21(), r)),
                And(EqOf(Call("length", l), Call("offset", Plug(c, b), Call("holeAddress", c))),
                    EqOf(Call("listSquaredDistance", Exterior(l, Pair12(), r),
                        Exterior(l, Pair21(), r)), D(2)))));
        return Disp(All("C", Op("OutputContext"), Exists("L", ListType(),
            Exists("R", ListType(), common))));
    }

    private static Formula NormalizedFormula()
    {
        Formula c = V("C"), l = V("L"), r = V("R");
        Formula b = Op("defectB"), d = Op("defectD");
        Formula bx = Coordinates(Plug(c, b));
        Formula dx = Coordinates(Plug(c, d));
        Formula mb = Call("length", Plug(c, b));
        Formula exteriorB = Exterior(l, Pair12(), r);
        Formula exteriorD = Exterior(l, Pair21(), r);
        Formula norm = EqOf(Call("normalizedListDistance", mb, exteriorB, exteriorD),
            Seq(Sqrt, Grp(D(2)), Div, Call("choose", mb, D(2))));
        return Disp(All("C", Op("OutputContext"), Exists("L", ListType(),
            Exists("R", ListType(), And(
                And(EqOf(bx, exteriorB), EqOf(dx, exteriorD)), norm))));
    }
}
