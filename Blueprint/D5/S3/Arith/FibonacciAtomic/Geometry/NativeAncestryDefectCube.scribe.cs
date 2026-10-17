using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Geometry;

internal sealed class NativeAncestryDefectCubeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Geometry/NativeAncestryDefectCube.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Independent bracket choices in a native Fibonacci source preserve the leaf word and have an exact affine ancestor-area formula.",
        H("Native Ancestor Area Choices"), Blocks(
            Paragraph(Text("Sources are nonempty ordered binary trees with beta and alpha leaves. "
                + "The canonical source T at generation n is the n-fold Fibonacci substitution of alpha. "
                + "The left-associated source B and the right-associated source D both have leaf word beta, alpha, beta.")),
            Def("defectB", "The canonical three-leaf source", "B is pair(pair(beta,alpha),beta)."),
            Def("defectD", "The bracket defect", "D is pair(beta,pair(alpha,beta))."),
            Def("positions", "All literal three-leaf positions",
                "positions(t) consists of every actual address whose subtree in t is B."),
            Def("fill", "Simultaneous native choices",
                "fill(t,a) replaces B by D precisely at the original positions where the Boolean choice a is true."),
            Def("variant", "The finite-subset family",
                "variant(t,A) uses the membership indicator of A as the simultaneous choice."),
            Describe.Lean(DescribeId.Create("native-fill-at"),
                DeclarationHandle.Create(Prefix + "fill_at"), H("The subtree at an original position"),
                StatementSource.FromAuthor(Disp(All("t", Op("Source"),
                    All("a", Seq(Op("Address"), Sp, To, Sp, Op("Bool")),
                    All("p", Op("Address"), Imp(Call("Member", V("p"), Call("positions", V("t"))),
                        EqOf(Call("subtree", V("p"), Call("fill", V("t"), V("a"))),
                            Call("some", Call("ite", Call("a", V("p")), Op("defectD"), Op("defectB")))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every original B position remains present after simultaneous filling. "
                    + "Its subtree is exactly D for a true choice and B for a false choice."))),
                DescribeRole.Theorem),
            Def("areaVector", "Euclidean ancestor-area vector",
                "areaVector(m,t) lists the products of the left and right child leaf counts in inorder gap order, "
                + "in Euclidean space with m minus one coordinates. Unoccupied coordinates are zero."),
            Def("gapVector", "One unit of transferred area",
                "gapVector(m,j) is the standard unit vector at j minus the standard unit vector at j plus one."),
            Def("sourceFamily", "The actual source family",
                "sourceFamily(t) is the image of the full powerset of positions(t) under variant(t)."),
            Def("areaVertices", "The complete Euclidean vertex set",
                "areaVertices(t) is the image of the same powerset under the ancestor-area vector."),
            Def("normalizedAreaFamily", "The normalized Euclidean family",
                "The area vertices of T(n) are scaled by the reciprocal of choose(fib(n plus one),two)."),
            Def("unitDirection", "Normalized independent directions",
                "Each signed gap vector is divided by square root two."),
            Def("directionSpan", "The direction space",
                "The real span of the normalized gap vectors is the Euclidean direction space of the cube."),
            Def("intrinsicCube", "The cube in its own direction space",
                "This is the inverse image of the convex hull under x maps to areaVector(t) plus x, "
                + "with x in directionSpan(t). Its volume is the canonical Euclidean volume on that subspace."),
            Describe.Lean(DescribeId.Create("native-area-cube"),
                DeclarationHandle.Create(Prefix + "native_area_cube"), H("The native family, area formula and squared distances"),
                StatementSource.FromAuthor(NativeFormula()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For n at least three, all B positions are counted by fib(n minus two). "
                        + "Distinct subsets give distinct actual trees. Every choice preserves the leaf word "
                        + "and the fib(n plus one) leaf count. The empty subset has intrinsic substitution "
                        + "depth n, and every nonempty subset has depth zero.")),
                    Paragraph(Text("Coordinates record the product of the two child leaf counts at each internal gap. "
                        + "Replacing B changes its two internal coordinates from [1,2] to [2,1]. "
                        + "An arbitrary context with equal-length fillings has the same exterior coordinate lists. "
                        + "Adding positions one at a time gives the stated sum of signed gap vectors. "
                        + "Distinct positions occupy disjoint gap pairs. Squared Euclidean distance is twice "
                        + "the cardinality of the symmetric difference of the choices, and total area is preserved.")),
                    Paragraph(Text("The convex hull is the translate of the parallelepiped of the independent "
                        + "signed gap vectors: its coefficients range independently from zero to one. "
                        + "After division by square root two these vectors are orthonormal. "
                        + "Their direction span has dimension fib(n minus two), every edge has length square root two, "
                        + "and the canonical volume in that direction space is two to the power fib(n minus two) divided by two."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("normalized-cube-diameter"),
                DeclarationHandle.Create(Prefix + "normalized_cube_diameter"),
                H("Exact normalized diameter and decay"),
                StatementSource.FromAuthor(DiameterFormula()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The empty and full subsets attain the maximal Euclidean separation. "
                        + "Scaling by the reciprocal total area gives the exact normalized diameter. "
                        + "There remain two to the power fib(n minus two) distinct sources, "
                        + "with depth n at the empty choice and zero at the full choice.")),
                    Paragraph(Text("Writing M for fib(n plus one) and K for fib(n minus two), "
                        + "the inequalities K at most M and choose(M,two) at least M squared divided by four "
                        + "bound the diameter by four times square root two times M to the power minus three halves. "
                        + "Since the Fibonacci leaf count diverges, the diameter tends to zero."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Def(string name, string title, string prose) => Describe.Lean(
        DescribeId.Create("native-area-" + name.ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
    private static Formula V(string name) => F.Id(name);
    private static Formula Op(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Op(name), [.. args]);
    private static Formula Nat() => Seq(Mathbb, Grp(V("N")));
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, Par(body));
    private static Formula EqOf(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula And(Formula a, Formula b) => Seq(Par(a), Sp, Land, Sp, Par(b));
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));

    private static Formula NativeFormula()
    {
        Formula n = V("n"), a = V("A"), p = V("p"), b = V("B"), i = V("i");
        Formula t = Call("T", n), positions = Call("positions", t);
        Formula m = Call("fib", Seq(n, Plus, D(1)));
        Formula value = Call("variant", t, a);
        Formula word = EqOf(Call("wd", value), Call("wd", t));
        Formula length = EqOf(Call("length", value), m);
        Formula depth = EqOf(Call("depth", value),
            Call("ite", EqOf(a, Emptyset), n, D(0)));
        Formula transfer = Seq(new Formula.Subscript(Sum, Seq(p, Sp, InMacro, Sp, a)), Sp,
            Call("gapVector", m, Call("offset", t, p)));
        Formula affine = EqOf(Call("areaVector", m, value),
            Seq(Call("areaVector", m, t), Plus, transfer));
        Formula total = EqOf(Seq(new Formula.Subscript(Sum,
            Seq(i, Colon, Call("Fin", Seq(m, Minus, D(1))))), Sp, Call("areaVector", m, value, i)),
            Call("choose", m, D(2)));
        Formula coordinateLength = EqOf(Call("length", Call("coordinates", value)), Seq(m, Minus, D(1)));
        Formula distance = All("B", Call("Finset", Op("Address")),
            Imp(Call("Subset", b, positions), EqOf(new Formula.Power(
                Call("norm", Seq(Call("areaVector", m, value), Minus,
                    Call("areaVector", m, Call("variant", t, b)))), D(2)),
                Seq(D(2), Times, Call("card", Call("symmDiff", a, b))))));
        Formula choices = All("A", Call("Finset", Op("Address")),
            Imp(Call("Subset", a, positions), And(word, And(length,
                And(depth, And(affine, And(total, And(coordinateLength, distance))))))));
        Formula injective = Call("InjectiveOn", Call("variant", t), Call("powerset", positions));
        Formula count = EqOf(Call("card", positions), Call("fib", Seq(n, Minus, D(2))));
        Formula q = V("q"), offset = Call("offset", t, p), offsetQ = Call("offset", t, q);
        Formula literal = All("p", Op("Address"), Call("Iff", Call("mem", p, positions),
            EqOf(Call("subtree", p, t), Call("some", Op("defectB")))));
        Formula valid = All("p", Op("Address"), Imp(Call("mem", p, positions),
            And(Seq(offset, Sp, Lt, Sp, Seq(m, Minus, D(1))),
                Seq(offset, Plus, D(1), Sp, Lt, Sp, Seq(m, Minus, D(1))))));
        Formula separated = All("p", Op("Address"), Imp(Call("mem", p, positions),
            All("q", Op("Address"), Imp(Call("mem", q, positions),
                Imp(Seq(p, Sp, Neq, Sp, q), Seq(Par(Seq(offset, Plus, D(3), Sp, Le, Sp, offsetQ)),
                    Sp, Lor, Sp, Par(Seq(offsetQ, Plus, D(3), Sp, Le, Sp, offset))))))));
        Formula directions = Seq(p, Colon, positions, Sp, Mapsto, Sp,
            Call("gapVector", m, Call("offset", t, p)));
        Formula hull = EqOf(Call("convexHull", Seq(Mathbb, Grp(V("R"))), Call("areaVertices", t)),
            Seq(Call("singleton", Call("areaVector", m, t)), Plus, Call("parallelepiped", directions)));
        Formula orthonormal = Call("Orthonormal", Seq(Mathbb, Grp(V("R"))), Call("unitDirection", t));
        Formula affineDirection = EqOf(Call("direction", Call("affineSpan", Seq(Mathbb, Grp(V("R"))),
            Call("convexHull", Seq(Mathbb, Grp(V("R"))), Call("areaVertices", t)))), Call("directionSpan", t));
        Formula span = EqOf(Call("directionSpan", t),
            Call("span", Seq(Mathbb, Grp(V("R"))), Call("range", directions)));
        Formula dimension = EqOf(Call("finrank", Seq(Mathbb, Grp(V("R"))), Call("directionSpan", t)),
            Call("fib", Seq(n, Minus, D(2))));
        Formula edges = All("p", positions, EqOf(Call("norm", Call("gapVector", m, Call("offset", t, p))),
            Call("sqrt", D(2))));
        Formula volume = EqOf(Call("volume", Call("intrinsicCube", t)), Call("ofReal",
            new Formula.Power(D(2), new Formula.Fraction(Call("fib", Seq(n, Minus, D(2))), D(2)))));
        Formula geometry = And(literal, And(valid, And(separated, And(hull, And(affineDirection,
            And(orthonormal, And(span, And(dimension, And(edges, volume)))))))));
        return Disp(All("n", Nat(), Imp(Seq(D(3), Sp, Le, Sp, n),
            And(count, And(injective, And(choices, geometry))))));
    }

    private static Formula DiameterFormula()
    {
        Formula n = V("n"), m = Call("fib", Seq(n, Plus, D(1)));
        Formula k = Call("fib", Seq(n, Minus, D(2)));
        Formula family = Call("normalizedAreaFamily", n);
        Formula diameter = Call("diam", family);
        Formula rate = new Formula.Power(m, Seq(Minus, new Formula.Fraction(D(3), D(2))));
        Formula exact = EqOf(diameter, new Formula.Fraction(Call("sqrt", Seq(D(2), Times, k)), Call("choose", m, D(2))));
        Formula count = EqOf(Call("card", Call("sourceFamily", Call("T", n))),
            new Formula.Power(D(2), k));
        Formula endpoints = And(EqOf(Call("depth", Call("variant", Call("T", n), Emptyset)), n),
            EqOf(Call("depth", Call("variant", Call("T", n), Call("positions", Call("T", n)))), D(0)));
        Formula scale = new Formula.Power(Call("choose", m, D(2)), Seq(Minus, D(1)));
        Formula emptyVector = Seq(scale, Times, Call("areaVector", m, Call("variant", Call("T", n), Emptyset)));
        Formula fullVector = Seq(scale, Times, Call("areaVector", m,
            Call("variant", Call("T", n), Call("positions", Call("T", n)))));
        Formula extremal = EqOf(Call("norm", Seq(emptyVector, Minus, fullVector)), diameter);
        Formula sequence = Seq(n, Sp, Mapsto, Sp, diameter);
        Formula decay = Seq(n, Sp, Mapsto, Sp, rate);
        return Disp(And(All("n", Nat(), Imp(Seq(D(3), Sp, Le, Sp, n), And(exact, And(count, And(endpoints, extremal))))),
            And(Call("IsBigO", Op("atTop"), sequence, decay),
                Call("Tendsto", sequence, Op("atTop"), Call("nhds", D(0))))));
    }
}
