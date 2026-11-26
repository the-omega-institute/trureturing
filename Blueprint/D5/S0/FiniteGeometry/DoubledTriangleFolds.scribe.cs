using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.FiniteGeometry;

internal sealed class DoubledTriangleFoldsDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S0/FiniteGeometry/DoubledTriangleFolds";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Minimum-fold colorings of doubled triangles",
        H("Minimum-fold colorings of doubled triangles"),
        Blocks(
            Model("axes", "Axis", "Barycentric axes",
                Seq(Named("Axis"), Eq, OpenBrace, X, Comma, Y, Comma, Z, CloseBrace),
                "The three constructors of Axis index the three coordinates."),
            Model("points", "Point", "Barycentric coordinate carrier",
                PointDefinition(),
                "The natural coordinate triple carries a proof of the additive constraint. The offset is zero for vertices, one for up cells and two for down cells."),
            Model("coordinate", "coord", "Coordinate lookup",
                CoordinateDefinition(),
                "Point.coord selects the coordinate indexed by the axis."),
            Model("cells", "Cell", "Cells of one sheet",
                All(N, Naturals, Equal(Cell, Call("Sum", Point(D(1)), Point(D(2))))),
                "The two summands distinguish up and down cells, including an empty down-cell carrier at side length one."),
            Model("faces", "Face", "Faces of the doubled subdivision",
                All(N, Naturals, Seq(Face, Eq, Bool, Times, Cell)),
                "The Boolean tag is false for the front and true for the back."),
            Model("colorings", "Coloring", "Face colorings",
                All(N, Naturals, Seq(Coloring, Eq, Face, To, Sp, Bool)),
                "True denotes black and false denotes white."),
            Model("up-face", "up", "Up face",
                All(N, Naturals, All(S, Bool, All(P, Point(D(1)),
                    Equal(Call("up", S, P), Pair(S, Call("inl", P)))))),
                "Use the left summand of Cell on the selected sheet."),
            Model("down-face", "down", "Down face",
                All(N, Naturals, All(S, Bool, All(P, Point(D(2)),
                    Equal(Call("down", S, P), Pair(S, Call("inr", P)))))),
                "Use the right summand of Cell on the selected sheet."),
            Model("boundary", "boundary", "Boundary vertices",
                All(N, Naturals, All(V, Point(D(0)), Seq(Call("boundary", V), Iff, Sp,
                    Call("x", V), Eq, D(0), Lor, Sp, Call("y", V), Eq, D(0), Lor, Sp, Call("z", V), Eq, D(0)))),
                "A boundary vertex has at least one zero coordinate. Its front and back representatives are identified."),
            Model("bump", "bump", "Single coordinate increment",
                All(A, Axis, All(B, Axis, Equal(Call("bump", A, B),
                    Conditional(Equal(A, B), D(1), D(0))))),
                "The increment is one on the selected axis and zero elsewhere."),
            Model("bump-pair", "bumpPair", "Two coordinate increments",
                All(A, Axis, All(B, Axis, Equal(Call("bumpPair", A, B),
                    Conditional(Equal(A, B), D(0), D(1))))),
                "Both coordinates other than the selected axis receive one."),
            Model("up-corner", "atUp", "Up corner incident to a vertex",
                AtCornerDefinition(false),
                "Subtract one in the selected coordinate when it is positive. The resulting point indexes the up face on the chosen sheet."),
            Model("down-corner", "atDown", "Down corner incident to a vertex",
                AtCornerDefinition(true),
                "Subtract one in each of the two other coordinates when both permit it. The resulting point indexes the down face on the chosen sheet."),
            Model("sheet-corners", "sheetCorners", "Incident corners on one sheet",
                SheetCornersDefinition(),
                "The six possible corners are enumerated in axis order, first up and then down. Absent options are discarded by filterMap."),
            Model("incident-corners", "incidentCorners", "Incident corners at a quotient vertex",
                IncidentCornersDefinition(),
                "Boundary vertices concatenate the two sheet lists. An interior vertex keeps the list on its own sheet."),
            Model("black-corners", "black", "Black corner count",
                All(N, Naturals, All(C, Coloring, All(L, ListOf(Face),
                    Equal(Call("black", C, L), Call("countP", C, L))))),
                "The natural count of true colors in the list is read as an integer."),
            Model("white-corners", "white", "White corner count",
                All(N, Naturals, All(C, Coloring, All(L, ListOf(Face),
                    Equal(Call("white", C, L), Call("countP",
                        Paren(Seq(Lambda, Sp, FaceVariable, Colon, Face, Comma, Sp, Neg, Sp, Apply(C, FaceVariable))), L))))),
                "The natural count of false colors in the list is read as an integer."),
            Model("good", "Good", "Good coloring",
                GoodDefinition(),
                "At every quotient vertex the black corner count minus the white corner count is divisible by three in the integers. On the boundary the choice of representative sheet gives the same list."),
            Model("edges", "Edge", "Edges of the doubled subdivision",
                EdgeDefinition(),
                "An up cell and omitted axis label an edge. A positive coordinate permits both sheet tags. A zero coordinate permits the canonical false sheet tag only."),
            Model("below", "below", "Down cell across an interior edge",
                BelowDefinition(),
                "The positive coordinate permits natural subtraction of one. It produces a triple of sum n minus two."),
            Model("edge-faces", "edgeFaces", "The two faces at an edge",
                EdgeFacesDefinition(),
                "For a seam the first face is front and the second back. Away from the seam the first face is up and the second down on the same sheet."),
            Model("fold", "Fold", "Fold predicate",
                All(N, Naturals, All(C, Coloring, All(E, Edges, Seq(Call("Fold", C, E), Iff, Sp,
                    Apply(C, Projection(Call("edgeFaces", E), 1)), Neq, Sp,
                    Apply(C, Projection(Call("edgeFaces", E), 2)))))),
                "The two incident face colors differ."),
            Model("folds", "folds", "Folded edges",
                All(N, Naturals, All(C, Coloring, Equal(Call("folds", C),
                    Seq(OpenBrace, E, Sp, InMacro, Sp, Edges, Sp, Mid, Sp, Call("Fold", C, E), CloseBrace)))),
                "The finite set of all edges is filtered by Fold."),
            Model("fold-count", "foldCount", "Total number of folds",
                All(N, Naturals, All(C, Coloring,
                    Equal(Call("foldCount", C), Call("card", Call("folds", C))))),
                "Each folded edge, including a seam edge, contributes exactly once."),
            Model("two-sided", "twoSided", "Opposite uniform sheets",
                All(N, Naturals, All(B, Bool, All(S, Bool, All(T, Cell,
                    Equal(Apply(Call("twoSided", B), Pair(S, T)),
                        Conditional(S, Seq(Neg, Sp, B), B)))))),
                "The front has color b and the back its Boolean complement."),
            Describe.Lean(
                DescribeId.Create("doubled-triangle-minimum-fold-uniqueness"),
                DeclarationHandle.Create(Module + ".minimum_fold_uniqueness"),
                H("Equality forces the two-sided coloring"),
                StatementSource.FromAuthor(Disp(UniquenessFormula())),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/FiniteGeometry/fernando2026goodcolorings")),
                Blocks(
                    Paragraph(Text(
                        "For every positive side length n, a coloring is good and has exactly 3n folds " +
                        "if and only if its front faces all have one color and its back faces all have " +
                        "the opposite color. Goodness requires the signed difference in incident " +
                        "black and white face corners to be divisible by three at every quotient vertex, including each sheet interior vertex. " +
                        "The identity symmetry suffices, with a global swap when the front is white.")),
                    Paragraph(Text(
                        "Up and down cells are indexed by barycentric triples of sum n minus one " +
                        "and n minus two, respectively. Each up cell and omitted corner specifies an " +
                        "edge on each sheet when the corresponding coordinate is positive. At zero " +
                        "there is one seam edge and the two incident up cells lie on opposite sheets. " +
                        "In particular, side length one has two faces and three distinct seam edges.")),
                    Paragraph(Text(
                        "A monochromatic ring would force every successive ring toward the corner to " +
                        "have that color. The vertex congruence first fixes both faces at the seam, " +
                        "then propagates across each sheet through triples of consecutive faces. The " +
                        "two corner faces have different colors. In a closed traversal of a " +
                        "nonmonochromatic ring, a rise and a fall in color occur at different edges. " +
                        "Every fold crosses two coordinate cuts, so there are at least 3n folds. " +
                        "At equality each cut has exactly two.")),
                    Paragraph(Text(
                        "At each side, the two corner folds leaving the side exhaust the nearest " +
                        "parallel cut. The up, down, up fans joining consecutive side faces on " +
                        "each sheet therefore use unfolded edges. Both sheets retain their first " +
                        "corner colors along the side, so every seam edge folds. The seam count " +
                        "exhausts the total of 3n and the remaining edges are unfolded. Moving one " +
                        "unit of barycentric mass toward a fixed corner connects all up cells " +
                        "through down cells within each sheet, and every down cell joins an up cell.")),
                    Paragraph(Text(
                        "Conversely, the opposite uniform sheets balance their incident corners at " +
                        "boundary vertices. Each interior vertex has six corners of one color. " +
                        "Exactly the seam edges fold, giving 3n folds."))),
                DescribeRole.Theorem))));

    private static DocumentBlock.Describe Model(string id, string declaration, string title,
        Formula formula, string commentary) =>
        Describe.Lean(DescribeId.Create("doubled-triangle-" + id),
            DeclarationHandle.Create(Module + "." + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(commentary))), DescribeRole.Definition);

    private static Formula N => F.Id("n");
    private static Formula Offset => F.Id("d");
    private static Formula A => F.Id("a");
    private static Formula B => F.Id("b");
    private static Formula C => F.Id("C");
    private static Formula E => F.Id("e");
    private static Formula L => F.Id("l");
    private static Formula P => F.Id("p");
    private static Formula S => F.Id("s");
    private static Formula T => F.Id("t");
    private static Formula V => F.Id("v");
    private static Formula X => F.Id("x");
    private static Formula Y => F.Id("y");
    private static Formula Z => F.Id("z");
    private static Formula FaceVariable => F.Id("f");
    private static Formula Naturals => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Axis => Named("Axis");
    private static Formula Bool => Named("Bool");
    private static Formula True => Named("true");
    private static Formula False => Named("false");
    private static Formula Cell => Call("Cell", N);
    private static Formula Face => Call("Face", N);
    private static Formula Coloring => Call("Coloring", N);
    private static Formula Edges => Call("Edge", N);
    private static Formula Point(Formula offset) => Call("Point", N, offset);
    private static Formula ListOf(Formula type) => Call("List", type);
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Apply(Formula name, params Formula[] args) => new Formula.Apply(name, [.. args]);
    private static Formula Call(string name, params Formula[] args) => Apply(Named(name), args);
    private static Formula Paren(Formula value) => Seq(Open, value, Close);
    private static Formula Pair(Formula first, Formula second) => Seq(Open, first, Comma, second, Close);
    private static Formula Triple(Formula first, Formula second, Formula third) =>
        Seq(Open, first, Comma, second, Comma, third, Close);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Eq, right);
    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, variable, Colon, Sp, type, Comma, Sp, body);
    private static Formula Some(Formula variable, Formula type, Formula body) =>
        Seq(Exists, Sp, variable, Colon, Sp, type, Comma, Sp, body);
    private static Formula Conditional(Formula condition, Formula yes, Formula no) =>
        Seq(Named("if"), Sp, condition, Sp, Named("then"), Sp, yes, Sp, Named("else"), Sp, no);
    private static Formula Projection(Formula value, byte index) => Seq(Paren(value), Dot, D(index));
    private static Formula Coord(Formula point, Formula axis) => Call("coord", point, axis);
    private static Formula SubtractBumps(Formula point, string bump) => Triple(
        Seq(Call("x", point), Minus, Call(bump, A, X)),
        Seq(Call("y", point), Minus, Call(bump, A, Y)),
        Seq(Call("z", point), Minus, Call(bump, A, Z)));

    private static Formula PointDefinition() => All(N, Naturals, All(Offset, Naturals,
        Equal(Point(Offset), Seq(OpenBrace, Triple(X, Y, Z), Sp, InMacro, Sp,
            Naturals, Times, Naturals, Times, Naturals, Sp, Mid, Sp,
            X, Plus, Y, Plus, Z, Plus, Offset, Eq, N, CloseBrace))));

    private static Formula CoordinateDefinition() => All(N, Naturals, All(Offset, Naturals,
        All(P, Point(Offset), Seq(Coord(P, X), Eq, Call("x", P), Land, Sp,
            Coord(P, Y), Eq, Call("y", P), Land, Sp, Coord(P, Z), Eq, Call("z", P)))));

    private static Formula AtCornerDefinition(bool down)
    {
        Formula condition = down
            ? Seq(Call("bumpPair", A, X), Leq, Sp, Call("x", V), Land, Sp,
                Call("bumpPair", A, Y), Leq, Sp, Call("y", V), Land, Sp,
                Call("bumpPair", A, Z), Leq, Sp, Call("z", V))
            : Seq(D(0), Lt, Coord(V, A));
        Formula point = SubtractBumps(V, down ? "bumpPair" : "bump");
        return All(N, Naturals, All(V, Point(D(0)), All(S, Bool, All(A, Axis,
            Equal(Call(down ? "atDown" : "atUp", V, S, A),
                Conditional(condition, Call("some", Call(down ? "down" : "up", S, point)), Named("none")))))));
    }

    private static Formula SheetCornersDefinition() => All(N, Naturals,
        All(V, Point(D(0)), All(S, Bool, Equal(Call("sheetCorners", V, S),
            Call("filterMap", Named("id"), Seq(OpenBracket,
                Call("atUp", V, S, X), Comma, Call("atUp", V, S, Y), Comma, Call("atUp", V, S, Z), Comma,
                Call("atDown", V, S, X), Comma, Call("atDown", V, S, Y), Comma, Call("atDown", V, S, Z),
                CloseBracket))))));

    private static Formula IncidentCornersDefinition() => All(N, Naturals,
        All(V, Point(D(0)), All(S, Bool, Equal(Call("incidentCorners", V, S),
            Conditional(Call("boundary", V),
                Seq(Call("sheetCorners", V, False), Sp, Plus, Plus, Sp, Call("sheetCorners", V, True)),
                Call("sheetCorners", V, S))))));

    private static Formula GoodDefinition()
    {
        Formula corners = Call("incidentCorners", V, S);
        Formula balance = Seq(Call("black", C, corners), Minus, Call("white", C, corners));
        Formula vertexLaw = All(V, Point(D(0)), All(S, Bool, Seq(D(3), Mid, Sp, Paren(balance))));
        return All(N, Naturals, All(C, Coloring, Seq(Call("Good", C), Iff, Sp, Paren(vertexLaw))));
    }

    private static Formula EdgeDefinition() => All(N, Naturals, Equal(Edges,
        Seq(OpenBrace, Triple(P, A, S), Sp, InMacro, Sp, Point(D(1)), Times, Axis, Times, Bool,
            Sp, Mid, Sp, Coord(P, A), Eq, D(0), Implies, Sp, S, Eq, False, CloseBrace)));

    private static Formula BelowDefinition() => All(N, Naturals, All(P, Point(D(1)), All(A, Axis,
        Seq(Coord(P, A), Neq, Sp, D(0), Implies, Sp, Equal(Call("below", P, A), SubtractBumps(P, "bump"))))));

    private static Formula EdgeFacesDefinition() => All(N, Naturals, All(Triple(P, A, S), Edges,
        Equal(Call("edgeFaces", Triple(P, A, S)),
            Pair(Call("up", S, P), Conditional(Equal(Coord(P, A), D(0)),
                Call("up", True, P), Call("down", S, Call("below", P, A)))))));

    private static Formula UniquenessFormula()
    {
        Formula minimum = Seq(Call("Good", C), Land, Sp, Call("foldCount", C), Eq, D(3), Times, Sp, N);
        Formula front = All(T, Cell, Equal(Apply(C, Pair(False, T)), B));
        Formula back = All(T, Cell, Equal(Apply(C, Pair(True, T)), Seq(Neg, Sp, B)));
        Formula uniform = Some(B, Bool, Seq(Paren(front), Land, Sp, Paren(back)));
        return All(N, Naturals, All(C, Coloring,
            Seq(D(0), Lt, N, Implies, Sp, Paren(Seq(Paren(minimum), Iff, Sp, Paren(uniform))))));
    }
}
