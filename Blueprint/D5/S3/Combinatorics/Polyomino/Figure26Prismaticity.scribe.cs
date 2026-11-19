using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Polyomino;

internal sealed class Figure26PrismaticityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Polyomino/Figure26Prismaticity.";
    private const string ProblemPrefix = "condon-dugan-goldman-williams-2026-figure-26-";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/FiniteGeometry/condon2026polyominodensity");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Both binary-colored 28-cell boards in Figure 26 are prismatic.",
        H("Prismatic polyhexes in Figure 26"),
        Blocks(
            Paragraph(Text("Section 9.1 and Figure 26 concern fixed translates on the hexagonal lattice. The cell carrier Point is the integer pair type from OrderedGridMemory. The coordinate changes below preserve edge adjacency, including the color and position of each cell.")),
            Node("hexSteps", "Axial edge steps", EqTo(F.Id("hexSteps"), Cells(
                (1, 0), (-1, 0), (0, 1), (0, -1), (1, -1), (-1, 1))),
                "An edge joins cells whose difference is one of these six steps."),
            Node("Adj", "Edge adjacency", AdjacencyFormula(),
                "The difference is computed componentwise on the integer pairs."),
            Node("BoardReach", "Paths within a board", ReachFormula(),
                "ReflTransGen allows the length-zero path. Both endpoints of each edge of a positive-length path lie in the board."),
            Node("IsPolyhex", "Nonempty connected boards", PolyhexFormula(),
                "Every pair of cells in the nonempty board is joined by a path using its cells."),
            Node("offsets", "Cell set of an ordered glyph", OffsetsFormula(),
                "There are four ordered offsets. Its underlying set is the image of all four indices."),
            Node("anchors", "Fixed translates in a board", AnchorsFormula(),
                "An anchor is a translation vector whose copy lies entirely in the board. Index zero supplies the finite candidate set. Two distinct vectors give distinct cell sets since a nonempty finite subset of the integer lattice has no nonzero translation period. Different copies may overlap."),
            Node("IsDense", "Minimum area for at least a given number of translates", DenseFormula(),
                "Area is the number of cells. The comparison ranges over all finite nonempty connected boards meeting the count."),
            Node("Word", "Four binary entries", EqTo(Word, Seq(Bool, Sp, Times, Sp, Group(
                    Seq(Bool, Sp, Times, Sp, Group(Seq(Bool, Sp, Times, Sp, Bool)))))),
                "The product is right-associated in Lean."),
            Node("wordAt", "Word read at an anchor", WordFormula(),
                "The four positions follow the displayed glyph in the recorded order. True denotes gray and false denotes white."),
            Node("IsBinaryDeBruijn", "Each word appears once", DeBruijnFormula(),
                "For every word in the fourfold product the exact multiplicity is one."),
            Node("FigureWitness", "The data certified for each panel", WitnessFormula(),
                "The connected glyph has four distinct cells. The connected board has 28 cells and exactly 16 anchors."),
            Node("IsPrismatic", "Prismaticity for these Figure 26 panels", PrismaticFormula(),
                "In this Figure 26 model prismaticity requires the displayed witness and density at 16 translates."),
            PanelPattern("left", "Left", (0, -1), (0, 0), (1, 0), (-1, 1)),
            PanelBoard("left", "Left", LeftBoard(),
                "The source cells are sent to the issue axes by (q,r) ↦ (−q,−r)."),
            PanelColor("left", "Left", LeftGray(),
                "The gray coordinate set is the image of the gray centers under the same board map."),
            PanelPattern("right", "Right", (0, 0), (1, 0), (-1, 1), (1, 1)),
            PanelBoard("right", "Right", RightBoard(),
                "The source cells are sent to the issue axes by (q,r) ↦ (−r,−q)."),
            PanelColor("right", "Right", RightGray(),
                "The board map sends the gray centers to this coordinate set. The right glyph alone is additionally shifted by (1,1), with the translate anchor shifted back accordingly."),
            Node("left_issue_prismatic", "Left panel prismaticity", PanelTheorem("left"),
                "Choose 16 distinct anchors in a competing board. The center and the three arm offsets lie in two residues of the index-three lattice kernel. Within each relevant residue, the arms form a simplex. If m input points have growth g, the occupied rows and their vertical endpoints give 2m ≤ g(g−1). Each output residue receives both centers and the preceding residue’s expanded arms. A finite check of the three residue counts summing to 16 forces at least 28 cells. The exhibited board has 28 cells and its 16 words occur exactly once.",
                new OpenProblemResolutionClaim(ProblemSlugRef.Create(ProblemPrefix + "left-prismaticity"),
                    ResolutionKind.Proved)),
            Node("right_issue_prismatic", "Right panel prismaticity", PanelTheorem("right"),
                "Choose 16 distinct anchors in a competing board. Each output column is the union of its own input column expanded by vertical offsets 0 and 2 and the preceding input column expanded by 0 and 1. Parity supplies the interior gain and the tight first-column bound. If a consecutive run has excess E at most 11, its at most five columns give an anchor count at most 47E/33. Runs separated by missing input columns have disjoint output supports. Thus excess at most 11 would allow fewer than 16 anchors. The exhibited board has 28 cells and its 16 words occur exactly once.",
                new OpenProblemResolutionClaim(ProblemSlugRef.Create(ProblemPrefix + "right-prismaticity"),
                    ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(string name, string title, Formula formula, string narrative,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("figure-26-" + name.ToLowerInvariant().Replace('_', '-')),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(narrative))),
            resolution is null ? DescribeRole.Definition : DescribeRole.Theorem, resolution);

    private static Formula Point => F.Id("Point");
    private static Formula Bool => F.Id("Bool");
    private static Formula Word => F.Id("Word");
    private static Formula Points => Call("Finset", Point);
    private static Formula Nats => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Color => Seq(Point, Sp, Rightarrow, Sp, Bool);
    private static Formula Four => Call("Fin", D(4));
    private static Formula Pattern => Seq(Four, Sp, Rightarrow, Sp, Point);
    private static Formula Group(Formula item) => Seq(Open, item, Close);
    private static Formula Pair(Formula a, Formula b) => Group(Seq(a, Comma, Sp, b));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula Bound(string name, Formula type) =>
        Group(Seq(F.Id(name), Sp, Colon, Sp, type));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Bound(name, type), Comma, Sp, body);
    private static Formula Lambda(string name, Formula type, Formula body) =>
        Seq(Bound(name, type), Sp, Mapsto, Sp, body);
    private static Formula SetOf(string name, Formula type, Formula body) =>
        Seq(OpenBrace, F.Id(name), Sp, Colon, Sp, type, Sp, Mid, Sp, body, CloseBrace);
    private static Formula Rel(Formula a, FormulaRelationOperator op, Formula b) => new Formula.Relation(a, op, b);
    private static Formula EqTo(Formula a, Formula b) => Rel(a, FormulaRelationOperator.Equal, b);
    private static Formula Mem(Formula a, Formula b) => Rel(a, FormulaRelationOperator.MemberOf, b);
    private static Formula Le(Formula a, Formula b) => Rel(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Logic(Formula a, FormulaLogicOperator op, Formula b) => new Formula.Logic(Group(a), op, Group(b));
    private static Formula And(Formula a, Formula b) => Logic(a, FormulaLogicOperator.And, b);
    private static Formula And(Formula a, Formula b, Formula c, Formula d, Formula e, Formula f) =>
        And(a, And(b, And(c, And(d, And(e, f)))));
    private static Formula IffTo(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Imp(Formula a, Formula b) => Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Card(Formula a) => Call("card", a);
    private static Formula Offset(Formula p) => Call("offsets", p);
    private static Formula Anchors(Formula p, Formula b) => Call("anchors", p, b);
    private static Formula Polyhex(Formula b) => Call("IsPolyhex", b);
    private static Formula Dense(Formula p, Formula n, Formula b) => Call("IsDense", p, n, b);
    private static Formula Number(int n) => n < 0 ? Seq(Minus, D((byte)(-n))) : D((byte)n);
    private static Formula Cell((int X, int Y) p) => Pair(Number(p.X), Number(p.Y));
    private static Formula Items(Formula first, params Formula[] rest)
    {
        var parts = new System.Collections.Generic.List<Formula> { first };
        foreach (Formula item in rest)
        {
            parts.Add(Comma);
            parts.Add(Sp);
            parts.Add(item);
        }
        return Seq([.. parts]);
    }
    private static Formula Cells(params (int X, int Y)[] points)
    {
        var rest = new Formula[points.Length - 1];
        for (int i = 1; i < points.Length; i++)
            rest[i - 1] = Cell(points[i]);
        return Seq(OpenBrace, Items(Cell(points[0]), rest), CloseBrace);
    }

    private static Formula AdjacencyFormula()
    {
        Formula p = F.Id("p"), q = F.Id("q");
        return All("p", Point, All("q", Point, IffTo(Call("Adj", p, q), Mem(Sub(q, p), F.Id("hexSteps")))));
    }

    private static Formula ReachFormula()
    {
        Formula b = F.Id("B"), p = F.Id("p"), q = F.Id("q"), x = F.Id("x"), y = F.Id("y");
        Formula edges = Lambda("x", Point, Lambda("y", Point, And(Mem(x, b), And(Mem(y, b), Call("Adj", x, y)))));
        return All("B", Points, All("p", Point, All("q", Point,
            IffTo(Call("BoardReach", b, p, q), Call("ReflTransGen", edges, p, q)))));
    }

    private static Formula PolyhexFormula()
    {
        Formula b = F.Id("B"), p = F.Id("p"), q = F.Id("q");
        Formula connected = All("p", Point, Imp(Mem(p, b),
            All("q", Point, Imp(Mem(q, b), Call("BoardReach", b, p, q)))));
        return All("B", Points, IffTo(Polyhex(b), And(Call("Nonempty", b), connected)));
    }

    private static Formula OffsetsFormula()
    {
        Formula p = F.Id("P");
        return All("P", Pattern, EqTo(Offset(p), Call("image", p, F.Id("univ"))));
    }

    private static Formula AnchorsFormula()
    {
        Formula p = F.Id("P"), b = F.Id("B"), x = F.Id("x"), t = F.Id("t"), i = F.Id("i");
        Formula candidate = Call("image", Lambda("x", Point, Sub(x, Call("P", D(0)))), b);
        Formula fits = Lambda("t", Point, All("i", Four, Mem(Add(t, Call("P", i)), b)));
        return All("P", Pattern, All("B", Points, EqTo(Anchors(p, b), Call("filter", fits, candidate))));
    }

    private static Formula DenseFormula()
    {
        Formula p = F.Id("P"), b = F.Id("B"), n = F.Id("N"), c = F.Id("C");
        Formula minimum = All("C", Points, Imp(Polyhex(c), Imp(Le(n, Card(Anchors(p, c))), Le(Card(b), Card(c)))));
        return All("P", Pattern, All("N", Nats, All("B", Points,
            IffTo(Dense(p, n, b), And(Polyhex(b), And(Le(n, Card(Anchors(p, b))), minimum))))));
    }

    private static Formula WordFormula()
    {
        Formula p = F.Id("P"), color = F.Id("c"), t = F.Id("t");
        Formula Entry(byte i) => Call("c", Add(t, Call("P", D(i))));
        Formula tuple = Group(Items(Entry(0), Entry(1), Entry(2), Entry(3)));
        return All("P", Pattern, All("c", Color, All("t", Point, EqTo(Call("wordAt", p, color, t), tuple))));
    }

    private static Formula WordCounts(Formula p, Formula b, Formula color)
    {
        Formula t = F.Id("t"), w = F.Id("w");
        Formula hasWord = Lambda("t", Point, EqTo(Call("wordAt", p, color, t), w));
        return All("w", Word, EqTo(Card(Call("filter", hasWord, Anchors(p, b))), D(1)));
    }

    private static Formula AllData(Formula formula) => All("P", Pattern, All("B", Points, All("c", Color, formula)));

    private static Formula DeBruijnFormula()
    {
        Formula p = F.Id("P"), b = F.Id("B"), color = F.Id("c");
        return AllData(IffTo(Call("IsBinaryDeBruijn", p, b, color), WordCounts(p, b, color)));
    }

    private static Formula Witness(Formula p, Formula b, Formula last) =>
        And(Polyhex(Offset(p)), EqTo(Card(Offset(p)), D(4)), Polyhex(b),
            EqTo(Card(b), D(2, 8)), EqTo(Card(Anchors(p, b)), D(1, 6)), last);

    private static Formula WitnessFormula()
    {
        Formula p = F.Id("P"), b = F.Id("B"), color = F.Id("c");
        return AllData(IffTo(Call("FigureWitness", p, b, color), Witness(p, b, Call("IsBinaryDeBruijn", p, b, color))));
    }

    private static Formula PrismaticFormula()
    {
        Formula p = F.Id("P"), b = F.Id("B"), color = F.Id("c");
        return AllData(IffTo(Call("IsPrismatic", p, b, color),
            And(Call("FigureWitness", p, b, color), Dense(p, D(1, 6), b))));
    }

    private static Formula PanelTheorem(string side)
    {
        Formula p = F.Id(side + "IssuePattern"), b = F.Id(side + "IssueBoard"), color = F.Id(side + "IssueColor");
        return And(Witness(p, b, WordCounts(p, b, color)), Dense(p, D(1, 6), b));
    }

    private static DocumentBlock PanelPattern(string side, string title, params (int X, int Y)[] offsets) =>
        Node(side + "IssuePattern", title + " glyph in issue coordinates",
            EqTo(F.Id(side + "IssuePattern"), Seq(OpenBracket, Items(
                Cell(offsets[0]), Cell(offsets[1]), Cell(offsets[2]), Cell(offsets[3])), CloseBracket)),
            "The vector lists the values at indices zero through three in order.");

    private static DocumentBlock PanelBoard(string side, string title, Formula cells, string prose) =>
        Node(side + "IssueBoard", title + " board in issue coordinates",
            EqTo(F.Id(side + "IssueBoard"), cells), prose);

    private static DocumentBlock PanelColor(string side, string title, Formula gray, string prose)
    {
        Formula p = F.Id("p");
        return Node(side + "IssueColor", title + " gray-cell indicator",
            All("p", Point, EqTo(Call(side + "IssueColor", p), Call("decide", Mem(p, gray)))), prose);
    }

    private static Formula LeftBoard() => Cells(
        (-6, 2), (-6, 3), (-5, 0), (-5, 1), (-5, 2), (-5, 3),
        (-4, -2), (-4, -1), (-4, 0), (-4, 1), (-4, 2), (-3, -3),
        (-3, -2), (-3, -1), (-3, 0), (-3, 1), (-3, 2), (-2, -3),
        (-2, -2), (-2, -1), (-2, 0), (-2, 1), (-1, -2), (-1, -1),
        (-1, 0), (-1, 1), (0, -1), (0, 0));
    private static Formula LeftGray() => Cells(
        (-6, 2), (-5, 0), (-5, 3), (-4, -2), (-4, -1), (-3, -1),
        (-3, 0), (-3, 1), (-2, -2), (-2, -1), (-2, 1), (-1, -2),
        (-1, 0));
    private static Formula RightBoard() => Cells(
        (-7, 0), (-6, -1), (-6, 0), (-5, -2), (-5, -1), (-5, 0),
        (-4, -3), (-4, -2), (-4, -1), (-4, 0), (-3, -3), (-3, -2),
        (-3, -1), (-3, 0), (-2, -4), (-2, -3), (-2, -2), (-2, -1),
        (-2, 0), (-1, -4), (-1, -3), (-1, -2), (-1, -1), (-1, 0),
        (0, -3), (0, -2), (0, -1), (0, 0));
    private static Formula RightGray() => Cells(
        (-6, -1), (-5, -2), (-4, -2), (-3, -3), (-3, -2), (-3, -1),
        (-3, 0), (-2, -1), (-1, -2), (-1, 0), (0, -2), (0, -1));
}
