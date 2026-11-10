using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.TraceAvoidingArrays;

internal sealed class HardinA233251TriangleStripDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/TraceAvoidingArrays/HardinA233251TriangleStrip.";
    private const string Note = "D5/L/Automata/hardin2013a233251";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Barker's generating function for normalized six-colour three-column arrays.",
        H("Six-colour horizontal and antidiagonal exclusion"),
        Blocks(
            Paragraph(Text("OEIS A233251, revision 9, defines arrays on n rows and three columns. Horizontal and antidiagonal bonds exclude equal colours and colours summing to five. Vertical and main-diagonal neighbours are unconstrained. The upper-left colour is zero. Every 2, 3 and 4 has an earlier 1, and every 3 an earlier 2, in row-major order. The coefficient at index zero is zero. Seen, good and finish are the existing width-independent scanning definitions in HardinA233175PairStrip; beta is BooleanRankThreeK4.beta, with fibres {0,5}, {1,4}, {2,3}.")),
            Def("row", "Row", "A row", Eq(V("Row"), Arrow(Fin(3), Fin(6))),
                "A row is an ordered triple of colours."),
            Def("rowlegal", "rowLegal", "Horizontal bonds", RowLegalFormula(),
                "The two bonds lie between columns zero and one, and one and two."),
            Def("pairs", "pairs", "The boundary pair labels", PairsFormula(),
                "Only the pair labels of columns one and two constrain the following row."),
            Def("compatible", "compatible", "Antidiagonal bonds", CompatibleFormula(),
                "The preceding column-one label excludes the next column-zero label, and the preceding column-two label excludes the next column-one label."),
            Def("valid", "Valid", "Reachable boundary classes", ValidFormula(),
                "Colour one has occurred, the boundary labels differ, and before colour two occurs neither label is two."),
            Def("count", "a", "The literal filtered array count", CountFormula(),
                "The filter ranges over every function on Fin n times Fin 3. The strict lexicographic order on cell indices is the row-major order. The first-cell existential is false for the empty array.", true),
            Def("classcount", "classCount", "Counting one row by its final flag", ClassCountFormula(),
                "This integer sum counts exactly the legal normalized rows with the specified final second flag."),
            Def("firstcount", "firstCount", "Counting first rows by their final flag", FirstCountFormula(),
                "This integer sum fixes the first colour to zero and starts the shared scanner with both flags false."),
            Thm("certificate", "finite_certificate", "The one-row class counts", CertificateFormula(),
                "The eight reachable boundary classes split according to the second seen flag. A fully seen boundary has 48 continuations. A boundary with only colour one seen has 20 continuations entering the fully seen class and eight staying in its class. The first row gives one fully seen array and two arrays with only colour one seen."),
            Def("transfernormal", "widthNormal", "Row-major normalization at any width",
                TransferNormalFormula(),
                "For every row and column index, earlier means strict lexicographic order. "
                + "The two initial flags account for colours already seen before these rows."),
            Def("transferstep", "widthStep", "A row transfer at any width",
                TransferStepFormula(),
                "R is the row predicate, P extracts the boundary, and C tests the next row. "
                + "All predicates carry their Lean deciding instances."),
            Def("transferv", "widthV", "Continuation counts at any width",
                TransferVFormula(),
                "The empty continuation has weight one. Each further row applies the transfer."),
            Def("transfertotal", "widthTotal", "First-row aggregation at any width",
                TransferTotalFormula(),
                "A positive width provides the column-zero index. The initial flags are false."),
            Thm("transferbridge", "width_counting_bridge", "The literal count equals transfer",
                TransferBridgeFormula(),
                "Assume a positive width k and a boundary type B. The bond predicate E must "
                + "be equivalent to C after applying P to the preceding row. The displayed "
                + "filter is the literal array count on n+1 rows. R, C and E have deciding "
                + "instances. Decomposing an array into its first row and tail gives the "
                + "identity. Nat.div denotes natural quotient division and Nat.mod its "
                + "nonnegative remainder; neither operation enters these formulas."),
            Thm("colourbond", "colour_bond_iff", "A bond depends only on pair labels",
                ColourBondFormula(),
                "The fibres of beta are the complementary pairs. Distinct fibres are exactly "
                + "the pairs of colours that are unequal and do not sum to five."),
            Resolution("result", "result", "Barker's generating function", ResultFormula(),
                "Let U(k) and V(k) be the continuation counts with and without colour two already seen. Then U(0)=V(0)=1, U(k+1)=48U(k), and V(k+1)=8V(k)+20U(k). Decomposing the literal arrays into their first row and tail gives a(k+1)=U(k)+2V(k). Consequently a(n+3)=56a(n+2)-384a(n+1), with a(1)=3 and a(2)=104. Coefficient comparison proves the displayed identity in integer power series; every natural count is cast to an integer before forming the series."),
            Def("widthlegal", "widthLegal", "The literal legality predicate at any width",
                WidthLegalFormula(),
                "The first cell is zero, each row satisfies R, consecutive rows satisfy E, "
                + "and the shared scanner imposes row-major normalization. The Fin.val "
                + "projections and typed finite zeroes are explicit."),
            Def("widthdecidablenormal", "widthInstDecidableNormal", "Deciding row-major normalization",
                WidthDecidableNormalFormula(),
                "The defining expression is inferInstanceAs for the displayed finite "
                + "universal quantification and its two implications."),
            Def("widthdecidablegood", "widthInstDecidableGood", "Deciding a row scan at any width",
                WidthDecidableGoodFormula(),
                "These are the zero and successor equations of the defining induction on k. "
                + "The successor uses the original allowed decision and the recursive tail "
                + "decision with the advanced flags; no positive-width instance is required."),
            Def("widthdecidablelegal", "widthInstDecidableLegal", "Deciding the literal legality predicate",
                WidthDecidableLegalFormula(),
                "The defining expression is inferInstanceAs for the four displayed "
                + "conjuncts, using the deciding instances for R and E."))));

    private static DocumentBlock Def(string id, string name, string title, Formula formula, string prose,
        bool literature = false) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)),
            literature ? AssessedProvenance.FromLiterature(LibraryNoteRef.Create(Note))
                : AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
    private static DocumentBlock Thm(string id, string name, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
    private static DocumentBlock Resolution(string id, string name, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem,
            new OpenProblemResolutionClaim(ProblemSlugRef.Create("hardin233251"), ResolutionKind.Proved));

    private const string TransferRoot =
        "D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233251TriangleStrip.";
    private const string ScannerRoot =
        "D5.S3.Combinatorics.TraceAvoidingArrays.HardinA233175PairStrip.";
    private const string PairMap = "D5.S3.Observer.Separation.BooleanRankThreeK4.beta";
    private static Formula Qualified(string name) => Seq(name.Split('.').SelectMany((part, i) =>
        i == 0 ? new[] { Seq(Operatorname, Grp(V(part))) }
            : new[] { Dot, Seq(Operatorname, Grp(V(part))) }).ToArray());
    private static Formula ApplyName(string name, params Formula[] args) =>
        App(Qualified(name), args);
    private static Formula TransferCall(string name, params Formula[] args) =>
        ApplyName(TransferRoot + name, args);
    private static Formula NatType() => Qualified("Nat");
    private static Formula IntType() => Qualified("Int");
    private static Formula RowType() => Arrow(ApplyName("Fin", V("k")), Fin(6));
    private static Formula SeenType() => Qualified(ScannerRoot + "Seen");
    private static Formula FinZero(Formula type) => Parenthesized(Seq(D(0), Colon, Sp, type));
    private static Formula Decides(Formula proposition) =>
        ApplyName("Decidable", Parenthesized(proposition));
    private static Formula TypedDecision(Formula value, Formula proposition) =>
        Parenthesized(Seq(value, Colon, Sp, Decides(proposition)));
    private static Formula NormalBody()
    {
        var i = V("i"); var j = V("j"); var value = App(App(V("f"), i), j);
        Formula Is(byte d) => Eq(value, Parenthesized(Seq(D(d), Colon, Sp, Fin(6))));
        Formula Earlier(byte d) => Ex("r", ApplyName("Fin", V("n")),
            Ex("t", ApplyName("Fin", V("k")),
                And(Or(Lt(V("r"), i), And(Eq(V("r"), i), Lt(V("t"), j))),
                    Eq(App(App(V("f"), V("r")), V("t")),
                        Parenthesized(Seq(D(d), Colon, Sp, Fin(6)))))));
        return All("i", ApplyName("Fin", V("n")), All("j", ApplyName("Fin", V("k")), And(
            Imp(Or(Is(2), Or(Is(3), Is(4))),
                Or(Eq(ApplyName("Prod.fst", V("s")), Qualified("Bool.true")), Earlier(1))),
            Imp(Is(3), Or(Eq(ApplyName("Prod.snd", V("s")), Qualified("Bool.true")), Earlier(2))))));
    }
    private static Formula WidthLegalBody()
    {
        var rows = ApplyName("Fin", V("n")); var cols = ApplyName("Fin", V("k"));
        var i = V("i"); var j = V("j"); var a = V("A");
        Formula Cell(Formula r) => App(a, Pair(r, j));
        var first = Ex("i", rows, And(Eq(ApplyName("Fin.val", i), D(0)),
            Eq(App(a, Pair(i, FinZero(cols))), FinZero(Fin(6)))));
        var horizontal = All("i", rows, App(V("R"), Fn("j", cols, Cell(i))));
        var next = ApplyName("Fin.mk", Add(ApplyName("Fin.val", i), D(1)), V("h"));
        var bonds = All("i", rows,
            All("h", Lt(Add(ApplyName("Fin.val", i), D(1)), V("n")),
                App(V("E"), Fn("j", cols, Cell(i)), Fn("j", cols, Cell(next)))));
        var normal = TransferCall("widthNormal", Pair(Qualified("Bool.false"), Qualified("Bool.false")),
            Fn("i", rows, Fn("j", cols, Cell(i))));
        return And(first, And(horizontal, And(bonds, normal)));
    }
    private static Formula LegalParameters(Formula body, bool decisions = false)
    {
        var predicate = Arrow(RowType(), Qualified("Prop"));
        var relation = Arrow(RowType(), predicate);
        var array = Arrow(Product(ApplyName("Fin", V("n")), ApplyName("Fin", V("k"))), Fin(6));
        var tail = All("n", NatType(), All("A", array, body));
        if (decisions)
            tail = Instance("DecidablePred", V("R"), Instance("DecidableRel", V("E"), tail));
        return All("k", NatType(), PositiveWidth(All("R", predicate, All("E", relation, tail))));
    }
    private static Formula WidthLegalFormula() => LegalParameters(
        Eq(TransferCall("widthLegal", V("R"), V("E"), V("A")), Parenthesized(WidthLegalBody())));
    private static Formula WidthDecidableNormalFormula() => NormalParameters(
        Eq(TypedDecision(TransferCall("widthInstDecidableNormal", V("s"), V("f")),
                TransferCall("widthNormal", V("s"), V("f"))),
            ApplyName("inferInstanceAs", Parenthesized(Decides(NormalBody())))));
    private static Formula WidthDecidableLegalFormula() => LegalParameters(
        Eq(TypedDecision(TransferCall("widthInstDecidableLegal", V("R"), V("E"), V("A")),
                TransferCall("widthLegal", V("R"), V("E"), V("A"))),
            ApplyName("inferInstanceAs", Parenthesized(Decides(WidthLegalBody())))), true);
    private static Formula WidthDecidableGoodFormula()
    {
        var s = V("s"); var c = V("c");
        Formula Decision() => TypedDecision(TransferCall("widthInstDecidableGood", s, c), Good(s, c));
        var head = App(c, FinZero(ApplyName("Fin", Add(V("k"), D(1)))));
        var advanced = ApplyName(ScannerRoot + "advance", s, head);
        var tail = ApplyName("Fin.tail", c);
        var baseCase = All("s", SeenType(), All("c", Arrow(ApplyName("Fin", D(0)), Fin(6)),
            Eq(Decision(), ApplyName("Decidable.isTrue", Qualified("True.intro")))));
        var successor = All("k", NatType(), All("s", SeenType(),
            All("c", Arrow(ApplyName("Fin", Add(V("k"), D(1))), Fin(6)),
                Eq(Decision(), ApplyName("instDecidableAnd",
                    ApplyName(ScannerRoot + "instDecidableAllowed", s, head),
                    TransferCall("widthInstDecidableGood", advanced, tail))))));
        return new Formula.Aligned([baseCase, successor]);
    }
    private static Formula Fn(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, V(name), Colon, Sp, type, Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula Instance(string name, Formula argument, Formula body) =>
        Seq(OpenBracket, ApplyName(name, argument), CloseBracket, Sp, body);
    private static Formula GenericParameters(Formula body, bool positiveWidth = false)
    {
        var parameters = All("B", Qualified("Type"),
            All("R", Arrow(RowType(), Qualified("Prop")),
            All("P", Arrow(RowType(), V("B")),
            All("C", Arrow(V("B"), Arrow(RowType(), Qualified("Prop"))),
                Instance("DecidablePred", V("R"), Instance("DecidableRel", V("C"), body))))));
        return All("k", NatType(), positiveWidth ? PositiveWidth(parameters) : parameters);
    }
    private static Formula NormalParameters(Formula body) => All("k", NatType(),
        All("n", NatType(), All("s", SeenType(),
        All("f", Arrow(ApplyName("Fin", V("n")), RowType()), body))));
    private static Formula TransferNormalFormula()
    {
        var i = V("i"); var j = V("j"); var r = V("r"); var t = V("t");
        var value = App(App(V("f"), i), j);
        Formula Earlier(byte d) => Ex("r", ApplyName("Fin", V("n")),
            Ex("t", ApplyName("Fin", V("k")),
                And(Or(Lt(r, i), And(Eq(r, i), Lt(t, j))),
                    Eq(App(App(V("f"), r), t),
                        Parenthesized(Seq(D(d), Colon, Sp, Fin(6)))))));
        Formula Is(byte d) => Eq(value, Parenthesized(Seq(D(d), Colon, Sp, Fin(6))));
        return NormalParameters(Eq(TransferCall("widthNormal", V("s"), V("f")),
            All("i", ApplyName("Fin", V("n")), All("j", ApplyName("Fin", V("k")), And(
                Imp(Or(Is(2), Or(Is(3), Is(4))),
                    Or(Eq(ApplyName("Prod.fst", V("s")), V("true")), Earlier(1))),
                Imp(Is(3), Or(Eq(ApplyName("Prod.snd", V("s")), V("true")), Earlier(2))))))));
    }
    private static Formula WeightType() => Arrow(SeenType(), Arrow(V("B"), IntType()));
    private static Formula Good(Formula s, Formula c) => ApplyName(ScannerRoot + "good", s, c);
    private static Formula Finish(Formula s, Formula c) => ApplyName(ScannerRoot + "finish", s, c);
    private static Formula TransferStepFormula()
    {
        var c = V("c"); var s = V("s"); var p = V("p");
        var condition = And(App(V("R"), c), And(App(V("C"), p, c), Good(s, c)));
        return GenericParameters(All("w", WeightType(), All("s", SeenType(), All("p", V("B"),
            Eq(TransferCall("widthStep", V("R"), V("P"), V("C"), V("w"), s, p),
                SumOver("c", RowType(), Conditional(condition,
                    App(V("w"), Finish(s, c), App(V("P"), c)), Cast(D(0)))))))));
    }
    private static Formula TransferVFormula()
    {
        Formula Value(Formula n) => TransferCall("widthV", V("R"), V("P"), V("C"), n);
        var baseCase = All("s", SeenType(), All("p", V("B"),
            Eq(App(Value(D(0)), V("s"), V("p")), Cast(D(1)))));
        var recursion = All("n", NatType(), All("s", SeenType(), All("p", V("B"),
            Eq(App(Value(Add(V("n"), D(1))), V("s"), V("p")),
                TransferCall("widthStep", V("R"), V("P"), V("C"), Value(V("n")), V("s"), V("p"))))));
        return GenericParameters(And(baseCase, recursion));
    }
    private static Formula PositiveWidth(Formula body) =>
        Seq(OpenBracket, ApplyName("NeZero", V("k")), CloseBracket, Sp, body);
    private static Formula TransferTotalFormula()
    {
        var c = V("c"); var s = Pair(V("false"), V("false"));
        var zero = Parenthesized(Seq(D(0), Colon, Sp, ApplyName("Fin", V("k"))));
        var colourZero = Parenthesized(Seq(D(0), Colon, Sp, Fin(6)));
        var condition = And(Eq(App(c, zero), colourZero), And(App(V("R"), c), Good(s, c)));
        var sum = SumOver("c", RowType(), Conditional(condition,
            App(V("w"), Finish(s, c), App(V("P"), c)), Cast(D(0))));
        var identity = Eq(TransferCall("widthTotal", V("R"), V("P"), V("w")), sum);
        return All("k", NatType(), PositiveWidth(All("B", Qualified("Type"),
            All("R", Arrow(RowType(), Qualified("Prop")), All("P", Arrow(RowType(), V("B")),
            Instance("DecidablePred", V("R"), All("w", WeightType(), identity)))))));
    }
    private static Formula TransferBridgeFormula()
    {
        var n = V("n"); var a = V("A"); var i = V("i"); var j = V("j");
        var rows = ApplyName("Fin", Add(n, D(1))); var cols = ApplyName("Fin", V("k"));
        Formula Cell(Formula r, Formula t) => App(a, Pair(r, t));
        var zero = Parenthesized(Seq(D(0), Colon, Sp, cols));
        var colourZero = Parenthesized(Seq(D(0), Colon, Sp, Fin(6)));
        var first = Ex("i", rows, And(Eq(ApplyName("Fin.val", i), D(0)),
            Eq(Cell(i, zero), colourZero)));
        var horizontal = All("i", rows, App(V("R"), Fn("j", cols, Cell(i, j))));
        var next = ApplyName("Fin.mk", Add(ApplyName("Fin.val", i), D(1)), V("h"));
        var bond = All("i", rows,
            All("h", Lt(Add(ApplyName("Fin.val", i), D(1)), Add(n, D(1))),
                App(V("E"), Fn("j", cols, Cell(i, j)), Fn("j", cols, Cell(next, j)))));
        var normal = TransferCall("widthNormal", Pair(V("false"), V("false")),
            Fn("i", rows, Fn("j", cols, Cell(i, j))));
        var filter = ApplyName("Finset.filter", Fn("A", Arrow(Product(rows, cols), Fin(6)),
            And(first, And(horizontal, And(bond, normal)))), ApplyName("Finset.univ"));
        var edge = All("c", RowType(), All("d", RowType(),
            Iff(App(V("E"), V("c"), V("d")),
                App(V("C"), App(V("P"), V("c")), V("d")))));
        var identity = Eq(Cast(ApplyName("Finset.card", filter)),
            TransferCall("widthTotal", V("R"), V("P"),
                TransferCall("widthV", V("R"), V("P"), V("C"), n)));
        return GenericParameters(All("E", Arrow(RowType(), Arrow(RowType(), Qualified("Prop"))),
            Instance("DecidableRel", V("E"), Imp(edge, All("n", NatType(), identity)))), true);
    }
    private static Formula ColourBondFormula()
    {
        var x = V("x"); var y = V("y");
        return All("x", Fin(6), All("y", Fin(6), Iff(
            And(Ne(x, y), Ne(Add(ApplyName("Fin.val", x), ApplyName("Fin.val", y)), D(5))),
            Ne(ApplyName(PairMap, x), ApplyName(PairMap, y)))));
    }

    private static Formula RowLegalFormula()
    {
        var c = V("c"); var j = V("j");
        var x = App(c, Call("Fin.castSucc", j)); var y = App(c, Call("Fin.succ", j));
        return All("c", V("Row"), Iff(Call("rowLegal", c),
            All("j", Fin(2), And(Ne(x, y), Ne(Add(Call("val", x), Call("val", y)), D(5))))));
    }
    private static Formula PairsFormula()
    {
        var c = V("c");
        return All("c", V("Row"), Eq(Call("pairs", c),
            Pair(Call("beta", App(c, D(1))), Call("beta", App(c, D(2))))));
    }
    private static Formula CompatibleFormula()
    {
        var p = V("p"); var c = V("c");
        return All("p", Product(Fin(3), Fin(3)), All("c", V("Row"),
            Iff(Call("compatible", p, c), And(Ne(Proj(p, 1), Call("beta", App(c, D(0)))),
                Ne(Proj(p, 2), Call("beta", App(c, D(1))))))));
    }
    private static Formula ValidFormula()
    {
        var s = V("s"); var p = V("p");
        return All("s", V("Seen"), All("p", Product(Fin(3), Fin(3)), Iff(Call("Valid", s, p),
            And(Eq(Proj(s, 1), V("true")), And(Ne(Proj(p, 1), Proj(p, 2)),
                Imp(Eq(Proj(s, 2), V("false")), And(Ne(Proj(p, 1), D(2)), Ne(Proj(p, 2), D(2)))))))));
    }
    private static Formula CountFormula()
    {
        var n = V("n"); var a = V("A"); var i = V("i"); var j = V("j"); var r = V("r"); var k = V("k");
        var cells = Product(Call("Fin", n), Fin(3));
        Formula Cell(Formula row, Formula col) => App(a, Pair(row, col));
        var first = Ex("i", Call("Fin", n), And(Eq(Call("val", i), D(0)), Eq(Cell(i, D(0)), D(0))));
        var horizontal = All("i", Call("Fin", n), Call("rowLegal",
            Seq(LambdaLower, Sp, j, Colon, Sp, Fin(3), Sp, Mapsto, Sp, Cell(i, j))));
        var x = Cell(i, Call("Fin.succ", j));
        var y = Cell(Call("Fin.mk", Add(Call("val", i), D(1)), V("h")), Call("Fin.castSucc", j));
        var anti = All("i", Call("Fin", n), All("h", Lt(Add(Call("val", i), D(1)), n),
            All("j", Fin(2), And(Ne(x, y), Ne(Add(Call("val", x), Call("val", y)), D(5))))));
        Formula Earlier(byte colour) => Ex("r", Call("Fin", n), Ex("k", Fin(3),
            And(Or(Lt(r, i), And(Eq(r, i), Lt(k, j))), Eq(Cell(r, k), D(colour)))));
        var normal = All("i", Call("Fin", n), All("j", Fin(3), And(
            Imp(Or(Eq(Cell(i, j), D(2)), Or(Eq(Cell(i, j), D(3)), Eq(Cell(i, j), D(4)))), Earlier(1)),
            Imp(Eq(Cell(i, j), D(3)), Earlier(2)))));
        var predicate = Seq(LambdaLower, Sp, a, Colon, Sp, Arrow(cells, Fin(6)), Sp,
            Mapsto, Sp, Parenthesized(And(first, And(horizontal, And(anti, normal)))));
        return All("n", V("Nat"), Eq(Call("a", n),
            Call("Finset.card", Call("Finset.filter", predicate, Call("Finset.univ")))));
    }
    private static Formula ClassCountFormula()
    {
        var s = V("s"); var p = V("p"); var b = V("b"); var c = V("c");
        var condition = And(Call("rowLegal", c), And(Call("compatible", p, c),
            And(Call("good", s, c), Eq(Proj(Call("finish", s, c), 2), b))));
        return All("s", V("Seen"), All("p", Product(Fin(3), Fin(3)), All("b", V("Bool"),
            Eq(Call("classCount", s, p, b), SumOver("c", V("Row"),
                Conditional(condition, Cast(D(1)), Cast(D(0))))))));
    }
    private static Formula FirstCountFormula()
    {
        var b = V("b"); var c = V("c"); var state = Pair(V("false"), V("false"));
        var condition = And(Eq(App(c, D(0)), D(0)), And(Call("rowLegal", c),
            And(Call("good", state, c), Eq(Proj(Call("finish", state, c), 2), b))));
        return All("b", V("Bool"), Eq(Call("firstCount", b), SumOver("c", V("Row"),
            Conditional(condition, Cast(D(1)), Cast(D(0))))));
    }
    private static Formula CertificateFormula()
    {
        var s = V("s"); var p = V("p"); var c = V("c");
        var rows = All("s", V("Seen"), All("p", Product(Fin(3), Fin(3)), Imp(Call("Valid", s, p), And(
            Eq(Call("classCount", s, p, V("true")), Conditional(Proj(s, 2), Cast(D(4,8)), Cast(D(2,0)))),
            Eq(Call("classCount", s, p, V("false")), Conditional(Proj(s, 2), Cast(D(0)), Cast(D(8))))))));
        return And(rows, And(Eq(Call("firstCount", V("true")), Cast(D(1))),
            Eq(Call("firstCount", V("false")), Cast(D(2)))));
    }

    private static Formula ResultFormula()
    {
        var x = V("X"); var n = V("n");
        var series = Call("PowerSeries.mk", Seq(LambdaLower, Sp, n, Colon, Sp, V("Nat"), Sp,
            Mapsto, Sp, Cast(Call("a", n))));
        return Seq(Eq(Mul(Mul(Sub(D(1), Mul(D(8), x)), Sub(D(1), Mul(D(4,8), x))), series),
            Mul(x, Sub(D(3), Mul(D(6,4), x)))), Sp, TextFormula("in"), Sp, Call("PowerSeries", V("Int")));
    }

    private static Formula TextFormula(string s) => Seq(Operatorname,
        s.Contains('.') ? Grp(V(s.Split('.')[0]), Dot, V(s.Split('.')[1])) : Grp(V(s)));
    private static Formula V(string name) => F.Id(name);
    private static Formula Fin(byte n) => Call("Fin", D(n));
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Call(string name, params Formula[] args) => App(TextFormula(name), args);
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula Product(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Times, Sp, Parenthesized(b));
    private static Formula Arrow(Formula a, Formula b) => Seq(Parenthesized(a), Sp, To, Sp, b);
    private static Formula Pair(Formula a, Formula b) => Parenthesized(Seq(a, Comma, Sp, b));
    private static Formula Proj(Formula a, byte i) => Call(i == 1 ? "Prod.fst" : "Prod.snd", a);
    private static Formula Cast(Formula a) => Parenthesized(Seq(a, Colon, Sp, V("Int")));
    private static Formula Eq(Formula a, Formula b) => Seq(a, Sp, F.Eq, Sp, b);
    private static Formula Ne(Formula a, Formula b) => Seq(a, Sp, Neq, Sp, b);
    private static Formula Lt(Formula a, Formula b) => Seq(a, Sp, F.Lt, Sp, b);
    private static Formula Imp(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Implies, Sp, Parenthesized(b));
    private static Formula Iff(Formula a, Formula b) => Seq(Parenthesized(a), Sp, F.Iff, Sp, Parenthesized(b));
    private static Formula And(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Land, Sp, Parenthesized(b));
    private static Formula Or(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Lor, Sp, Parenthesized(b));
    private static Formula Conditional(Formula condition, Formula yes, Formula no) =>
        Parenthesized(Seq(TextFormula("if"), Sp, Parenthesized(condition), Sp, TextFormula("then"), Sp,
            yes, Sp, TextFormula("else"), Sp, no));
    private static Formula SumOver(string name, Formula type, Formula body) =>
        Seq(Sum, Underscore, Grp(V(name), Colon, Sp, type), Sp, Parenthesized(body));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, Parenthesized(body));
    private static Formula Ex(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, V(name), Colon, Sp, type, Comma, Sp, Parenthesized(body));
}
