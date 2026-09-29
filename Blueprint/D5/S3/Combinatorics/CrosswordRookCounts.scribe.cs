using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics;

internal sealed class CrosswordRookCountsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/CrosswordRookCounts.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/lewis2026crossword");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An alternating five-column family realizes every positive count, and a three-by-three grid realizes zero.",
        H("Every Natural Rook-Placement Count Occurs"),
        Blocks(
            Node("white-same-across", "Horizontal row intervals", "white_same_across", WhiteSameAcrossFormula(),
                "Two white cells in the same row of the family lie in the same across word.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("side-word-stays-in-block", "Side-word confinement", "side_word_stays_in_block", SideWordFormula(),
                "A down word meeting the side column within a block remains between that block's first and last rows.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("tip-word-is-singleton", "Singleton outer words", "tip_word_is_singleton", TipWordFormula(),
                "A down word through an outer tip contains only that tip.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("odd-row-columns", "Odd-row white columns", "odd_row_columns", RowColumnsFormula(true),
                "Each occupied odd row consists of the central, side, and outer columns of its block.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("even-row-columns", "Even-row white columns", "even_row_columns", RowColumnsFormula(false),
                "Each occupied even row meets the central column and the side columns of the blocks incident to it.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("white-iff-pattern", "Spine, side runs, and tips", "white_iff_pattern", WhitePatternFormula(),
                "The white cells are precisely the central spine, the three-cell side runs, and the outer tips.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("same-down-iff", "Classification of down words", "same_down_iff", SameDownFormula(),
                "Two white cells share a down word exactly when both are central, both lie in one side block, or they coincide.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("candidate-row-unique", "At most one candidate rook per row", "candidate_row_unique", CandidateRowUniqueFormula(),
                "Candidate cells with the same row index are equal.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("candidate-side-choice", "Selected side endpoint", "candidate_side_choice", CandidateSideFormula(),
                "A candidate cell in a side block is its top endpoint before the central index and its bottom endpoint afterward.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("candidate-row-exists", "Candidate across-word coverage", "candidate_row_exists", CandidateRowExistsFormula(),
                "For k less than r, every occupied row contains a candidate rook.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("candidate-down-exists", "Candidate down-word coverage", "candidate_down_exists", CandidateDownExistsFormula(),
                "For k less than r, every white cell shares its down word with a candidate rook.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("candidate-is-placement", "Candidate completeness", "candidate_is_placement", CandidatePlacementFormula(),
                "Every central index less than r gives a complete non-attacking rook placement.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("placement-top-before-central", "Forced upper endpoints", "placement_top_before_central", ForcedEndpointFormula(true),
                "In any complete placement with a central rook in row two k, every earlier side block uses its upper endpoint.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("placement-bottom-after-central", "Forced lower endpoints", "placement_bottom_after_central", ForcedEndpointFormula(false),
                "In any complete placement with a central rook in row two k, every side block from k onward uses its lower endpoint.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("placement-eq-candidate", "Exhaustion by central indices", "placement_eq_candidate", PlacementCandidateFormula(),
                "For positive r, every complete placement equals the candidate for some k less than r.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("candidate-injective", "Distinct central choices", "candidate_injective", CandidateInjectiveFormula(),
                "Equal candidates with indices less than r have equal indices.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("zero-white", "The zero-count grid", "zeroWhite", ZeroWhiteFormula(),
                "The white cells are two adjacent cells in the first row and two vertically adjacent cells in the first column.", DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("zero-rook-count", "No placement on the zero grid", "zero_rook_count", Disp(Eq(Call("rookCount", F.Id("zeroWhite")), D(0))),
                "The two singleton down words in the first row would force two rooks in one across word, so the count is zero.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("result", "Every natural number occurs", "result", Disp(F.Id("claim")),
                "The zero grid and the positive family together realize every natural rook-placement count on square grids.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("lewis-won-crossword-rook-counts"), ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Nat() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula Call(string name, params Formula[] args) => new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(Formula body, params (string Name, Formula Domain)[] variables)
    {
        for (var i = variables.Length - 1; i >= 0; i--)
            body = new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variables[i].Name), variables[i].Domain, body);
        return body;
    }
    private static Formula Ex(string name, Formula domain, Formula body) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula And(params Formula[] clauses)
    {
        var result = clauses[^1];
        for (var i = clauses.Length - 2; i >= 0; i--)
            result = new Formula.Logic(clauses[i], FormulaLogicOperator.And, result);
        return result;
    }
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Or, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Mem(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Row(Formula c) => Seq(c, Dot, D(1));
    private static Formula Col(Formula c) => Seq(c, Dot, D(2));
    private static Formula A(Formula c) => Call("val", Row(c));
    private static Formula B(Formula c) => Call("val", Col(c));
    private static Formula Twice(Formula i) => Mul(D(2), i);
    private static Formula Cell(Formula r) => Call("Cell", Call("gridSize", r));
    private static Formula Finset(Formula a) => Call("Finset", a);
    private static Formula White(Formula r) => Call("white", r);
    private static Formula Candidate(Formula r, Formula k) => Call("candidate", r, k);
    private static Formula Block(Formula i, Formula c) => And(Le(Twice(i), A(c)), Le(A(c), Add(Twice(i), D(2))));

    private static Formula WhiteSameAcrossFormula()
    {
        var r = F.Id("r"); var c = F.Id("c"); var d = F.Id("d");
        return Disp(All(Imp(And(Mem(c, White(r)), Mem(d, White(r)), Eq(Row(c), Row(d))),
            Call("SameAcross", White(r), c, d)), ("r", Nat()), ("c", Cell(r)), ("d", Cell(r))));
    }

    private static Formula SideWordFormula()
    {
        var r = F.Id("r"); var i = F.Id("i"); var c = F.Id("c"); var d = F.Id("d");
        return Disp(All(Imp(And(Block(i, c), Eq(B(c), Call("side", i)), Call("SameDown", White(r), c, d)),
            Block(i, d)), ("r", Nat()), ("i", Nat()), ("c", Cell(r)), ("d", Cell(r))));
    }

    private static Formula TipWordFormula()
    {
        var r = F.Id("r"); var i = F.Id("i"); var c = F.Id("c"); var d = F.Id("d");
        return Disp(All(Imp(And(Eq(A(c), Add(Twice(i), D(1))), Eq(B(c), Call("tip", i)),
            Call("SameDown", White(r), c, d)), Eq(c, d)),
            ("r", Nat()), ("i", Nat()), ("c", Cell(r)), ("d", Cell(r))));
    }

    private static Formula RowColumnsFormula(bool odd)
    {
        var r = F.Id("r"); var i = F.Id("i"); var b = F.Id("b");
        var a = odd ? Add(Twice(i), D(1)) : Twice(i);
        var interval = And(Lt(a, Sub(Twice(r), D(1))), Le(Call("rowLeft", r, a), b), Le(b, Call("rowRight", r, a)));
        var columns = odd ? Or(Eq(b, D(2)), Or(Eq(b, Call("side", i)), Eq(b, Call("tip", i))))
            : Or(Eq(b, D(2)), Or(And(Lt(D(0), i), Eq(b, Call("side", Sub(i, D(1))))),
                And(Lt(Add(i, D(1)), r), Eq(b, Call("side", i)))));
        return Disp(All(Imp(Lt(odd ? Add(i, D(1)) : i, r), Iff(interval, columns)),
            ("r", Nat()), ("i", Nat()), ("b", Nat())));
    }

    private static Formula WhitePatternFormula()
    {
        var r = F.Id("r"); var c = F.Id("c"); var i = F.Id("i");
        var spine = And(Lt(A(c), Sub(Twice(r), D(1))), Eq(B(c), D(2)));
        var sides = Ex("i", Nat(), And(Lt(Add(i, D(1)), r), Eq(B(c), Call("side", i)), Block(i, c)));
        var tips = Ex("i", Nat(), And(Lt(Add(i, D(1)), r), Eq(A(c), Add(Twice(i), D(1))), Eq(B(c), Call("tip", i))));
        return Disp(All(Iff(Mem(c, White(r)), Or(spine, Or(sides, tips))), ("r", Nat()), ("c", Cell(r))));
    }

    private static Formula SameDownFormula()
    {
        var r = F.Id("r"); var c = F.Id("c"); var d = F.Id("d"); var i = F.Id("i");
        var sides = Ex("i", Nat(), And(Lt(Add(i, D(1)), r), Eq(B(c), Call("side", i)),
            Eq(B(d), Call("side", i)), Block(i, c), Block(i, d)));
        return Disp(All(Imp(And(Mem(c, White(r)), Mem(d, White(r))),
            Iff(Call("SameDown", White(r), c, d), Or(And(Eq(B(c), D(2)), Eq(B(d), D(2))), Or(sides, Eq(c, d))))),
            ("r", Nat()), ("c", Cell(r)), ("d", Cell(r))));
    }

    private static Formula CandidateRowUniqueFormula()
    {
        var r = F.Id("r"); var k = F.Id("k"); var c = F.Id("c"); var d = F.Id("d");
        return Disp(All(Imp(And(Mem(c, Candidate(r, k)), Mem(d, Candidate(r, k)), Eq(Row(c), Row(d))), Eq(c, d)),
            ("r", Nat()), ("k", Nat()), ("c", Cell(r)), ("d", Cell(r))));
    }

    private static Formula CandidateSideFormula()
    {
        var r = F.Id("r"); var k = F.Id("k"); var i = F.Id("i"); var c = F.Id("c");
        return Disp(All(Imp(And(Mem(c, Candidate(r, k)), Eq(B(c), Call("side", i)), Block(i, c)),
            Or(And(Lt(i, k), Eq(A(c), Twice(i))), And(Le(k, i), Eq(A(c), Add(Twice(i), D(2)))))),
            ("r", Nat()), ("k", Nat()), ("i", Nat()), ("c", Cell(r))));
    }

    private static Formula CandidateRowExistsFormula()
    {
        var r = F.Id("r"); var k = F.Id("k"); var a = F.Id("a"); var d = F.Id("d");
        return Disp(All(Imp(And(Lt(k, r), Lt(Call("val", a), Sub(Twice(r), D(1)))),
            Ex("d", Cell(r), And(Mem(d, Candidate(r, k)), Eq(Row(d), a)))),
            ("r", Nat()), ("k", Nat()), ("a", Call("Fin", Call("gridSize", r)))));
    }

    private static Formula CandidateDownExistsFormula()
    {
        var r = F.Id("r"); var k = F.Id("k"); var c = F.Id("c"); var d = F.Id("d");
        return Disp(All(Imp(And(Lt(k, r), Mem(c, White(r))), Ex("d", Cell(r),
            And(Mem(d, Candidate(r, k)), Call("SameDown", White(r), c, d)))),
            ("r", Nat()), ("k", Nat()), ("c", Cell(r))));
    }

    private static Formula CandidatePlacementFormula()
    {
        var r = F.Id("r"); var k = F.Id("k");
        return Disp(All(Imp(Lt(k, r), Call("IsRookPlacement", White(r), Candidate(r, k))), ("r", Nat()), ("k", Nat())));
    }

    private static Formula ForcedEndpointFormula(bool top)
    {
        var r = F.Id("r"); var k = F.Id("k"); var rooks = F.Id("R");
        var u = F.Id("u"); var i = F.Id("i"); var d = F.Id("d");
        var hypotheses = And(Call("IsRookPlacement", White(r), rooks), Mem(u, rooks), Eq(A(u), Twice(k)), Eq(B(u), D(2)));
        var endpoint = Ex("d", Cell(r), And(Mem(d, rooks), Eq(A(d), top ? Twice(i) : Add(Twice(i), D(2))), Eq(B(d), Call("side", i))));
        var body = All(Imp(Lt(Add(i, D(1)), r), Imp(top ? Lt(i, k) : Le(k, i), endpoint)), ("i", Nat()));
        return Disp(All(Imp(hypotheses, body), ("r", Nat()), ("k", Nat()), ("R", Finset(Cell(r))), ("u", Cell(r))));
    }

    private static Formula PlacementCandidateFormula()
    {
        var r = F.Id("r"); var rooks = F.Id("R"); var k = F.Id("k");
        return Disp(All(Imp(And(Lt(D(0), r), Call("IsRookPlacement", White(r), rooks)),
            Ex("k", Nat(), And(Lt(k, r), Eq(rooks, Candidate(r, k))))), ("r", Nat()), ("R", Finset(Cell(r)))));
    }

    private static Formula CandidateInjectiveFormula()
    {
        var r = F.Id("r"); var k = F.Id("k"); var l = F.Id("l");
        return Disp(All(Imp(And(Lt(k, r), Lt(l, r), Eq(Candidate(r, k), Candidate(r, l))), Eq(k, l)),
            ("r", Nat()), ("k", Nat()), ("l", Nat())));
    }

    private static Formula ZeroWhiteFormula() => Disp(Eq(F.Id("zeroWhite"), new Formula.SetLiteral([
        Seq(Open, D(0), Comma, Sp, D(1), Close), Seq(Open, D(0), Comma, Sp, D(2), Close),
        Seq(Open, D(1), Comma, Sp, D(0), Close), Seq(Open, D(2), Comma, Sp, D(0), Close)])));
}
