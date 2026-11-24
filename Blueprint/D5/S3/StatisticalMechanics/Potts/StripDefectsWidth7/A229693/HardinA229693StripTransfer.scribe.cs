using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.Potts.StripDefectsWidth7.A229693;

internal sealed class HardinA229693StripTransferDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/Potts/StripDefectsWidth7/A229693/HardinA229693StripTransfer.";
    private const string Note = "D5/L/SpinModels/hardin2013a229693";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact two-defect strip transfer.", H("Exact two-defect strip transfer"),
        Blocks(
            Describe.Lean(DescribeId.Create("exhausted-class"),
                DeclarationHandle.Create(Prefix + "exhaustedClass"), H("Classes at budget zero"),
                StatementSource.FromAuthor(Disp(ExhaustedClassFormula())),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("If Valid(p,1) holds, let i be the value of the A229585 class of p at budget zero. The return value is i minus 16 in Fin 96 when i is at least 16, and zero otherwise. If Valid(p,1) fails, use the A229635 first-occurrence equality-pattern index. Its first 40 entries are the lexicographically ordered canonical six-cell boundaries with exactly two adjacent equalities. Fin.ofNat 40 takes the residue of its natural-valued input modulo 40. Fin.natAdd 56 embeds the residue with offset 56. A pattern absent from the 40 entries in this branch has more than two adjacent equalities. Its equality mask is absent from the 96 A229635 representatives, whose lookup returns 96 before reduction modulo 96. The resulting index is zero, so the exhausted class is 56."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("cl"),
                DeclarationHandle.Create(Prefix + "cl"), H("Class of a boundary and budget"),
                StatementSource.FromAuthor(Disp(All("p", Call("HardinA229585StripData.Boundary"), All("d", V("Nat"), Eq(Call("HardinA229693StripTransfer.cl", V("p"), V("d")), Conditional(Eq(V("d"), Num("0")), Call("Fin.natAdd", Num("72"), Call("HardinA229693StripTransfer.exhaustedClass", V("p"))), Call("Fin.castAdd", Num("96"), Call("HardinA229585StripData.cl", V("p"), Sub(V("d"), Num("1")))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("A positive budget d uses the A229585 boundary class at budget d minus one."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("exit-read"),
                DeclarationHandle.Create(Prefix + "exitRead"), H("Column indices of the exhausted block"),
                StatementSource.FromAuthor(Disp(TypeOf(Call("HardinA229693StripTransfer.exitRead"), Arrow(Call("Fin", Num("96")), Call("Fin", Num("108")))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("This 96-entry map selects an old column when the returned value is below 72. Otherwise its value minus 72 is one of 36 radix-16 digit positions in the packed word selected by the source row. The tables store 56 active words and 38 distinct exhausted words. The successor formula pins the entries to their destination classes."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("t"),
                DeclarationHandle.Create(Prefix + "T"), H("Transfer matrix"),
                StatementSource.FromAuthor(Disp(TypeOf(Call("HardinA229693StripTransfer.T"), Call("Matrix", Call("Fin", Num("168")), Call("Fin", Num("168")), V("Int"))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("The leading block is the A229585 transfer matrix. The lower left block is zero. For a valid source boundary p and budget d, the entry at source cl(p,d) and exhausted destination 72 plus j counts next rows of exact cost d whose exhausted class is j. The 16 upper-right rows selected by zeroBudgetClass use the exhausted columns of the corresponding A229585 row followed by 40 zeros. The other 56 upper-right rows use the active words. For a right-column index j, an exitRead value below 72 selects the old leading entry at this source row and the indicated old column. The weight takes Int.toNat of that entry and casts it back to Int. An exitRead value at least 72 selects the digit at position exitRead minus 72 in the source word, starting with the least significant digit, and casts that digit to Int. Within the lower right block, the original exhausted sources reuse the exhausted rows and columns of A229585, followed by 40 zeros. The 40 new exhausted rows select from 38 distinct packed words. They return zero for exitRead values below 72 and cast the selected radix-16 digit to Int otherwise."))), DescribeRole.Definition),
            Node("uniformRegion", "Destinations with source-independent agreement",
                UniformRegionFormula(),
                "Each listed coordinate has count zero and matrix entry zero for all sources. Exhaustive integer evaluation over all 729 boundaries and all 2,187 successor rows gives a mismatch witness for each omitted coordinate at budgets zero through fifteen. At fifteen and above, the twelve-bond cost bound leaves at least three units and the classifiers stabilize.", DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("transition-counts"),
                DeclarationHandle.Create(Prefix + "transition_counts"), H("Multiplicity of a successor class"),
                StatementSource.FromAuthor(Disp(TransitionCounts())),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)),
                Blocks(Paragraph(Text("Every next row whose cost fits the available budget contributes one to its destination.")),
                    Paragraph(Text("At budget zero the possible destinations are 56 plus a value of zeroBudgetClass. At budget one the support is contained in the values of zeroBudgetClass and the interval 72 through 127. Both sides vanish outside these supports. At a constant zero boundary with budget one and destination 29, the literal count is two and the matrix entry is one.")),
                    Paragraph(Text("A successor at destination 129 or greater must spend the entire budget and its boundary can have at most two horizontal matches. The cross charge plus the first horizontal bond adds at most seven to the boundary cost. The lower destination cases follow from the budget-two classifier checked on six-cell boundaries.")),
                    Paragraph(Text("A separate candidate is that the source is valid if and only if the two rows agree at every destination. Exhaustive integer comparisons give the converse at budgets zero through two. At budget three the literal row has total at least 810, compared with a maximum matrix row total of 426, and the literal total is nondecreasing. The converse still lacks a Lean proof."))), DescribeRole.Theorem),
            Node("oldZeroImage", "Reindex an inherited exhausted class",
                All("i", Call("Fin", Num("72")), Eq(Call("oldZeroImage", V("i")),
                    Parenthesized(Seq(Q("if"), Sp, V("h"), Colon, Sp,
                        Parenthesized(Leq(Num("16"), Call("Fin.val", V("i")))), Sp, Q("then"), Sp,
                        Call("Fin.castAdd", Num("40"), Call("Fin.subNat", Num("16"), V("i"), V("h"))),
                        Sp, Q("else"), Sp, D(0))))),
                "Subtract 16 below the embedding into Fin 96. The index is zero when the input is below 16.", DescribeRole.Definition),
            Node("valid_parts", "Source validity",
                All("p", BoundaryType, All("d", V("Nat"), Iff(Call("HardinA229635State.Valid", V("p"), V("d")),
                    And(Leq(V("d"), D(2)), Leq(Call("HardinA229635State.h", V("p")), Sub(D(2), V("d"))))))),
                "Validity bounds the remaining budget and the number of equal neighbours in the boundary.", DescribeRole.Theorem),
            Node("fresh_relabel", "New class under relabelling",
                All("e", Call("Equiv.Perm", Fin3), All("p", BoundaryType,
                    Eq(Call("HardinA229635State.fresh", Compose(V("e"), V("p"))),
                        Call("HardinA229635State.fresh", V("p"))))),
                "Permuting colours preserves the equality pattern.", DescribeRole.Theorem),
            Node("exhausted_relabel", "Exhausted class under relabelling",
                All("e", Call("Equiv.Perm", Fin3), All("p", BoundaryType,
                    Eq(Call("exhaustedClass", Compose(V("e"), V("p"))), Call("exhaustedClass", V("p"))))),
                "The exhausted index depends on the equality pattern.", DescribeRole.Theorem),
            Node("active_cut", "Successor in the leading block", CutFormula(true),
                "A leading destination occurs with strictly positive budget after the transition.", DescribeRole.Theorem),
            Node("exhausted_cut", "Successor in the exhausted block", CutFormula(false),
                "An exhausted destination occurs when the cost equals the remaining budget.", DescribeRole.Theorem),
            Node("horizontal_cons", "Horizontal charge of a new head",
                All("x", Fin3, All("p", BoundaryType, HorizontalConsFormula())),
                "Prepending a colour adds one comparison with the first boundary cell.", DescribeRole.Theorem),
            Node("exhausted_support", "Support of the exhausted matrix rows",
                All("s", Fin168, Iff(ExistsIn("i", Call("Fin", Num("96")),
                    Ne(App(Call("HardinA229693StripTransfer.T"), Call("Fin.natAdd", Num("72"), V("i")), V("s")), Num("0"))),
                    ExistsIn("k", Call("Fin", Num("16")), Eq(SVal, Add(Num("56"), ZeroClassValue))))),
                "A destination occurs in at least one of the 96 exhausted matrix rows precisely when it lies in this image.", DescribeRole.Theorem),
            Node("matchCost", "Cost of a colour match",
                Seq(TypeOf(Call("matchCost"), Arrow(OptionColour, Arrow(Fin3, V("Nat")))), Comma, Sp,
                    Clause(All("x", Fin3, Eq(Call("matchCost", Call("none"), V("x")), D(0)))), Comma, Sp,
                    Clause(All("p", Fin3, All("x", Fin3,
                        Eq(Call("matchCost", Call("some", V("p")), V("x")),
                            Conditional(Eq(V("p"), V("x")), D(1), D(0))))))),
                "An absent colour costs zero. A present colour costs one exactly when it agrees with the current colour.", DescribeRole.Definition),
            Node("completionCost", "Cost of a completion",
                CompletionCostClauses(),
                "Sum the initial match, when a previous colour is supplied, the matches between neighbours, and the matches against the optional boundary colours.", DescribeRole.Definition),
            Node("completionRows", "Pruned completion list",
                CompletionRowsClauses(),
                "Try the three available colours in order, keep each head whose cost fits the budget, and prepend it to the completions at the remaining budget. The last cell must spend the entire remaining budget.", DescribeRole.Definition),
            Node("completionRows_count", "Multiplicity of qualifying rows",
                All("k", V("Nat"), All("p", Boundary, All("b", Call("Option", Fin3),
                    All("d", V("Nat"), All("f", Arrow(Row, V("Bool")),
                        Eq(Call("List.countP", V("f"), Call("completionRows", V("p"), V("b"), V("d"))),
                            Seq(Sum, Underscore, Grp(V("r"), Colon, Sp, Row), Sp, Parenthesized(Seq(
                                V("if"), Sp, Parenthesized(Eq(Call("completionCost", V("p"), V("b"), V("r")), V("d"))),
                                Sp, Land, Sp, Parenthesized(Eq(Call("f", V("r")), V("true"))),
                                Sp, V("then"), Sp, D(1), Sp, V("else"), Sp, D(0)))))))))),
                "The sum counts each qualifying row once.", DescribeRole.Theorem),
            Node("completionCodes", "Pruned list in base three",
                CompletionCodesClauses(),
                "Run the same recursion on a list of boundary colours. Prepending a colour x replaces the tail code c with the natural value of x plus three times c.", DescribeRole.Definition),
            Node("rowCode_cons", "Code of a row with a new head",
                All("m", V("Nat"), All("k", V("Nat"), All("x", Call("Fin", V("m")),
                    All("r", Arrow(Call("Fin", V("k")), Call("Fin", V("m"))),
                        Eq(Code(Call("Fin.cons", V("x"), V("r"))),
                            Add(Call("Fin.val", V("x")), Mul(V("m"), Code(V("r"))))))))),
                "The leading cell is the least significant digit of the code.", DescribeRole.Theorem),
            Node("completionCodes_eq", "Agreement of the two lists",
                All("k", V("Nat"), All("p", Boundary, All("b", Call("Option", Fin3), All("d", V("Nat"),
                    Eq(Call("completionCodes", Call("List.ofFn", V("p")), V("b"), V("d")),
                        Call("List.map", Seq(LambdaLower, Sp, V("r"), Sp, Mapsto, Sp, Code(V("r"))),
                            Call("completionRows", V("p"), V("b"), V("d")))))))),
                "The numeric enumerator returns the codes of the pruned completion list in the same order.", DescribeRole.Theorem))));

    private static Formula Num(string s) => D(s.Select(c => (byte)(c - '0')).ToArray());
    private static Formula V(string s) => new Formula.Symbol(FormulaIdentifier.Create(s));
    private static Formula Q(string s) => Seq(s.Split('.').SelectMany((x,i) => i == 0
        ? new[] { Seq(Operatorname, Grp(V(x))) }
        : new[] { Dot, Seq(Operatorname, Grp(V(x))) }).ToArray());
    private static Formula App(Formula g, params Formula[] a) => new Formula.Apply(g, [.. a]);
    private static Formula Call(string s, params Formula[] a) => a.Length == 0 ? Q(s) : App(Q(s), a);
    private static Formula Parenthesized(Formula a) => Seq(Open, a, Close);
    private static Formula Arrow(Formula a, Formula b) => Seq(Parenthesized(a), Sp, To, Sp, Parenthesized(b));
    private static Formula Eq(Formula a, Formula b) => Seq(a, Sp, F.Eq, Sp, b);
    private static Formula Leq(Formula a, Formula b) => Seq(a, Sp, Le, Sp, b);
    private static Formula And(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Land, Sp, Parenthesized(b));
    private static Formula Or(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Lor, Sp, Parenthesized(b));
    private static Formula Lt(Formula a, Formula b) => Seq(a, Sp, F.Lt, Sp, b);
    private static Formula Imp(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Implies, Sp, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula CastInt(Formula a) => Parenthesized(Seq(a, Colon, Sp, V("Int")));
    private static Formula All(string n, Formula t, Formula b) => Seq(Forall, Sp, V(n), Colon, Sp, t, Comma, Sp, Parenthesized(b));
    private static Formula SumOver(string n, Formula t, Formula b) => Seq(Sum, Underscore, Grp(V(n), Colon, Sp, t), Sp, Parenthesized(b));
    private static Formula Conditional(Formula c, Formula y, Formula n) => Parenthesized(Seq(Q("if"), Sp, Parenthesized(c), Sp, Q("then"), Sp, y, Sp, Q("else"), Sp, n));

    private static Formula TypeOf(Formula a, Formula b) => Seq(a, Sp, Colon, Sp, b);
    private static DocumentBlock Node(string declaration, string title, Formula formula, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(declaration.ToLowerInvariant().Replace('_', '-')), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(Disp(formula)),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create(Note)), Blocks(Paragraph(Text(prose))), role);

    private static Formula Fin168 => Call("Fin", Num("168"));
    private static Formula SVal => Call("Fin.val", V("s"));
    private static Formula ZeroClassValue => Call("Fin.val", Call("HardinA229585StripData.zeroBudgetClass", V("k")));
    private static Formula Fin3 => Call("Fin", D(3));
    private static Formula Boundary => Arrow(Call("Fin", V("k")), Call("Option", Fin3));
    private static Formula Row => Arrow(Call("Fin", Add(V("k"), D(1))), Fin3);
    private static Formula BoundaryType => Call("HardinA229585StripData.Boundary");
    private static Formula Compose(Formula e, Formula p) =>
        Lambda("i", App(e, App(p, V("i"))));
    private static Formula HorizontalConsFormula()
    {
        var row = Call("Fin.cons", V("x"), V("p"));
        return Eq(Call("DefectTransfer.bondDefects", Call("HardinA229585StripData.horizontal"), row, row),
            Add(Conditional(Eq(V("x"), App(V("p"), D(0))), D(1), D(0)), Call("HardinA229635State.h", V("p"))));
    }
    private static Formula CutFormula(bool active)
    {
        var p = V("p");
        var d = V("d");
        var c = V("c");
        var j = V("j");
        var index = active ? Call("Fin.castAdd", Num("96"), j) : Call("Fin.natAdd", Num("72"), j);
        var destination = Call("cl", p, Sub(d, c));
        var left = And(Leq(c, d), Eq(destination, index));
        var right = active
            ? And(Lt(D(0), d), And(Leq(c, Sub(d, D(1))),
                Eq(Call("HardinA229585StripData.cl", p, Sub(Sub(d, D(1)), c)), j)))
            : And(Eq(c, d), Eq(Call("exhaustedClass", p), j));
        return All("p", BoundaryType, All("d", V("Nat"), All("c", V("Nat"),
            All("j", Call("Fin", Num(active ? "72" : "96")), Iff(left, right)))));
    }

    private static Formula TransitionCounts()
    {
        var p = V("p");
        var d = V("d");
        var s = V("s");
        var r = V("r");
        var cost = Add(Call("HardinA229585StripData.cross", p, r),
            Call("DefectTransfer.bondDefects", Call("HardinA229585StripData.horizontal"), r, r));
        var destination = Call("HardinA229693StripTransfer.cl",
            Call("HardinA229585StripData.boundary", r), Sub(d, Parenthesized(cost)));
        var premise = Or(Call("HardinA229635State.Valid", p, d), Call("uniformRegion", d, s));
        var literal = SumOver("r", Call("HardinA229585StripData.Row"),
            Conditional(And(Leq(cost, d), Eq(destination, s)), CastInt(D(1)), CastInt(D(0))));
        return All("p", Call("HardinA229585StripData.Boundary"), All("d", V("Nat"),
            All("s", Fin168, Imp(premise, Eq(literal, App(Call("HardinA229693StripTransfer.T"),
                Call("HardinA229693StripTransfer.cl", p, d), s))))));
    }

    private static Formula ExhaustedClassFormula()
    {
        var p = V("p");
        var oldClass = Call("oldZeroImage", Call("HardinA229585StripData.cl", p, D(0)));
        var freshValue = Call("Fin.val", Call("HardinA229635State.fresh", p));
        var newClass = Call("Fin.natAdd", Num("56"), Call("Fin.ofNat", Num("40"), freshValue));
        return All("p", BoundaryType, Eq(Call("exhaustedClass", p),
            Conditional(Call("HardinA229635State.Valid", p, D(1)), oldClass, newClass)));
    }

    private static Formula UniformRegionFormula()
    {
        var d = V("d");
        var zero = And(Eq(d, D(0)), All("k", Call("Fin", Num("16")),
            Ne(SVal, Add(Num("56"), ZeroClassValue))));
        var one = And(Eq(d, D(1)), And(Lt(SVal, Num("72")),
            All("k", Call("Fin", Num("16")), Ne(SVal, ZeroClassValue))));
        var high = And(Or(Eq(d, D(1)), Leq(Num("13"), d)), Leq(Num("128"), SVal));
        var laterHigh = And(Leq(Num("10"), d), Leq(Num("129"), SVal));
        var twelve = And(Eq(d, Num("12")), InList(SVal, "9", "11"));
        var thirteen = And(Eq(d, Num("13")), InList(SVal, "2", "4", "5", "6", "8", "9", "10", "11", "12", "13", "14"));
        var fourteen = And(Eq(d, Num("14")), Lt(D(0), SVal));
        var low = And(Lt(SVal, Num("16")), Or(twelve, Or(thirteen, Or(fourteen, Leq(Num("15"), d)))));
        return All("d", V("Nat"), All("s", Fin168,
            Eq(Call("uniformRegion", d, V("s")), Or(zero, Or(one, Or(high, Or(laterHigh, low)))))));
    }

    private static Formula InList(Formula x, params string[] values) =>
        Seq(x, Sp, InMacro, Sp, OpenBracket,
            Seq(values.SelectMany((v, i) => i == 0 ? new[] { Num(v) } : new[] { Comma, Sp, Num(v) }).ToArray()),
            CloseBracket);

    private static Formula CompletionCostClauses()
    {
        var p = V("p");
        var b = V("b");
        var r = V("r");
        var k = V("k");
        var head = App(r, D(0));
        var baseEquation = Eq(Call("completionCost", p, b, r), Call("matchCost", b, head));
        var stepEquation = Eq(Call("completionCost", p, b, r),
            Add(LocalCharge(b, App(p, D(0)), head),
                Call("completionCost", Call("Fin.tail", p), Call("some", head), Call("Fin.tail", r))));
        return Seq(TypeOf(Call("completionCost"),
                All("k", V("Nat"), Arrow(Boundary, Arrow(OptionColour, Arrow(Row, V("Nat")))))), Comma, Sp,
            Clause(All("p", OptionalRow(D(0)), All("b", OptionColour, All("r", ColourRow(D(1)), baseEquation)))),
            Comma, Sp,
            Clause(All("k", V("Nat"), All("p", OptionalRow(Add(k, D(1))),
                All("b", OptionColour, All("r", ColourRow(Add(k, D(2))), stepEquation))))));
    }

    private static Formula CompletionRowsClauses()
    {
        var x = V("x");
        var p = V("p");
        var b = V("b");
        var d = V("d");
        var c = V("c");
        var k = V("k");
        var recursive = Call("List.map", Call("Fin.cons", x),
            Call("completionRows", Call("Fin.tail", p), Call("some", x), Sub(d, c)));
        var baseEquation = Eq(Call("completionRows", p, b, d),
            Call("List.map", Call("Function.const", Call("Fin", D(1))), LastColours(b, d)));
        var stepEquation = Eq(Call("completionRows", p, b, d),
            Call("List.flatMap", Lambda("x", LetCharge(b, App(p, D(0)), x,
                Conditional(Leq(c, d), recursive, Call("List.nil")))), Call("List.finRange", D(3))));
        return Seq(TypeOf(Call("completionRows"),
                All("k", V("Nat"), Arrow(Boundary, Arrow(OptionColour, Arrow(V("Nat"), Call("List", Row)))))), Comma, Sp,
            Clause(All("p", OptionalRow(D(0)), All("b", OptionColour, All("d", V("Nat"), baseEquation)))),
            Comma, Sp,
            Clause(All("k", V("Nat"), All("p", OptionalRow(Add(k, D(1))),
                All("b", OptionColour, All("d", V("Nat"), stepEquation))))));
    }

    private static Formula CompletionCodesClauses()
    {
        var x = V("x");
        var a = V("a");
        var bs = V("bs");
        var b = V("b");
        var d = V("d");
        var c = V("c");
        var list = Call("List", OptionColour);
        var recursive = Call("List.map", Lambda("r", Add(Call("Fin.val", x), Mul(D(3), V("r")))),
            Call("completionCodes", bs, Call("some", x), Sub(d, c)));
        var baseEquation = Eq(Call("completionCodes", Call("List.nil"), b, d),
            Call("List.map", Call("Fin.val"), LastColours(b, d)));
        var stepEquation = Eq(Call("completionCodes", Call("List.cons", a, bs), b, d),
            Call("List.flatMap", Lambda("x", LetCharge(b, a, x,
                Conditional(Leq(c, d), recursive, Call("List.nil")))), Call("List.finRange", D(3))));
        return Seq(TypeOf(Call("completionCodes"), Arrow(list,
                Arrow(OptionColour, Arrow(V("Nat"), Call("List", V("Nat")))))), Comma, Sp,
            Clause(All("b", OptionColour, All("d", V("Nat"), baseEquation))), Comma, Sp,
            Clause(All("a", OptionColour, All("bs", list,
                All("b", OptionColour, All("d", V("Nat"), stepEquation))))));
    }

    private static Formula Clause(Formula body) => Parenthesized(body);
    private static Formula OptionalRow(Formula n) => Arrow(Call("Fin", n), OptionColour);
    private static Formula ColourRow(Formula n) => Arrow(Call("Fin", n), Fin3);
    private static Formula LastColours(Formula b, Formula d) => Call("List.filter",
        Lambda("x", Call("BEq.beq", Call("matchCost", b, V("x")), d)), Call("List.finRange", D(3)));
    private static Formula LocalCharge(Formula b, Formula a, Formula x) =>
        Add(Call("matchCost", b, x), Call("matchCost", a, x));
    private static Formula LetCharge(Formula b, Formula a, Formula x, Formula body) =>
        Seq(Q("let"), Sp, V("c"), Sp, Colon, F.Eq, Sp, LocalCharge(b, a, x), Comma, Sp, body);
    private static Formula Lambda(string name, Formula body) =>
        Parenthesized(Seq(LambdaLower, Sp, V(name), Sp, Mapsto, Sp, body));
    private static Formula OptionColour => Call("Option", Fin3);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula ExistsIn(string n, Formula t, Formula b) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(n), t, Parenthesized(b));
    private static Formula Code(Formula row) => Call("Fin.val", Call("finFunctionFinEquiv", row));
}
