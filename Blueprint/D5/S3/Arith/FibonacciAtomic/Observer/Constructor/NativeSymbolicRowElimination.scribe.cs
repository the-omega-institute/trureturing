using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer.Constructor;

internal sealed class NativeSymbolicRowEliminationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete raw row elimination over one original variable family",
        H("Complete raw rows and shared source reconstruction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("native-symbolic-exterior-match-exact"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeSymbolicRowElimination.exterior_match_exact"),
                H("A symbolic exterior matches exactly when its finite bindings hold"),
                StatementSource.FromAuthor(Disp(Statement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("A symbolic exterior has Boolean leaves, residual variables and literal address holes. The matcher descends through ordered pair constructors, rejects constructor and hole mismatches, and decodes a target subtree into a source term only when that subtree contains no address hole. Every successful variable match contributes an explicit binding to a finite list; repeated variables are retained as repeated bindings.")),
                    Paragraph(Text("For every valuation, the theorem equates the filled symbolic exterior with an arbitrary concrete hole exterior exactly with the existence of the matcher output whose bindings all evaluate to the valuation. Constructor and address-hole mismatches are rejected. Literal holes with the same address match exactly, while residual variables expand only to hole-free source subtrees and retain every returned binding. The full row compiler combines these bindings with every sign of the reached partition. Interpreted positive history equations remain separate."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("native-complete-raw-row-elimination"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeSymbolicRowElimination.complete_row_elimination"),
                H("All raw rows and free signed comparisons share one exact reconstruction"),
                StatementSource.FromAuthor(Disp(RowsStatement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("A raw row is a cut set paired with an arbitrary concrete hole exterior and an arbitrary finite relation on addresses. No attained-row or partition-validity premise is supplied. The compiler fixes the ordered reached list from the source term, rejects relation pairs outside it, and retains every ordered reached pair: membership gives an equation, and nonmembership gives a disequality. This includes diagonals, both orders, repeated class occurrences, every cross-class pair and empty reached sets. The exterior matcher also retains uncut frontier variables and literal address holes.")),
                    Paragraph(Text("The finite extra argument contains arbitrary additional free-term equations and disequalities over the same original type. All rows, exterior bindings and extra equations enter one existing native unifier. Its total action reconstructs every original variable, including repeated and unused coordinates. The output explicitly enumerates its free subtype of the original finite presentation. Its domain consists only of arbitrary finite native trees satisfying the substituted disequalities; no positive row equation, shape restriction or normality condition remains. Failure means that no assignment satisfies the positive constraints. Success may still have an empty disequality domain.")),
                    Paragraph(Text("For every sufficiently deep prefix pattern, filling the same named frontiers gives the actual original source. The existing symbolic recutting theorem identifies its complete literal row with the symbolic row, preserving the concrete exterior and every partition bit. The second conjunct states that exact actual-source consequence for all prefix-free cuts whose addresses lie above the frontier. Taking the naming map to be the identity gives the original pattern and its literal original frontier tuple.")),
                    Paragraph(Text("In the formula, fst and snd are pair projections, free and theta and delta are output fields, and composition(v,name) is the valuation x mapped to v(name(x)). Evaluation after simultaneous substitution reconstructs the same source term because it reconstructs every original coordinate. The result eliminates free row equalities only; equations involving the interpreted substitution history and the general mixed image and cofinality conclusions remain outside its scope."))),
                DescribeRole.Theorem)
        )));

    private static Formula V(string s) => F.Id(s);
    private static Formula C(string s, params Formula[] xs) => new Formula.Apply(Seq(Operatorname, Grp(V(s))), [.. xs]);
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula All(string s, Formula t, Formula b) => Seq(Forall, Sp, V(s), Colon, Sp, t, Comma, Sp, Par(b));
    private static Formula Some(string s, Formula t, Formula b) => Seq(Exists, Sp, V(s), Colon, Sp, t, Comma, Sp, Par(b));
    private static Formula EqOf(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula And(Formula a, Formula b) => Seq(Par(a), Sp, Land, Sp, Par(b));
    private static Formula IffOf(Formula a, Formula b) => Seq(Par(a), Sp, Iff, Sp, Par(b));
    private static Formula Arr(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);

    private static Formula Statement()
    {
        var x = V("X");
        var p = V("p");
        var u = V("u");
        var v = V("v");
        var bs = V("bs");
        var filled = C("exteriorFill", v, p);
        var matched = C("matchExterior", p, u);
        var binding = C("bindingHolds", v, bs);
        var rhs = Some("bs", C("List", C("Prod", x, C("Term", x))),
            And(EqOf(matched, C("some", bs)), binding));
        return All("X", V("Type"), All("p", C("SymbolicExterior", x),
            All("u", V("HoleExterior"), All("v", Arr(x, V("Source")), IffOf(EqOf(filled, u), rhs)))));
    }

    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));
    private static Formula Member(Formula a, Formula b) => Seq(a, Sp, InMacro, Sp, b);
    private static Formula Fst(Formula a) => C("fst", a);
    private static Formula Snd(Formula a) => C("snd", a);
    private static Formula Bounded(string x, Formula type, Formula list, Formula body) =>
        All(x, type, Imp(Member(V(x), list), body));

    private static Formula Extras()
    {
        var x = V("X");
        var termPair = C("Prod", C("Term", x), C("Term", x));
        var v = V("v");
        var c = V("c");
        var d = V("e");
        return And(
            Bounded("c", termPair, Fst(V("extra")),
                EqOf(C("evaluate", v, Fst(c)), C("evaluate", v, Snd(c)))),
            Bounded("e", termPair, Snd(V("extra")),
                Seq(C("evaluate", v, Fst(d)), Sp, Neq, Sp, C("evaluate", v, Snd(d)))));
    }

    private static Formula Image()
    {
        var o = V("o");
        var z = V("z");
        var e = V("e");
        var free = C("free", o);
        var reconstructed = All("x", V("X"),
            EqOf(C("evaluate", z, C("theta", o, V("x"))), C("v", V("x"))));
        var negatives = Bounded("e", C("Prod", C("Term", free), C("Term", free)),
            C("delta", o), Seq(C("evaluate", z, Fst(e)), Sp, Neq, Sp, C("evaluate", z, Snd(e))));
        return Some("o", C("RowOutput", V("X")),
            And(EqOf(C("eliminateRows", V("p"), V("t"), V("rs"), V("extra")), C("some", o)),
                Some("z", Arr(free, V("Source")), And(reconstructed, negatives))));
    }

    private static Formula RowsStatement()
    {
        var r = V("r");
        var rs = V("rs");
        var symbolic = Bounded("r", V("RawRow"), rs,
            EqOf(C("symbolicRecord", Fst(r), V("t"), V("v")), Snd(r)));
        var actualSource = C("fill", V("pat"), C("composition", V("v"), V("name")));
        var actual = Bounded("r", V("RawRow"), rs,
            EqOf(C("literalRecord", Fst(r), actualSource), Snd(r)));
        var prefix = Bounded("r", V("RawRow"), rs, C("CutPrefixFree", Fst(r)));
        var depth = Bounded("r", V("RawRow"), rs,
            Bounded("q", V("Address"), Fst(r), Seq(C("length", V("q")), Sp, Lt, Sp, V("d"))));
        var pattern = All("d", V("Nat"), All("pat", C("Pattern", V("d")),
            All("name", Arr(C("Frontier", V("pat")), V("X")),
                Imp(EqOf(V("t"), C("patternTerm", V("pat"), V("name"))),
                    Imp(prefix, Imp(depth, IffOf(And(actual, Extras()), Image())))))));
        return All("X", V("Type"), All("p", C("Presentation", V("X")),
            All("t", C("Term", V("X")), All("rs", C("List", V("RawRow")),
                All("extra", C("SignedConstraints", V("X")), All("v", Arr(V("X"), V("Source")),
                    And(IffOf(And(symbolic, Extras()), Image()), pattern)))))));
    }

}
