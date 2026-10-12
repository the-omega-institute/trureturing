using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Palindromes;

internal sealed class ScatteredPalindromeMatchingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Words/Palindromes/ScatteredPalindromeMatching.";

    public DocumentDefinition Create()
    {
        var i = F.Id("i"); var j = F.Id("j"); var s = F.Id("s");
        var l = F.Id("l"); var h = F.Id("h"); var n = F.Id("n");
        var r = F.Id("r"); var f = F.Id("f");
        var valid = And(
            All("i", F.Id("I"), Imp(Member(i, s),
                And(Less(App(l, i), App(h, i)), Less(App(h, i), n)))),
            All("i", F.Id("I"), Imp(Member(i, s),
                All("j", F.Id("I"), Imp(Member(j, s),
                    And(Imp(Equal(App(l, i), App(l, j)), Equal(i, j)),
                        And(Imp(Equal(App(h, i), App(h, j)), Equal(i, j)),
                            NotEqual(App(l, i), App(h, j)))))))));
        return DocumentDefinition.Create(ScribeNode.Create(
            "Convex endpoint matching bounds the sum of inner gaps.",
            H("Convex Endpoint Matching"), Blocks(
                Paragraph(Text("A matching consists of disjoint endpoint pairs in the positions "
                    + "zero through n minus one. For an increasing, discretely convex natural-valued "
                    + "function, nesting the pairs at the extremes bounds every matching cost. "
                    + "All subtraction below is truncated subtraction in Nat.")),
                Node("matchValid", "Disjoint endpoint pairs", Parameters(false,
                    Iff(Call("matchValid", s, l, h, n), valid)),
                    "Both endpoints are in range, every lower endpoint is strictly below its "
                    + "upper endpoint, endpoints of the same kind are injective, and a lower "
                    + "endpoint never equals an upper endpoint.", AssessedProvenance.FromRepo()),
                Node("nestSum", "Cost of the nested matching",
                    All("f", Arrow(Nat, Nat), All("n", Nat, All("r", Nat,
                        Equal(Call("nestSum", f, n, r),
                            SumOver("i", App(Q("Finset", "range"), r),
                                App(f, Subtract(n, Multiply(D(2), Add(i, D(1)))))))))),
                    "The i-th nested pair leaves n−2(i+1) interior positions.", AssessedProvenance.FromRepo()),
                Node("nestSum_succ", "Removing the outer nested pair",
                    All("f", Arrow(Nat, Nat), All("n", Nat, All("r", Nat,
                        Equal(Call("nestSum", f, n, Add(r, D(1))),
                            Add(App(f, Subtract(n, D(2))),
                                Call("nestSum", f, Subtract(n, D(2)), r)))))),
                    "The first summand has gap n minus two; the remaining summands form the "
                    + "nested cost on n minus two positions.", AssessedProvenance.FromRepo(), DescribeRole.Theorem),
                Node("matching_bound", "The convex matching inequality",
                    All("I", F.Id("Type"), Instances(All("f", Arrow(Nat, Nat),
                        Imp(Call("Monotone", f),
                            Imp(Call("Monotone", Lambda("k", Nat,
                                Subtract(App(f, Add(F.Id("k"), D(1))), App(f, F.Id("k"))))),
                                All("s", Call("Finset", F.Id("I")),
                                All("l", Arrow(F.Id("I"), Nat),
                                All("h", Arrow(F.Id("I"), Nat), All("n", Nat,
                                Imp(Call("matchValid", s, l, h, n),
                                    Leq(SumOver("i", s,
                                            App(f, Subtract(Subtract(App(h, i), App(l, i)), D(1)))),
                                        Call("nestSum", f, n, App(Q("Finset", "card"), s))))))))))))),
                    "Choose the smallest lower endpoint and largest upper endpoint. When "
                    + "they belong to different pairs, discrete convexity bounds the cost "
                    + "after exchanging partners. Remove the outer pair and shift the "
                    + "remaining endpoints down by one. Strong induction on the number of "
                    + "pairs gives the bound, including the empty matching.", AssessedProvenance.FromRepo(), DescribeRole.Theorem))));
    }

    private static DocumentBlock Node(string name, string title, Formula formula, string prose, AssessedProvenance provenance,
        DescribeRole role = DescribeRole.Definition) => Describe.Lean(
            DescribeId.Create(name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), role);

    private static Formula Parameters(bool decidable, Formula body) =>
        All("I", F.Id("Type"), decidable
            ? Instances(All("s", Call("Finset", F.Id("I")),
                All("l", Arrow(F.Id("I"), Nat), All("h", Arrow(F.Id("I"), Nat),
                    All("n", Nat, body)))))
            : All("s", Call("Finset", F.Id("I")),
                All("l", Arrow(F.Id("I"), Nat), All("h", Arrow(F.Id("I"), Nat),
                    All("n", Nat, body)))));
    private static Formula Instances(Formula body) =>
        Seq(OpenBracket, Call("DecidableEq", F.Id("I")), CloseBracket, Comma, Sp, body);
    private static Formula Nat => F.Id("Nat");
    private static Formula Arrow(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula Q(string owner, string name) => Seq(Operatorname, Grp(F.Id(owner)), Dot, F.Id(name));
    private static Formula App(Formula name, params Formula[] args) => new Formula.Apply(name, [.. args]);
    private static Formula All(string x, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(x), type, body);
    private static Formula Lambda(string x, Formula type, Formula body) =>
        Seq(F.Id("fun"), Sp, Parenthesized(Seq(F.Id(x), Colon, Sp, type)), Sp, Mapsto, Sp, body);
    private static Formula Parenthesized(Formula body) => Seq(Open, body, Close);
    private static Formula SumOver(string x, Formula set, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(F.Id(x), Sp, InMacro, Sp, set)), Sp, body);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Less(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Leq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Member(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
}
