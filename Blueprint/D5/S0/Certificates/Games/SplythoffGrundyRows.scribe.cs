using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates.Games;

internal sealed class SplythoffGrundyRowsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S0/Certificates/Games/SplythoffGrundyRows.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/fokkinkrust2024splythoff");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every Splythoff Nim row and column contains each Sprague–Grundy value exactly once.",
        H("Splythoff Nim: all Grundy values in every row and column"),
        Blocks(
            Node("splythoff-moves", "Single, double and split moves", "splythoffMove",
                MoveFormula(), DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source),
                "Section 2 (arXiv v2, printed page 4) states: \"We modify Wythoff Nim by "
                    + "allowing the additional option of a split. If a player takes an equal "
                    + "number of counters from both piles and only one pile remains, then he "
                    + "can split the remaining pile into two.\" It also states: \"A split is "
                    + "only allowed after taking counters from both piles. It is not allowed "
                    + "to take all counters from a single pile and then split.\" The first "
                    + "two clauses reduce a single pile, the third removes the same positive "
                    + "number k from both piles, and the fourth distributes the remainder "
                    + "after removing the smaller positive pile. Pile sizes include zero; "
                    + "subtraction is natural-number truncated subtraction."),
            Node("splythoff-followers", "The finite set of followers", "followers",
                FollowersFormula(), DescribeRole.Definition,
                AssessedProvenance.FromRepo(Source),
                "Every follower coordinate is at most the larger starting pile. Filtering "
                    + "this finite rectangle by splythoffMove therefore retains exactly "
                    + "the legal followers, including all allowed splits."),
            Node("splythoff-grundy", "Recursive Sprague–Grundy values", "grundy",
                GrundyFormula(), DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source),
                "The mex operation is the least natural number absent from a finite set. "
                    + "The definition maps every attached follower to its recursively "
                    + "computed value and takes mex after converting the list to a finite "
                    + "set. Every legal move decreases the sum of the two pile sizes, "
                    + "which makes this recursion well founded. The subtype variable q "
                    + "carries its membership proof; val(q) is its ordered pair."),
            Node("splythoff-claim", "The row and column statement", "claim",
                ClaimFormula(), DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source),
                "Section 9 (arXiv v2, printed page 16) states: \"For Splythoff Nim, it "
                    + "appears that every row or column contains each Sprague-Grundy "
                    + "value once and no more. We do not have a proof for that.\" A row "
                    + "fixes x and a column fixes y. In both clauses g ranges over every "
                    + "natural number, including zero; the exclamation mark denotes "
                    + "existence of exactly one coordinate."),
            Node("splythoff-row-bound", "A finite bound for each row occurrence",
                "row_exists_bound", RowBoundFormula(), DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source),
                "For fixed x and g, a column carrying g occurs by 5x+2g+3. Equal-valued "
                    + "unordered pairs share no coordinate unless they are the same pair. "
                    + "There is at most one equal-coordinate pair of value g. Consequently "
                    + "the distinct sums of value-g split targets up to M number at most "
                    + "floor((M+2)/2). Ordinary vertical and double obstructions number "
                    + "at most 2x, and values below g occupy at most g columns. A window "
                    + "of length M=2g+4x+3 cannot be covered by these three bounds."),
            Node("splythoff-result", "Every value occurs exactly once", "result",
                Disp(F.Id("claim")), DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source),
                "The finite row bound supplies existence. Single moves between distinct "
                    + "positions of one row force different Grundy values, supplying "
                    + "uniqueness. Swapping the two pile sizes preserves all legal moves "
                    + "and their Grundy values, so the same conclusion holds for columns. "
                    + "The separate question about reflected diagonals remains open.",
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("fokkink-rust-2024-splythoff-grundy-rows"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string id, string title, string name, Formula formula,
        DescribeRole role, AssessedProvenance provenance, string prose,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula NatType => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula PairType => Seq(NatType, Sp, Times, Sp, NatType);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(F.Id(owner)), Dot, Operatorname, Grp(F.Id(name)));
    private static Formula App(Formula function, params Formula[] arguments) =>
        Seq(function, Parenthesized(Join(arguments)));
    private static Formula Join(Formula[] arguments) => arguments.Length == 1 ? arguments[0]
        : Seq(arguments[0], Comma, Sp, Join(arguments[1..]));
    private static Formula Pair(Formula x, Formula y) => Parenthesized(Seq(x, Comma, Sp, y));
    private static Formula Fst(Formula p) => Seq(p, Dot, D(1));
    private static Formula Snd(Formula p) => Seq(p, Dot, D(2));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Parenthesized(Seq(F.Id(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula Unique(string name, Formula body) =>
        Seq(Exists, Bang, Sp, Parenthesized(Seq(F.Id(name), Colon, Sp, NatType)), Comma, Sp, body);
    private static Formula Lam(string name, Formula type, Formula body) =>
        Parenthesized(Seq(Operatorname, Grp(F.Id("fun")), Sp,
            Parenthesized(Seq(F.Id(name), Colon, Sp, type)), Sp, Mapsto, Sp, body));
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Or(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Or, Parenthesized(b));
    private static Formula Iff(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Member(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);

    private static Formula MoveFormula()
    {
        var p = F.Id("p"); var q = F.Id("q"); var k = F.Id("k");
        var minimum = Call("min", Fst(p), Snd(p));
        return Disp(All("p", PairType, All("q", PairType,
            Iff(Call("splythoffMove", p, q),
                Or(And(Lt(Fst(q), Fst(p)), Equal(Snd(q), Snd(p))),
                    Or(And(Equal(Fst(q), Fst(p)), Lt(Snd(q), Snd(p))),
                        Or(Ex("k", NatType, And(Le(D(1), k),
                            And(Le(k, minimum), Equal(q,
                                Pair(Subtract(Fst(p), k), Subtract(Snd(p), k)))))),
                            And(Le(D(1), minimum),
                                Equal(Add(Fst(q), Snd(q)),
                                    Subtract(Call("max", Fst(p), Snd(p)), minimum))))))))));
    }

    private static Formula FollowersFormula()
    {
        var p = F.Id("p");
        var range = App(Qualified("Finset", "range"), Add(Call("max", Fst(p), Snd(p)), D(1)));
        var rectangle = App(Qualified("Finset", "product"), range, range);
        return Disp(All("p", PairType, Equal(Call("followers", p),
            App(Qualified("Finset", "filter"), Call("splythoffMove", p), rectangle))));
    }

    private static Formula GrundyFormula()
    {
        var x = F.Id("x"); var y = F.Id("y"); var q = F.Id("q"); var z = F.Id("z");
        var followers = Call("followers", Pair(x, y));
        var subtype = Seq(OpenBrace, z, Colon, Sp, PairType, Sp, Mid, Sp,
            Member(z, followers), CloseBrace);
        var val = Call("val", q);
        var attached = App(Qualified("Finset", "attach"), followers);
        var list = App(Qualified("Finset", "toList"), attached);
        var values = App(Qualified("List", "map"),
            Lam("q", subtype, Call("grundy", Fst(val), Snd(val))), list);
        return Disp(All("x", NatType, All("y", NatType,
            Equal(Call("grundy", x, y), Call("mex", App(Qualified("List", "toFinset"), values))))));
    }

    private static Formula ClaimFormula()
    {
        var x = F.Id("x"); var y = F.Id("y"); var g = F.Id("g");
        var rows = All("x", NatType, All("g", NatType,
            Unique("y", Equal(Call("grundy", x, y), g))));
        var columns = All("y", NatType, All("g", NatType,
            Unique("x", Equal(Call("grundy", x, y), g))));
        return Disp(Iff(F.Id("claim"), And(rows, columns)));
    }

    private static Formula RowBoundFormula()
    {
        var x = F.Id("x"); var g = F.Id("g"); var y = F.Id("y");
        return Disp(All("x", NatType, All("g", NatType, Ex("y", NatType,
            And(Equal(Call("grundy", x, y), g),
                Le(y, Add(Add(Multiply(D(5), x), Multiply(D(2), g)), D(3))))))));
    }
}
