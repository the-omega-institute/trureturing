using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Additive;

internal sealed class GreathouseA359506XorBoundDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Additive/GreathouseA359506XorBound.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithUnits/greathouse2023a359506");
    private const string Sequence =
        "OEIS A359506, revision 41, NAME (unpaginated): “a(n) is the least integer m such that there exists a strictly increasing integer sequence n = b_1 < b_2 < ... < b_t = m with the property that b_1 XOR b_2 XOR ... XOR b_t = 0.” ";
    private const string Bound =
        "OEIS A359506, revision 41, FORMULA (unpaginated): “For n > 1, a(n) >= n + 3. a(4n) = 4n + 3 for n > 0. Conjecture: a(n) <= 5(n+1)/3. - Charles R Greathouse IV, Jan 12 2023” ";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every least zero-XOR ender satisfies Greathouse's sharp five-thirds bound.",
        H("Greathouse's bound for zero-XOR enders"),
        Blocks(
            Node("HasZeroXorSequence", "Increasing zero-XOR sequences", SequenceFormula(),
                Sequence + "The carrier is the natural numbers, including zero. List.Pairwise with strict order states that every earlier entry is smaller. The list is nonempty, and List.headD and List.getLastD with default zero specify both endpoints. List.foldr of HXor.hXor, the natural bitwise XOR operation, starts at zero.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("IsLeastEnder", "The least ender predicate", IsLeastEnderFormula(),
                "IsLeastEnder combines the zero-XOR endpoint predicate with the universal comparison that every other ender is at least the selected endpoint.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The five-thirds claim", Disp(Equal(Call("claim"), Parenthesized(ClaimBody()))),
                Bound + "For every natural n, a least ender exists. Its inequality is written with integer coefficients: 3m ≤ 5(n+1). The universal comparison ranges over all possible natural enders, so minimum existence is explicit.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The five-thirds bound", Disp(ClaimBody()),
                "Write n+1 as a power of two times an odd number. An odd factor at least three gives a four-term zero-XOR sequence. A power of two gives a three-term sequence. Projecting XOR to the high binary blocks excludes every smaller ender. The singleton list containing zero handles n=0. The two resulting exact minimum formulas imply the bound; n=3·2^s−1 attains equality.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("greathouse-a359506"),
                    ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("greathouse359506-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) => App(Named(name), args);
    private static Formula App(Formula function, params Formula[] args) =>
        args.Length == 0 ? function : new Formula.Apply(function, [.. args]);
    private static Formula Qualified(string owner, string name, params Formula[] args) =>
        App(Seq(Named(owner), Dot, Named(name)), args);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id(name), Sp, Colon, Sp, type)), Comma, Sp, body);
    private static Formula AllPrime(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id(name), Apos, Sp, Colon, Sp, type)), Comma, Sp, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Parenthesized(Seq(F.Id(name), Sp, Colon, Sp, type)), Comma, Sp, body);
    private static Formula Fun(string name, Formula body) =>
        Seq(Named("fun"), Sp, Parenthesized(Seq(F.Id(name), Sp, Colon, Sp, Nat())), Sp, Mapsto, Sp, body);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula SequenceFormula()
    {
        var n = F.Id("n");
        var m = F.Id("m");
        var bs = F.Id("bs");
        var order = Fun("a", Fun("b",
            new Formula.Relation(F.Id("a"), FormulaRelationOperator.LessThan, F.Id("b"))));
        var body = And(Qualified("List", "Pairwise", order, bs),
            And(new Formula.Relation(bs, FormulaRelationOperator.NotEqual, Seq(OpenBracket, CloseBracket)),
                And(Equal(Qualified("List", "headD", bs, D(0)), n),
                    And(Equal(Qualified("List", "getLastD", bs, D(0)), m),
                        Equal(XorFold(bs), D(0))))));
        return Disp(All("n", Nat(), All("m", Nat(),
            Equal(Call("HasZeroXorSequence", n, m),
                Parenthesized(Some("bs", Call("List", Nat()), body))))));
    }

    private static Formula XorFold(Formula bs)
    {
        var xor = Fun("a", Fun("b", Qualified("HXor", "hXor", F.Id("a"), F.Id("b"))));
        return Qualified("List", "foldr", xor, D(0), bs);
    }

    private static Formula IsLeastEnderFormula()
    {
        var n = F.Id("n");
        var m = F.Id("m");
        var other = Seq(F.Id("m"), Apos);
        var least = And(Call("HasZeroXorSequence", n, m),
            AllPrime("m", Nat(), Imp(Call("HasZeroXorSequence", n, other), Le(m, other))));
        return Disp(All("n", Nat(), All("m", Nat(),
            Equal(Call("IsLeastEnder", n, m), Parenthesized(least)))));
    }

    private static Formula ClaimBody()
    {
        var n = F.Id("n");
        var m = F.Id("m");
        var minimum = Call("IsLeastEnder", n, m);
        var bound = Le(new Formula.Binary(D(3), FormulaBinaryOperator.Multiply, m),
            new Formula.Binary(D(5), FormulaBinaryOperator.Multiply,
                Parenthesized(new Formula.Binary(n, FormulaBinaryOperator.Add, D(1)))));
        return All("n", Nat(), Some("m", Nat(), And(minimum, bound)));
    }
}
