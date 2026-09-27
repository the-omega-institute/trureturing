using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics;

internal sealed class BalancedCompositionPathsDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/BalancedCompositionPaths.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/wiseman2018a026010");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Nonnegative unit-step height sequences from two are as many as the compositions "
            + "whose even parts are split evenly between odd and even positions, because both "
            + "are windows of the same Pascal kernel.",
        H("Balanced Compositions Are Counted by Nonnegative Walks from Height Two"),
        Blocks(
            Node("walks-from-two", "Walks from height two", "walkCount", WalkFormula(),
                "A height sequence of length one more than the step count starts at two and "
                    + "moves by one at every step. The heights are natural numbers, so staying "
                    + "nonnegative costs nothing extra, and no height can exceed two plus the "
                    + "step count, so the sequences form a finite set and can be counted.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("balanced-compositions", "Compositions balanced across position parity",
                "balancedCompositionCount", CompositionFormula(),
                "A composition is balanced when its even parts occupy as many odd positions as "
                    + "even ones. Positions are counted from one, so the first part sits at an "
                    + "odd position; in terms of the zero-based index into the list of parts, an "
                    + "odd position is an even index. A composition with no even part is "
                    + "balanced. The worked list on the source entry fixes both readings: for "
                    + "total five the balanced compositions are five; three one one; one three "
                    + "one; one one three; two two one; one two two; and one one one one one. "
                    + "The tuple two one two is excluded, its two even parts sitting at the "
                    + "first and third positions.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("the-conjectured-identity", "The conjectured identity", "claim", ClaimFormula(),
                "The source asserts that the two counts agree once the total of the composition "
                    + "exceeds the step count by two, and reports the assertion checked as far "
                    + "as nineteen steps.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("identity-holds", "The identity holds", "result", ResultFormula(),
                "Both sides are windows of one kernel. Write the kernel on the integers whose "
                    + "value at length zero is the indicator of the origin and which sends each "
                    + "entry to the sum of its two neighbours at the previous length; it is even "
                    + "in the displacement and is Pascal's array in displacement coordinates. "
                    + "For the walks, reflect across the line one below zero: the sequences that "
                    + "touch it correspond to all sequences starting four below zero, and "
                    + "summing over the end height telescopes because the subtracted index "
                    + "exceeds the added one by exactly three, leaving three consecutive kernel "
                    + "entries. For the compositions, recursion on the first part splits three "
                    + "ways: a first part of at least three loses two and keeps every position, "
                    + "a first part of one is deleted and reverses position parity, and a first "
                    + "part of two contributes one before being deleted. Tracking the signed "
                    + "difference between even parts at odd and at even positions, the count at "
                    + "a given difference is the sum of six consecutive kernel entries centred "
                    + "at three times that difference. At difference zero evenness folds that "
                    + "window into the same three-entry expression the reflection produced, term "
                    + "by term. No generating function and no square root enter. Each side is "
                    + "then tied to its literal objects, the finite set of height sequences on "
                    + "one hand and a filter on the compositions on the other, so the statement "
                    + "counts what the source counts.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("balanced-composition-paths"),
                    ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.FromAuthor(formula),
            provenance,
            Blocks(Paragraph(Text(prose))),
            role,
            resolution);

    private static Formula Naturals() =>
        new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));

    private static Formula Card(Formula x) => Seq(Lvert, Sp, x, Sp, Rvert);

    private static Formula Apply(Formula f, Formula x) => Seq(f, Open, x, Close);

    private static Formula WalkSet(Formula n) =>
        Seq(F.Id("Walks"), Open, n, Close);

    private static Formula BalancedSet(Formula m) =>
        Seq(F.Id("Balanced"), Open, m, Close);

    private static Formula WalkFormula()
    {
        var n = F.Id("n");
        var s = F.Id("s");
        var i = F.Id("i");
        var body = And(Equal(Apply(s, D(0)), D(2)),
            Universal("i", IndexSet(n),
                Equal(Abs(Subtract(Apply(s, Seq(i, Plus, D(1))), Apply(s, i))), D(1))));
        return Disp(Equal(WalkSet(n),
            Seq(OpenBrace, s, Sp, Mid, Sp, body, CloseBrace)));
    }

    private static Formula IndexSet(Formula n) => Seq(F.Id("Fin"), Sp, n);

    private static Formula Abs(Formula x) => new Formula.Absolute(x);

    private static Formula CompositionFormula()
    {
        var m = F.Id("m");
        var c = F.Id("c");
        var lhs = Seq(F.Id("odd"), Open, c, Close);
        var rhs = Seq(F.Id("even"), Open, c, Close);
        return Disp(Equal(BalancedSet(m),
            Seq(OpenBrace, c, Sp, Mid, Sp, Equal(lhs, rhs), CloseBrace)));
    }

    private static Formula Statement()
    {
        var n = F.Id("n");
        return Universal("n", Naturals(),
            Equal(Card(WalkSet(n)), Card(BalancedSet(Add(n, D(2))))));
    }

    private static Formula ClaimFormula() => Disp(Iff(F.Id("claim"), Statement()));

    private static Formula ResultFormula() => Disp(Statement());

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Universal(string name, Formula domain, Formula body) =>
        new Formula.Bind(
            FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
}
