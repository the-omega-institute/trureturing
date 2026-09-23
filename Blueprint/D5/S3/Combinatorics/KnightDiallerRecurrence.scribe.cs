using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics;

internal sealed class KnightDiallerRecurrenceDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/KnightDiallerRecurrence.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/barker2019a327692");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The knight-dialler counts satisfy the conjectured fourth-order recurrence, because "
            + "the residual of that recurrence on the all-ones vector sits entirely on the one "
            + "key a knight can never leave, and one further step annihilates it.",
        H("The Knight-Dialler Recurrence"),
        Blocks(
            Node("knight-adjacency", "Knight adjacency on the keypad", "adjacency",
                AdjacencyFormula(),
                "The keypad carries the digits one to nine in three rows of three, with zero "
                    + "below the eight and the two cells beside it blank. Two digits are "
                    + "adjacent when a chess knight moves between their cells. The relation is "
                    + "symmetric and has no loop, and the out-degrees are two at every digit "
                    + "except three at four and at six, and zero at five: both knight images of "
                    + "the five are blank cells, so the five is a key a knight can never leave.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("dialable-sequences", "Dialable sequences", "dial", DialFormula(),
                "A dialable sequence of n steps assigns a digit to each of the n plus one "
                    + "positions so that consecutive digits are knight-adjacent. The digits form "
                    + "a finite type, so these sequences form a finite set and can be counted, "
                    + "with no start digit preferred. In the source entry's indexing, the count "
                    + "at n steps is the term at n plus one.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("the-conjectured-recurrence", "The conjectured recurrence", "claim",
                ClaimFormula(),
                "The source asserts a fourth-order recurrence with constant coefficients, in "
                    + "the range beyond the sixth term, and a later comment on the entry extends "
                    + "the range to the sixth term itself. The form recorded here is additive, "
                    + "because truncated subtraction on the natural numbers would silently "
                    + "weaken the assertion at exactly the small arguments where it is tightest.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("recurrence-holds", "The recurrence holds", "result", ResultFormula(),
                "Let the transfer vector at n steps carry, at each digit, the number of "
                    + "dialable sequences of n steps starting there. At zero steps it is all "
                    + "ones, and at each further step every entry becomes the sum of the entries "
                    + "at its knight neighbours. The count over all starting digits is the sum "
                    + "of its entries. The bridge from the cardinality to that recursion is the "
                    + "proved part: the sequences starting at a given digit whose second digit "
                    + "is a fixed neighbour correspond, by deleting the head and by prepending "
                    + "it, to the sequences of one step fewer starting at that neighbour, and "
                    + "counting fibrewise turns the cardinality into the transfer step. The step "
                    + "is linear, so it carries the identity from one place to the next. The "
                    + "base case is an evaluation: the residual of the recurrence on the "
                    + "all-ones vector is not zero but is supported on the five alone, and one "
                    + "further step annihilates it because the five has no knight neighbour. "
                    + "That single fact also fixes the range, the identity failing one place "
                    + "earlier, where the two sides differ by exactly that residual. No "
                    + "eigenvalue, no diagonalisability and no real spectrum enter.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("knight-dialler-recurrence"),
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

    private static Formula Digits() => Seq(F.Id("Fin"), Sp, D(1, 0));

    private static Formula IndexSet(Formula n) => Seq(F.Id("Fin"), Sp, n);

    private static Formula Adjacent(Formula a, Formula b) =>
        Seq(F.Id("adjacency"), Sp, a, Sp, b);

    private static Formula AdjacencyFormula()
    {
        var i = F.Id("i");
        var j = F.Id("j");
        return Disp(Equal(Seq(F.Id("Knight"), Open, i, Close),
            Seq(OpenBrace, j, Sp, InMacro, Sp, Digits(), Sp, Mid, Sp,
                Adjacent(i, j), CloseBrace)));
    }

    private static Formula DialFormula()
    {
        var n = F.Id("n");
        var s = F.Id("s");
        var i = F.Id("i");
        var body = Universal("i", IndexSet(n),
            Adjacent(Apply(s, i), Apply(s, Seq(i, Sp, Plus, Sp, D(1)))));
        return Disp(Equal(Apply(F.Id("dial"), n),
            Card(Seq(OpenBrace, s, Sp, Mid, Sp, body, CloseBrace))));
    }

    private static Formula Dial(Formula n) => Apply(F.Id("dial"), n);

    private static Formula Statement()
    {
        var n = F.Id("n");
        return Universal("n", Naturals(),
            Equal(Add(Dial(Add(n, D(5))), Multiply(D(4), Dial(Add(n, D(1))))),
                Multiply(D(6), Dial(Add(n, D(3))))));
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
}
