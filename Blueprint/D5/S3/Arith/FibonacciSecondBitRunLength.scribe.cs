using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class FibonacciSecondBitRunLengthDocument
    : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciSecondBitRunLength.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Recurrence/cicuttin2016a272170");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "No three consecutive Fibonacci numbers carry the same second most significant "
            + "binary digit.",
        H("Runs in the Second Binary Digit of the Fibonacci Numbers"),
        Blocks(
            Node("second-binary-digit", "The second binary digit", "secondBit",
                SecondBitFormula(),
                "The source takes each Fibonacci number greater than one, writes it in base "
                    + "two, and records the digit just below the leading one. Dividing by two "
                    + "raised to the number of digits less two brings that place to the bottom, "
                    + "and the remainder on division by two reads it off.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("run-length-statement", "The conjectured bound on runs", "claim",
                ClaimFormula(),
                "The comment on the sequence reads verbatim: \"It is conjectured that there are "
                    + "no more than two consecutive zeros or ones (tested up to n equals ten to "
                    + "the fifth). The sequence looks quasiperiodic and its Fourier spectrum "
                    + "seems to have a fractal structure.\" Stated over the indices, no three "
                    + "consecutive entries agree. The sequence starts at the third Fibonacci "
                    + "number, the first one with a second binary digit.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("run-length-proved", "The bound holds", "result",
                ResultFormula(),
                "Bracketing a number between two consecutive powers of two turns the digit into "
                    + "an arithmetic condition: if twice a power of two is at most the number "
                    + "and four times that power exceeds it, then the digit is one exactly when "
                    + "three times the power is at most the number, because the quotient by the "
                    + "power is then two or three. Any such bracket reads the same digit, which "
                    + "lets the argument move one and two brackets up without tracking the "
                    + "number of digits. The other ingredient is a two-sided bound on "
                    + "consecutive terms, eight times a term at most five times the next and "
                    + "eight times the next at most thirteen times the term, holding from the "
                    + "fifth index on. Its content is that the interval from eight fifths to "
                    + "thirteen eighths is carried into itself by adding one to the reciprocal, "
                    + "so each half of the bound proves the other half one step later and the "
                    + "pair is a single induction, with both ends attained at the fifth index. "
                    + "Three ones would put twice the third term below twenty-one times the "
                    + "bracket while its own bracket demands twenty-four; three zeros would put "
                    + "the third term at or above six times the bracket inside a bracket where "
                    + "that already means a one. The first two indices are checked directly. No "
                    + "logarithms, no irrationality and no equidistribution enter, although the "
                    + "wording of the source points that way.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("fibonacci-second-bit-run-length"),
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

    private static Formula Fib(Formula argument) => Call("fib", argument);

    private static Formula Bit(Formula argument) => Call("secondBit", argument);

    private static Formula SecondBitFormula()
    {
        var m = F.Id("m");
        var exponent = Subtract(Call("size", m), D(2));
        var shifted = Call("div", m, new Formula.Power(D(2), Parenthesized(exponent)));
        return Disp(Universal("m", Naturals(),
            Equal(Bit(m), Call("mod", shifted, D(2)))));
    }

    private static Formula ClaimFormula()
    {
        var n = F.Id("n");
        var body = Universal("n", Naturals(),
            Implies(LessEqual(D(3), n),
                new Formula.Not(Parenthesized(
                    And(Equal(Bit(Fib(n)), Bit(Fib(Add(n, D(1))))),
                        Equal(Bit(Fib(Add(n, D(1)))), Bit(Fib(Add(n, D(2)))))))))); 
        return Disp(Iff(F.Id("claim"), body));
    }

    private static Formula ResultFormula() => Disp(F.Id("claim"));

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Universal(string name, Formula domain, Formula body) =>
        new Formula.Bind(
            FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula LessEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
}
