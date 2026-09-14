using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Deficit.Beatty;

internal sealed class KimberlingRoundedHalfRootTwoDifferenceDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S1/Deficit/Beatty/KimberlingRoundedHalfRootTwoDifference.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Arith/sloane2014a049473");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Rounded multiples of one over sqrt two have binary differences at the two shifted Beatty position sequences.",
        H("Rounded Half-Root-Two Differences"),
        Blocks(
            Node("a", "Nearest integers to multiples of one over sqrt two", AFormula(),
                "For each natural n, a(n) is the nearest integer to n divided by sqrt two, "
                    + "with the rounding convention supplied by the real ordered ring.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("lower", "The lower shifted Beatty sequence", LowerFormula(),
                "For each natural k, lower(k) is the floor of (k+1/2) times sqrt two. "
                    + "These are the positions at which the rounded sequence increases by one.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("upper", "The upper shifted Beatty sequence", UpperFormula(),
                "For each natural k, upper(k) is the floor of (k+1/2) times two plus sqrt two. "
                    + "These are the positions at which the rounded sequence has zero difference.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The difference and position characterization", ResultFormula(),
                "Every adjacent difference of a is zero or one. The jump-position "
                    + "characterization identifies the unit differences exactly with lower, "
                    + "while the zero differences are exactly upper. The complementary shifted "
                    + "Beatty partition used in the position argument is the classical "
                    + "2-Wythoff complementarity.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create(
                        "oeis-a049473-kimberling-rounded-half-root-two-difference"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? claim = null) => Describe.Lean(
        DescribeId.Create("a049473-" + name.ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula AFormula()
    {
        var n = F.Id("n");
        return Disp(Universal("n", Equal(
            Call("a", n), Call("round", Divide(n, RootTwo())))));
    }

    private static Formula LowerFormula()
    {
        var k = F.Id("k");
        var shifted = Parenthesized(Add(k, Half()));
        return Disp(Universal("k", Equal(
            Call("lower", k), Floor(Multiply(shifted, RootTwo())))));
    }

    private static Formula UpperFormula()
    {
        var k = F.Id("k");
        var shifted = Parenthesized(Add(k, Half()));
        var slope = Parenthesized(Add(D(2), RootTwo()));
        return Disp(Universal("k", Equal(
            Call("upper", k), Floor(Multiply(shifted, slope)))));
    }

    private static Formula ResultFormula()
    {
        var n = F.Id("n");
        var k = F.Id("k");
        var difference = Subtract(Call("a", Add(n, D(1))), Call("a", n));
        var values = Or(Equal(difference, D(0)), Equal(difference, D(1)));
        var jumps = Iff(
            Equal(difference, D(1)),
            Exists("k", Equal(IntCast(n), Call("lower", k))));
        var zeros = Iff(
            Equal(difference, D(0)),
            Exists("k", Equal(IntCast(n), Call("upper", k))));
        return Disp(Universal("n", And(
            Parenthesized(values),
            And(Parenthesized(jumps), Parenthesized(zeros)))));
    }

    private static Formula Naturals() =>
        new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));

    private static Formula Universal(string name, Formula body) =>
        new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create(name),
            Naturals(),
            body);

    private static Formula Exists(string name, Formula body) =>
        new Formula.Bind(
            FormulaQuantifier.Exists,
            FormulaIdentifier.Create(name),
            Naturals(),
            body);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);

    private static Formula IntCast(Formula value) => Call("intCast", value);

    private static Formula RootTwo() => Seq(Sqrt, Grp(D(2)));

    private static Formula Half() => Seq(D(1), Sp, Slash, Sp, D(2));

    private static Formula Floor(Formula value) => Seq(Lfloor, value, Rfloor);

    private static Formula Divide(Formula numerator, Formula denominator) =>
        Seq(numerator, Sp, Slash, Sp, denominator);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Or(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Or, right);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
}
