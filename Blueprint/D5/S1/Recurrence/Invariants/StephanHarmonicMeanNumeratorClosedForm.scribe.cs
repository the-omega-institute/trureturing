using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Invariants;

internal sealed class StephanHarmonicMeanNumeratorClosedFormDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S1/Recurrence/Invariants/StephanHarmonicMeanNumeratorClosedForm.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Recurrence/stephan2010a107928");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Stephan's three-residue closed form for the harmonic-mean-numerator recurrence.",
        H("The Closed Form of the Harmonic-Mean-Numerator Recurrence"),
        Blocks(
            Node("a", "The harmonic-mean-numerator recurrence", RecurrenceFormula(),
                "a(0) = 0 is the offset-1 sentinel; the harmonic mean is taken in the "
                + "rationals and Rat.num is its reduced numerator. The displayed toNat "
                + "converts that integer numerator to a natural number.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("stephan_a107928", "Stephan's three-residue closed form", TheoremFormula(),
                "Block induction propagates the pair (a(3m+1), a(3m+2)) = "
                + "(3*8^m, 2*8^m). The coprime reductions and the block invariant are "
                + "carried inside the proof. The exponent m-1 uses natural-number "
                + "subtraction.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create(
                        "oeis-a107928-harmonic-mean-numerator-closed-form"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? claim = null) => Describe.Lean(
        DescribeId.Create("a107928-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula RecurrenceFormula()
    {
        var n = F.Id("n");
        var initialZero = Equal(Call("a", D(0)), D(0));
        var initialOne = Equal(Call("a", D(1)), D(2));
        var initialTwo = Equal(Call("a", D(2)), D(3));
        var previous = Call("a", Add(n, D(1)));
        var current = Call("a", Add(n, D(2)));
        var harmonicMean = new Formula.Fraction(
            Multiply(Multiply(D(2), current), previous),
            Add(previous, current));
        var recurrence = Universal("n", Equal(
            Call("a", Add(n, D(3))),
            Call("toNat", Call("num", harmonicMean))));
        return Disp(And(initialZero, Parenthesized(And(
            initialOne, Parenthesized(And(initialTwo, recurrence))))));
    }

    private static Formula TheoremFormula()
    {
        var m = F.Id("m");
        var first = Equal(
            Call("a", Multiply(D(3), m)),
            Multiply(D(1, 2), Power(D(8), Subtract(m, D(1)))));
        var second = Equal(
            Call("a", Add(Multiply(D(3), m), D(1))),
            Multiply(D(3), Power(D(8), m)));
        var third = Equal(
            Call("a", Add(Multiply(D(3), m), D(2))),
            Multiply(D(2), Power(D(8), m)));
        var conclusion = And(first, Parenthesized(And(second, third)));
        return Disp(Universal("m", Implies(
            LessThanOrEqual(D(1), m), Parenthesized(conclusion))));
    }

    private static Formula Naturals() =>
        new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula Universal(string variable, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll,
            FormulaIdentifier.Create(variable), Naturals(), body);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula LessThanOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Power(Formula basis, Formula exponent) =>
        new Formula.Power(basis, exponent);
}
