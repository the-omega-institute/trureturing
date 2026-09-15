using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit;

internal sealed class YanevBinaryReversalPositionIdentityDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S1/Digit/YanevBinaryReversalPositionIdentity.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Digit/yanev2017a030101");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Binary reversal is determined by the lexicographic position recurrence after removing the leading bit.",
        H("Yanev's Binary-Reversal Position Identity"),
        Blocks(
            Paragraph(Text("All variables and values lie in the natural numbers. A Boolean bit b "
                + "and a half-index m represent Nat.bit b m, equal to 2m when b is false and "
                + "2m+1 when b is true. The operator binaryRec is Nat.binaryRec. The operator "
                + "log_2(m) is Nat.log 2 m: for positive m it is the floor of the base-two "
                + "logarithm, and Mathlib totalizes it at zero. Powers, addition, and "
                + "multiplication are natural-number operations. Subtraction is truncated "
                + "natural subtraction, so stripTop(0)=0.")),
            Node("w", "The A264596 lexicographic position", WFormula(),
                "The defining binary recursion starts at zero. An even low bit preserves the "
                + "previous value; an odd low bit adds the half-index and one. This is Heinz's "
                + "recurrence for A264596.", DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node("stripTop", "Remove the leading binary bit", StripTopFormula(),
                "For a positive input, 2 raised to log_2(n) is its largest binary power. "
                + "Natural subtraction removes that leading power, matching A053645. The "
                + "definition is totalized at zero.", DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node("rev", "Reverse the binary digits", RevFormula(),
                "The defining binary recursion uses Stephan's recurrence for A030101. The first "
                + "odd value is one; subsequent odd steps add the next leading binary power, "
                + "while even steps preserve the previous value.", DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node("result", "Yanev's position identity", ResultFormula(),
                "For every positive natural n, moving both subtracted terms to the additive side "
                + "gives a truncation-free form of Yanev's conjecture. Binary induction tracks "
                + "stripTop through even and odd inputs and closes both branches from the two "
                + "source recurrences.", DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? claim = null) => Describe.Lean(
        DescribeId.Create("a030101-" + name.Replace("T", "-t").ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula WFormula()
    {
        Formula b = F.Id("b");
        Formula m = F.Id("m");
        Formula previous = F.Id("p");
        Formula step = Seq(
            Parenthesized(Seq(b, Comma, Sp, m, Comma, Sp, previous)),
            Sp, Mapsto, Sp,
            Call("if", b, Add(Add(previous, m), D(1)), previous));
        return Disp(Equal(F.Id("w"), Call("binaryRec", D(0), step)));
    }

    private static Formula StripTopFormula()
    {
        Formula n = F.Id("n");
        Formula power = new Formula.Power(D(2), Log(n));
        return Disp(Universal("n", Equal(Call("stripTop", n), Subtract(n, power))));
    }

    private static Formula RevFormula()
    {
        Formula b = F.Id("b");
        Formula m = F.Id("m");
        Formula previous = F.Id("p");
        Formula oddStep = Call("if", Equal(m, D(0)), D(1),
            Add(previous, new Formula.Power(D(2), Parenthesized(Add(Log(m), D(1))))));
        Formula step = Seq(
            Parenthesized(Seq(b, Comma, Sp, m, Comma, Sp, previous)),
            Sp, Mapsto, Sp, Call("if", b, oddStep, previous));
        return Disp(Equal(F.Id("rev"), Call("binaryRec", D(0), step)));
    }

    private static Formula ResultFormula()
    {
        Formula n = F.Id("n");
        Formula hypothesis = LessOrEqual(D(1), n);
        Formula left = Add(Add(Call("rev", n),
            Multiply(D(2), Call("w", Call("stripTop", n)))), D(1));
        Formula right = Multiply(D(2), Call("w", n));
        return Disp(Universal("n", new Formula.Logic(
            Parenthesized(hypothesis), FormulaLogicOperator.Implies,
            Parenthesized(Equal(left, right)))));
    }

    private static Formula Naturals() => F.Id("Nat");
    private static Formula Log(Formula value) =>
        new Formula.Apply(new Formula.Subscript(F.Id("log"), D(2)), [value]);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Universal(string variable, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll,
            FormulaIdentifier.Create(variable), Naturals(), body);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula LessOrEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
}
