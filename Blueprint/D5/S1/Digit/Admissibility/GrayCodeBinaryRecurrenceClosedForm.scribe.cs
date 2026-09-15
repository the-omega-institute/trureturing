using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Digit.Admissibility;

internal sealed class GrayCodeBinaryRecurrenceClosedFormDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S1/Digit/Admissibility/GrayCodeBinaryRecurrenceClosedForm.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Digit/yanev2016a163617");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Yanev's Gray-code formula for the nonnegative half of the binary recurrence.",
        H("A Gray-Code Closed Form for a Binary Recurrence"),
        Blocks(
            Paragraph(Text(
                "The recurrence is considered on the natural numbers with initial value zero. "
                + "The integer-indexed negative half is the separate sequence A163618 and is "
                + "not asserted here.")),
            Paragraph(Text(
                "The correction is integral in each parity branch. Over the integers it equals "
                + "(6n + 1 - (-1)^n)/4, and the Gray-code term is OEIS A003188. The function "
                + "div denotes natural-number integer division.")),
            Node("a", "The binary recurrence", RecurrenceFormula(),
                "At an even index the previous value is doubled. At an odd index it is doubled "
                + "and increased by three when the half-index is even, or by one when the "
                + "half-index is odd.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("gray", "Binary reflected Gray code", GrayFormula(),
                "The binary reflected Gray code is the binary exclusive OR of n and its "
                + "integer half.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("corr", "The parity correction", CorrectionFormula(),
                "The even branch is floor(3n/2), and the odd branch is floor((3n+1)/2). "
                + "These branches equal (6n + 1 - (-1)^n)/4 over the integers.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("yanev_a163617", "Yanev's formula", ClosedFormFormula(),
                "Binary induction carries the equality through both recurrence branches. "
                + "The Gray-code shifts follow by separating the low bit, while the correction "
                + "supplies the matching parity increment.",
                DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create(
                        "oeis-a163617-gray-code-binary-recurrence-closed-form"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? claim = null) => Describe.Lean(
        DescribeId.Create("a163617-" + name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        provenance, Blocks(Paragraph(Text(prose))), role, claim);

    private static Formula RecurrenceFormula()
    {
        var m = F.Id("m");
        var initial = Equal(Call("a", D(0)), D(0));
        var even = Universal("m", Equal(
            Call("a", Multiply(D(2), m)),
            Multiply(D(2), Call("a", m))));
        var odd = Universal("m", Equal(
            Call("a", Add(Multiply(D(2), m), D(1))),
            Add(Multiply(D(2), Call("a", m)),
                Call("if", Call("Even", m), D(3), D(1)))));
        return Disp(And(initial, Parenthesized(And(even, odd))));
    }

    private static Formula GrayFormula()
    {
        var n = F.Id("n");
        return Disp(Universal("n", Equal(
            Call("gray", n),
            Call("xor", n, Call("div", n, D(2))))));
    }

    private static Formula CorrectionFormula()
    {
        var n = F.Id("n");
        var evenBranch = Call("div", Multiply(D(3), n), D(2));
        var oddBranch = Call("div", Add(Multiply(D(3), n), D(1)), D(2));
        return Disp(Universal("n", Equal(
            Call("corr", n), Call("if", Call("Even", n), evenBranch, oddBranch))));
    }

    private static Formula ClosedFormFormula()
    {
        var n = F.Id("n");
        return Disp(Universal("n", Equal(
            Call("a", n), Add(Call("gray", n), Call("corr", n)))));
    }

    private static Formula Naturals() => F.Id("Nat");
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Universal(string variable, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll,
            FormulaIdentifier.Create(variable), Naturals(), body);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
}
