using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates;

internal sealed class StephanFloorSqrtRecurrenceRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S0/Certificates/StephanFloorSqrtRecurrenceRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/seidov2005a104863");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The term at n = 17 refutes the conjectured recurrence for OEIS A104863.",
        H("The OEIS A104863 Floor-Square-Root Recurrence Conjecture"),
        Blocks(
            Describe.Lean(DescribeId.Create("a104863-sequence"),
                DeclarationHandle.Create(Prefix + "a"),
                H("The A104863 sequence"),
                StatementSource.FromAuthor(SequenceFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The displayed equations give a(1) = 10, a(2) = 30, and the recursive "
                        + "value at n+3 for every natural n. Nat.sqrt is the greatest natural "
                        + "number whose square does not exceed its argument. Lean makes the "
                        + "recursive definition total with the sentinel value a(0) = 0."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("a104863-recurrence-conjecture"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("Stephan's recurrence conjecture"),
                StatementSource.FromAuthor(ClaimFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For every natural n at least 17, the conjecture equates a(n) with "
                        + "a(n-2) + a(n-4) + 1. Both subtractions are truncated natural "
                        + "subtractions, as in the Lean definition."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("a104863-recurrence-conjecture-refuted"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The conjecture fails at n = 17"),
                StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "At n = 17, the defining recurrence gives a(17) = 935, whereas "
                        + "a(15) + a(13) + 1 = 578 + 358 + 1 = 937, so the claim is false. "
                        + "The sign-corrected reading also fails numerically at n = 33, and "
                        + "the odd and even closed forms fail at m = 16 and m = 19, "
                        + "respectively, as detailed in the dossier."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create(
                        "oeis-a104863-floor-sqrt-recurrence-refutation"),
                    ResolutionKind.Refuted)))));

    private static Formula SequenceFormula()
    {
        var n = F.Id("n");
        var recurrence = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("n"),
            Naturals(),
            Equal(
                Call("a", Add(n, D(3))),
                QualifiedCall("Nat", "sqrt", Add(
                    Square(Call("a", Add(n, D(2)))),
                    Square(Call("a", Add(n, D(1))))))));
        return Disp(And(
            Equal(Call("a", D(1)), D(1, 0)),
            Equal(Call("a", D(2)), D(3, 0)),
            recurrence));
    }

    private static Formula ClaimFormula()
    {
        var n = F.Id("n");
        var premise = new Formula.Relation(
            D(1, 7), FormulaRelationOperator.LessThanOrEqual, n);
        var conclusion = Equal(
            Call("a", n),
            Add(Add(Call("a", Subtract(n, D(2))), Call("a", Subtract(n, D(4)))), D(1)));
        var quantified = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("n"),
            Naturals(),
            new Formula.Logic(premise, FormulaLogicOperator.Implies, conclusion));
        return Disp(new Formula.Logic(
            Parenthesized(F.Id("claim")),
            FormulaLogicOperator.Iff,
            Parenthesized(quantified)));
    }

    private static Formula ResultFormula() =>
        Disp(new Formula.Not(F.Id("claim")));

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Square(Formula value) =>
        new Formula.Power(Parenthesized(value), D(2));

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula QualifiedCall(
        string prefix,
        string name,
        params Formula[] arguments) =>
        new Formula.Apply(Seq(F.Id(prefix), Dot, F.Id(name)), [.. arguments]);

    private static Formula And(params Formula[] clauses)
    {
        Formula result = Parenthesized(clauses[^1]);
        for (int i = clauses.Length - 2; i >= 0; i--)
            result = new Formula.Logic(
                Parenthesized(clauses[i]), FormulaLogicOperator.And, result);
        return result;
    }

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Naturals() =>
        new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}
