using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Residue;

internal sealed class QuetRationalIterationDenominatorDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S1/Recurrence/Residue/QuetRationalIterationDenominator.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Recurrence/quet2003a079278");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The reduced denominators of Quet's rational iteration satisfy his recurrence.",
        H("Quet's Rational Iteration Denominator Recurrence"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("a079278-num"),
                DeclarationHandle.Create(Prefix + "num"),
                H("Pair-recurrence numerator"),
                StatementSource.FromAuthor(NumFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The auxiliary numerator starts with num(0)=0 and num(1)=1. "
                        + "Each later value is the preceding numerator multiplied by "
                        + "that numerator plus twice the preceding denominator."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("a079278-den"),
                DeclarationHandle.Create(Prefix + "den"),
                H("Pair-recurrence denominator"),
                StatementSource.FromAuthor(DenFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The denominator starts with den(0)=den(1)=1. Each later value "
                        + "is the preceding denominator multiplied by the sum of the "
                        + "preceding numerator and denominator."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("a079278-b"),
                DeclarationHandle.Create(Prefix + "b"),
                H("Quet's rational iteration"),
                StatementSource.FromAuthor(BFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The rational sequence is extended by b(0)=0 and begins with "
                        + "b(1)=1. At every later index it adds one divided by one "
                        + "plus the reciprocal of the preceding value."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("a079278-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("Quet's denominator recurrence"),
                StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For every m at least two, the square of the reduced denominator "
                        + "of b(m-1) divides the cube of the reduced denominator of b(m), "
                        + "and the reduced denominator of b(m+1) satisfies Quet's formula. "
                        + "The divisibility clause makes the natural-number quotient exact. "
                        + "The reduced-form bridge identifies these denominators with the "
                        + "integer pair recurrence before the numerator recurrence yields "
                        + "the equation."))),
                DescribeRole.Theorem))));

    private static Formula NumFormula()
    {
        Formula n = F.Id("n");
        return Disp(new Formula.Aligned([
            FunctionType("num", Naturals()),
            Equal(Num(D(0)), D(0)),
            Equal(Num(D(1)), D(1)),
            ForAll("n", Equal(
                Num(Add(n, D(2))),
                Multiply(
                    Num(Add(n, D(1))),
                    Parenthesized(Add(
                        Num(Add(n, D(1))),
                        Multiply(D(2), Den(Add(n, D(1)))))))))
        ]));
    }

    private static Formula DenFormula()
    {
        Formula n = F.Id("n");
        Formula next = Multiply(
            Den(Add(n, D(1))),
            Parenthesized(Add(Num(Add(n, D(1))), Den(Add(n, D(1))))));
        return Disp(new Formula.Aligned([
            FunctionType("den", Naturals()),
            Equal(Den(D(0)), D(1)),
            Equal(Den(D(1)), D(1)),
            ForAll("n", Equal(Den(Add(n, D(2))), next))
        ]));
    }

    private static Formula BFormula()
    {
        Formula n = F.Id("n");
        Formula previous = B(Add(n, D(1)));
        return Disp(new Formula.Aligned([
            FunctionType("b", Rationals()),
            Equal(B(D(0)), D(0)),
            Equal(B(D(1)), D(1)),
            ForAll("n", Equal(
                B(Add(n, D(2))),
                Add(previous,
                    Divide(D(1), Parenthesized(Add(D(1), Divide(D(1), previous)))))))
        ]));
    }

    private static Formula ResultFormula()
    {
        Formula m = F.Id("m");
        Formula previous = ReducedDen(Subtract(m, D(1)));
        Formula current = ReducedDen(m);
        Formula divisibility = Divides(Power(previous, D(2)), Power(current, D(3)));
        Formula recurrence = Equal(
            ReducedDen(Add(m, D(1))),
            Subtract(
                Add(
                    Power(current, D(2)),
                    Divide(Power(current, D(3)), Power(previous, D(2)))),
                Multiply(current, Power(previous, D(2)))));
        return Disp(ForAll("m",
            Implies(LessEqual(D(2), m), And(divisibility, recurrence))));
    }

    private static Formula FunctionType(string name, Formula codomain) =>
        new Formula.Relation(
            F.Id(name), FormulaRelationOperator.MemberOf,
            new Formula.TypeArrow(Naturals(), codomain));

    private static Formula Naturals() =>
        new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));

    private static Formula Rationals() =>
        new Formula.NamedConstant(FormulaIdentifier.Create("Rat"));

    private static Formula Num(Formula index) => Call("num", index);

    private static Formula Den(Formula index) => Call("den", index);

    private static Formula B(Formula index) => Call("b", index);

    private static Formula ReducedDen(Formula index) =>
        Seq(Parenthesized(B(index)), Dot, F.Id("den"));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);

    private static Formula ForAll(string name, Formula body) =>
        new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create(name),
            Naturals(),
            body);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));

    private static Formula And(Formula first, params Formula[] rest)
    {
        Formula result = rest[^1];
        for (int i = rest.Length - 1; i >= 0; i--)
        {
            Formula left = i == 0 ? first : rest[i - 1];
            result = new Formula.Logic(
                Parenthesized(left), FormulaLogicOperator.And, Parenthesized(result));
        }
        return result;
    }

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula LessEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Divides(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Divides, right);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Divide(Formula numerator, Formula denominator) =>
        Seq(numerator, Sp, Slash, Sp, denominator);

    private static Formula Power(Formula value, Formula exponent) =>
        new Formula.Power(value, exponent);
}
