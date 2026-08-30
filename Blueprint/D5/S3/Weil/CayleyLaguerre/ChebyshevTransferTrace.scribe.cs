using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.CayleyLaguerre;

internal sealed class ChebyshevTransferTraceDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Weil/CayleyLaguerre/ChebyshevTransferTrace.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Powers of the free determinant-one transfer matrix realize Chebyshev traces.",
        H("Chebyshev Transfer Trace"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("free-transfer-matrix"),
                DeclarationHandle.Create(Prefix + "freeTransferMatrix"),
                H("Free transfer matrix"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At a real spectral coordinate y, the named two-by-two matrix has "
                        + "rows (2y, -1) and (1, 0)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("chebyshev-slack"),
                DeclarationHandle.Create(Prefix + "chebyshevSlack"),
                H("Chebyshev slack"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At degree N and coordinate y, the named slack is one minus the square "
                        + "of the first-kind Chebyshev value."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("free-transfer-matrix-invariants"),
                DeclarationHandle.Create(Prefix + "free_transfer_matrix_invariants"),
                H("Determinant and half-trace invariants"),
                StatementSource.FromAuthor(InvariantsFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Direct evaluation of the two-by-two determinant and trace gives "
                        + "determinant one and half-trace y."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("chebyshev-transfer-trace"),
                DeclarationHandle.Create(Prefix + "chebyshev_transfer_trace"),
                H("Transfer powers realize Chebyshev values"),
                StatementSource.FromAuthor(TraceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every natural degree, half the trace of the corresponding "
                            + "matrix power is the first-kind Chebyshev value.")),
                    Paragraph(Text(
                        "The proof derives the quadratic transfer recurrence and matches its "
                            + "two initial values with Mathlib's Chebyshev recurrence."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("free-transfer-power-discriminant"),
                DeclarationHandle.Create(Prefix + "free_transfer_power_discriminant"),
                H("Transfer discriminant formula"),
                StatementSource.FromAuthor(DiscriminantFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Mathlib's two-by-two characteristic-polynomial discriminant becomes "
                        + "the squared power trace minus four because every power has "
                        + "determinant one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("chebyshev-slack-transfer-discriminant"),
                DeclarationHandle.Create(
                    Prefix + "chebyshev_slack_eq_transfer_discriminant"),
                H("Slack as a transfer discriminant"),
                StatementSource.FromAuthor(SlackFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Substituting the half-trace identity rewrites Chebyshev slack as "
                        + "minus one quarter of the transfer discriminant expression."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("chebyshev-transfer-trace-degenerate-cases"),
                DeclarationHandle.Create(
                    Prefix + "chebyshev_transfer_trace_degenerate_cases"),
                H("Zero-degree and zero-coordinate audit"),
                StatementSource.FromAuthor(DegenerateFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The concrete zero-coordinate audit checks the identity power at degree "
                        + "zero, the first power at degree one, and vanishing zero-degree "
                        + "slack."))),
                DescribeRole.Theorem))));

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Power(Formula value, Formula exponent) =>
        new Formula.Power(value, Seq(exponent));

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula ForAll(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    private static Formula MatrixPower(Formula degree, Formula coordinate) =>
        Power(Call("freeTransferMatrix", coordinate), degree);

    private static Formula PowerTrace(Formula degree, Formula coordinate) =>
        Call("tr", MatrixPower(degree, coordinate));

    private static Formula Chebyshev(Formula degree, Formula coordinate) =>
        Call("ChebyshevT", degree, coordinate);

    private static Formula HalfTrace(Formula degree, Formula coordinate) =>
        Seq(new Formula.Fraction(D(1), D(2)), Sp, Times, Sp,
            PowerTrace(degree, coordinate));

    private static Formula TransferExpression(Formula degree, Formula coordinate) =>
        Seq(Power(PowerTrace(degree, coordinate), D(2)), Sp, Minus, Sp, D(4));

    private static Formula InvariantsFormula()
    {
        Formula y = F.Id("y");
        Formula determinant = Call("det", Call("freeTransferMatrix", y));
        return Disp(ForAll(
            [Bound("y", Reals())],
            And(Equal(determinant, D(1)), Equal(HalfTrace(D(1), y), y))));
    }

    private static Formula TraceFormula()
    {
        Formula degree = F.Id("N");
        Formula y = F.Id("y");
        return Disp(ForAll(
            [Bound("N", Naturals()), Bound("y", Reals())],
            Equal(HalfTrace(degree, y), Chebyshev(degree, y))));
    }

    private static Formula DiscriminantFormula()
    {
        Formula degree = F.Id("N");
        Formula y = F.Id("y");
        Formula discriminant = Call("discr", MatrixPower(degree, y));
        return Disp(ForAll(
            [Bound("N", Naturals()), Bound("y", Reals())],
            Equal(discriminant, TransferExpression(degree, y))));
    }

    private static Formula SlackFormula()
    {
        Formula degree = F.Id("N");
        Formula y = F.Id("y");
        Formula scaledDiscriminant = Seq(
            Minus, new Formula.Fraction(D(1), D(4)), Sp, Times, Sp,
            Open, TransferExpression(degree, y), Close);
        return Disp(ForAll(
            [Bound("N", Naturals()), Bound("y", Reals())],
            Equal(Call("chebyshevSlack", degree, y), scaledDiscriminant)));
    }

    private static Formula DegenerateFormula()
    {
        Formula zeroTrace = Equal(HalfTrace(D(0), D(0)), Chebyshev(D(0), D(0)));
        Formula firstTrace = Equal(HalfTrace(D(1), D(0)), Chebyshev(D(1), D(0)));
        Formula zeroSlack = Equal(Call("chebyshevSlack", D(0), D(0)), D(0));
        return Disp(And(zeroTrace, And(firstTrace, zeroSlack)));
    }
}
