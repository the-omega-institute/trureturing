using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Budget;

internal sealed class EvenChannelGhostNoGoDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A shared positive square update preserves even positivity while it can force the "
            + "odd channel below zero.",
        H("Even-Channel Ghost No-Go"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("even-channel-update-nonnegative"),
                Handle("even_channel_update_nonnegative"),
                H("Nonnegative updates preserve the even channel"),
                StatementSource.FromAuthor(EvenUpdateStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The real square models the squared modulus of the even-channel "
                        + "coefficient. Its product with a nonnegative update is "
                        + "nonnegative, so adding it preserves a nonnegative base value."))),
                DescribeRole.Proposition),
            Describe.Lean(
                DescribeId.Create("odd-channel-update-eventually-negative"),
                Handle("odd_channel_update_eventually_negative"),
                H("A nonzero odd coefficient admits a destructive positive update"),
                StatementSource.FromAuthor(OddUpdateStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For arbitrary real initial odd value, the proof constructs the "
                        + "positive coefficient (q-minus squared plus one) divided by S "
                        + "squared. This remains positive even when the initial value is "
                        + "less than minus one."))),
                DescribeRole.Proposition),
            Describe.Lean(
                DescribeId.Create("even-channel-ghost-no-go"),
                Handle("even_channel_ghost_no_go"),
                H("Even positivity alone cannot exclude the odd ghost"),
                StatementSource.FromAuthor(MainStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "When the initial even channel is nonnegative and the odd "
                            + "coefficient is nonzero, one explicitly constructed positive "
                            + "coefficient simultaneously leaves the even update "
                            + "nonnegative and makes the odd update strictly negative.")),
                    Paragraph(Text(
                        "This is an abstract real-algebra statement: C squared and S "
                            + "squared represent the real squared moduli of the analytic "
                            + "channel coefficients. It does not formalize a general "
                            + "Krein-Bochner representation, a Hilbert-Polya realization, "
                            + "or the zeta-specific sufficiency of even Weil tests."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("odd-channel-margin-iff-nonnegative"),
                Handle("odd_channel_margin_iff_nonnegative"),
                H("The odd margin condition is exact"),
                StatementSource.FromAuthor(MarginStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The old odd value has enough margin precisely when it dominates the "
                        + "subtracted square update; this is equivalent to the updated odd "
                        + "channel remaining nonnegative."))),
                DescribeRole.Proposition),
            Describe.Lean(
                DescribeId.Create("concrete-same-coefficient-witness"),
                Handle("concrete_same_coefficient_witness"),
                H("One concrete coefficient preserves even and breaks odd"),
                StatementSource.FromAuthor(ConcreteWitnessStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At q-plus = q-minus = C = S = 1 and c = 2, the even update is "
                        + "three while the odd update is minus one."))),
                DescribeRole.Proposition),
            Describe.Lean(
                DescribeId.Create("zero-odd-coefficient-counterexample"),
                Handle("zero_odd_coefficient_counterexample"),
                H("The zero odd coefficient is a necessary exception"),
                StatementSource.FromAuthor(ZeroCoefficientStatement()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At S = 0 and c = 100, the odd update remains one. This concrete "
                        + "counterexample records why the main theorem requires S to be "
                        + "nonzero."))),
                DescribeRole.Proposition))));

    private static DeclarationHandle Handle(string declaration) =>
        DeclarationHandle.Create(
            "D5/S3/Weil/Budget/EvenChannelGhostNoGo." + declaration);

    private static Formula EvenUpdateStatement()
    {
        Formula qPlus = new Formula.Subscript(F.Id("q"), Plus);
        Formula c = F.Id("c");
        Formula coefficient = F.Id("C");

        return Disp(Seq(
            Forall, Sp, qPlus, Comma, Sp, c, Comma, Sp, coefficient,
            Sp, InMacro, Sp, RealNumbers(), Comma, Esc,
            Open, D(0), Sp, Le, Sp, qPlus, Sp, Land, Sp,
            D(0), Sp, Le, Sp, c, Close, Sp, Rightarrow, Sp,
            D(0), Sp, Le, Sp, qPlus, Sp, Plus, Sp,
            Product(c, Square(coefficient)), Dot));
    }

    private static Formula OddUpdateStatement()
    {
        Formula qMinus = new Formula.Subscript(F.Id("q"), Minus);
        Formula c = F.Id("c");
        Formula coefficient = F.Id("S");

        return Disp(Seq(
            Forall, Sp, qMinus, Comma, Sp, coefficient,
            Sp, InMacro, Sp, RealNumbers(), Comma, Esc,
            coefficient, Sp, Neq, Sp, D(0), Sp, Rightarrow, Sp,
            Exists, Sp, c, Sp, InMacro, Sp, RealNumbers(), Comma, Esc,
            D(0), Sp, Lt, Sp, c, Sp, Land, Sp,
            qMinus, Sp, Minus, Sp, Product(c, Square(coefficient)),
            Sp, Lt, Sp, D(0), Dot));
    }

    private static Formula MainStatement()
    {
        Formula qPlus = new Formula.Subscript(F.Id("q"), Plus);
        Formula qMinus = new Formula.Subscript(F.Id("q"), Minus);
        Formula c = F.Id("c");
        Formula evenCoefficient = F.Id("C");
        Formula oddCoefficient = F.Id("S");

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, qPlus, Comma, Sp, qMinus, Comma, Sp,
            evenCoefficient, Comma, Sp, oddCoefficient,
            Sp, InMacro, Sp, RealNumbers(), Comma,
            RowBreak, Grp(),
            Open, D(0), Sp, Le, Sp, qPlus, Sp, Land, Sp,
            oddCoefficient, Sp, Neq, Sp, D(0), Close,
            Sp, Rightarrow,
            RowBreak, Grp(),
            Exists, Sp, c, Sp, InMacro, Sp, RealNumbers(), Comma, Sp,
            D(0), Sp, Lt, Sp, c, Sp, Land,
            RowBreak, Grp(),
            D(0), Sp, Le, Sp, qPlus, Sp, Plus, Sp,
            Product(c, Square(evenCoefficient)), Sp, Land,
            RowBreak, Grp(),
            qMinus, Sp, Minus, Sp, Product(c, Square(oddCoefficient)),
            Sp, Lt, Sp, D(0), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula MarginStatement()
    {
        Formula qMinus = new Formula.Subscript(F.Id("q"), Minus);
        Formula c = F.Id("c");
        Formula coefficient = F.Id("S");
        Formula update = Product(c, Square(coefficient));

        return Disp(Seq(
            Forall, Sp, qMinus, Comma, Sp, c, Comma, Sp, coefficient,
            Sp, InMacro, Sp, RealNumbers(), Comma, Esc,
            update, Sp, Le, Sp, qMinus, Sp, Leftrightarrow, Sp,
            D(0), Sp, Le, Sp, qMinus, Sp, Minus, Sp, update, Dot));
    }

    private static Formula ConcreteWitnessStatement() => Disp(Seq(
        D(0), Sp, Lt, Sp, D(2), Sp, Land, Sp, D(1), Sp, Neq, Sp, D(0),
        Sp, Land, Sp, D(0), Sp, Le, Sp,
        D(1), Sp, Plus, Sp, Product(D(2), Square(D(1))),
        Sp, Land, Sp,
        D(1), Sp, Minus, Sp, Product(D(2), Square(D(1))),
        Sp, Lt, Sp, D(0), Dot));

    private static Formula ZeroCoefficientStatement() => Disp(Seq(
        D(0), Sp, Lt, Sp, D(1, 0, 0), Sp, Land, Sp,
        D(0), Sp, Le, Sp,
        D(1), Sp, Minus, Sp, Product(D(1, 0, 0), Square(D(0))), Dot));

    private static Formula RealNumbers() => Seq(Mathbb, Grp(F.Id("R")));

    private static Formula Square(Formula value) =>
        Seq(value, Caret, Grp(D(2)));

    private static Formula Product(Formula left, Formula right) =>
        Seq(left, Sp, Cdot, Sp, right);
}
