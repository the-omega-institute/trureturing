using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Automata;

internal sealed class WordExcursionLowerBoundDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Factorization/Automata/WordExcursionLowerBound.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A word is at least as long as twice its excursion width minus the absolute"
        + " value of its net displacement.",
        H("An Excursion Lower Bound on Word Length"),
        Blocks(
            Paragraph(Text(
                "A word is a finite list of booleans, each letter moving an integer coordinate "
                + "up by one or down by one. The three functions below read that walk: its net "
                + "displacement, the least coordinate it reaches, and the greatest. Both "
                + "extrema include the empty prefix, so they bracket zero. All values are "
                + "integers and the length of the word is cast to an integer.")),
            Node("displacement", "Net displacement of a word", DisplacementFormula(),
                "The empty word displaces nothing. A letter contributes plus one when it is "
                + "true and minus one when it is false, and the rest of the word contributes "
                + "its own displacement.",
                DescribeRole.Definition),
            Node("low", "Least coordinate reached", LowFormula(),
                "The empty word reaches only zero. For a nonempty word the least coordinate is "
                + "the smaller of zero and the first letter's step added to the least "
                + "coordinate of the rest, so the empty prefix is included and the value is "
                + "never positive.",
                DescribeRole.Definition),
            Node("high", "Greatest coordinate reached", HighFormula(),
                "Dually, the greatest coordinate is the larger of zero and the first letter's "
                + "step added to the greatest coordinate of the rest; it is never negative.",
                DescribeRole.Definition),
            Node("word_length_lower_bound", "Length bounds the excursion", BoundFormula(),
                "Every word is at least as long as twice the width it explores, minus the "
                + "absolute value of what it finally achieves. The bound is stated for every "
                + "word, not for a chosen representative. A word that returns to its start "
                + "has zero displacement, so the bound charges it twice its full width: "
                + "reaching an extreme coordinate and coming back are both paid for. The "
                + "proof inducts on the word, and the inductive hypothesis supplies exactly "
                + "the bracketing of the displacement between the two extrema that the step "
                + "needs.",
                DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role) => Describe.Lean(
        DescribeId.Create("word-excursion-" + name.Replace('_', '-')),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);

    private static Formula Step() =>
        Seq(Open, F.Id("if"), Sp, F.Id("b"), Sp, F.Id("then"), Sp, D(1), Sp, F.Id("else"), Sp,
            Minus, D(1), Close);

    private static Formula DisplacementFormula() => Disp(Seq(
        Equal(Call1("displacement", Nil()), D(0)), Sp, Land, Sp,
        Universal("b", Booleans(), Universal("w", Words(),
            Equal(Call1("displacement", Cons()),
                Add(Step(), Call1("displacement", F.Id("w"))))))));

    private static Formula LowFormula() => Disp(Seq(
        Equal(Call1("low", Nil()), D(0)), Sp, Land, Sp,
        Universal("b", Booleans(), Universal("w", Words(),
            Equal(Call1("low", Cons()),
                Call2("min", D(0), Add(Step(), Call1("low", F.Id("w")))))))));

    private static Formula HighFormula() => Disp(Seq(
        Equal(Call1("high", Nil()), D(0)), Sp, Land, Sp,
        Universal("b", Booleans(), Universal("w", Words(),
            Equal(Call1("high", Cons()),
                Call2("max", D(0), Add(Step(), Call1("high", F.Id("w")))))))));

    private static Formula BoundFormula() => Disp(Universal("w", Words(),
        Seq(Sub(Mul(D(2), Paren(Sub(Call1("high", F.Id("w")), Call1("low", F.Id("w"))))),
                Call2("max", Call1("displacement", F.Id("w")),
                    Seq(Minus, Call1("displacement", F.Id("w"))))),
            Sp, Leq, Sp, Call1("length", F.Id("w")))));

    private static Formula Nil() => Seq(OpenBracket, CloseBracket);

    private static Formula Cons() => Seq(F.Id("b"), Sp, Colon, Colon, Sp, F.Id("w"));

    private static Formula Booleans() => F.Id("Bool");

    private static Formula Words() => Call1("List", Booleans());

    private static Formula Paren(Formula value) => Seq(Left, Open, value, Right, Close);

    private static Formula Call1(string name, Formula first) =>
        Seq(F.Id(name), Left, Open, first, Right, Close);

    private static Formula Call2(string name, Formula first, Formula second) =>
        Seq(F.Id(name), Left, Open, first, Comma, Sp, second, Right, Close);

    private static Formula Universal(string variable, Formula domain, Formula body) =>
        Seq(Forall, Sp, F.Id(variable), Sp, InMacro, Sp, domain, Comma, Sp, body);

    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);

    private static Formula Add(Formula left, Formula right) => Seq(left, Sp, Plus, Sp, right);

    private static Formula Sub(Formula left, Formula right) => Seq(left, Sp, Minus, Sp, right);

    private static Formula Mul(Formula left, Formula right) => Seq(left, Sp, Times, Sp, right);
}
