using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy.Forgetting;

internal sealed class CommitmentInformationSaturationDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Entropy/Forgetting/CommitmentInformationSaturation."
            + "commitment_information_saturation";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete future recovery saturates the conditional commitment-information bound.",
        H("Commitment Information Saturation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("complete-recovery-saturates-commitment-information"),
                DeclarationHandle.Create(Declaration),
                H("Complete recovery saturates commitment information"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A nonnegative finite sample mass constructs the environment, current "
                            + "commitment, and future behavior records through their joint "
                            + "pushforward law.")),
                    Paragraph(Text(
                        "When the commitment has zero conditional entropy after observing the "
                            + "paired environment-future record, its conditional mutual "
                            + "information with the future equals its entropy given only the "
                            + "environment."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Arrow(Formula source, Formula target) =>
        new Formula.TypeArrow(source, target);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Pair(Formula left, Formula right) =>
        Seq(Open, left, Comma, Sp, right, Close);

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Fintype(Formula carrier) =>
        Seq(OpenBracket, Operatorname, Grp(F.Id("Fintype")),
            Open, carrier, Close, CloseBracket);

    private static Formula TheoremFormula()
    {
        Formula type = F.Id("Type"), real = Seq(Mathbb, Grp(F.Id("R")));
        Formula sample = F.Id("X"), environmentCarrier = F.Id("E");
        Formula commitmentCarrier = F.Id("C"), futureCarrier = F.Id("B");
        Formula mu = Mu, x = F.Id("x"), environment = F.Id("e");
        Formula commitment = F.Id("c"), future = F.Id("b");
        Formula futureReadout = Seq(x, Sp, Mapsto, Sp,
            Pair(Apply(environment, x), Apply(future, x)));
        Formula jointReadout = Seq(x, Sp, Mapsto, Sp,
            Pair(Apply(environment, x),
                Pair(Apply(commitment, x), Apply(future, x))));
        Formula nonnegative = Seq(
            Forall, Sp, x, InMacro, Sp, sample, Comma, Sp,
            D(0), Sp, Leq, Sp, Apply(mu, x));
        Formula recovery = Seq(
            Call("targetResidualEntropy", mu, futureReadout, commitment),
            Sp, Eq, Sp, D(0));
        Formula conclusion = Seq(
            Call("conditionalMutualInformation",
                Call("pushforward", jointReadout, mu)),
            Sp, Eq, Sp,
            Call("targetResidualEntropy", mu, environment, commitment));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp,
            Typed(sample, type), Comma, Sp,
            Typed(environmentCarrier, type), Comma, Sp,
            Typed(commitmentCarrier, type), Comma, Sp,
            Typed(futureCarrier, type), Comma,
            RowBreak, Grp(),
            Fintype(sample), Comma, Sp, Fintype(environmentCarrier), Comma, Sp,
            Fintype(commitmentCarrier), Comma, Sp, Fintype(futureCarrier), Comma,
            RowBreak, Grp(),
            Typed(mu, Arrow(sample, real)), Comma, Sp,
            Typed(environment, Arrow(sample, environmentCarrier)), Comma,
            RowBreak, Grp(),
            Typed(commitment, Arrow(sample, commitmentCarrier)), Comma, Sp,
            Typed(future, Arrow(sample, futureCarrier)), Comma,
            RowBreak, Grp(),
            Open, Open, nonnegative, Close, Sp, Land, Sp, recovery, Close,
            Sp, Rightarrow,
            RowBreak, Grp(),
            conclusion, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
