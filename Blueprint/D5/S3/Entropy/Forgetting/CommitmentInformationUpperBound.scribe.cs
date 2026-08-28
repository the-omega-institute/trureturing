using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy.Forgetting;

internal sealed class CommitmentInformationUpperBoundDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Entropy/Forgetting/CommitmentInformationUpperBound."
            + "commitment_information_le_residual_entropy";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Conditional commitment information is bounded by commitment entropy given environment.",
        H("Commitment Information Upper Bound"),
        Blocks(Describe.Lean(
            DescribeId.Create("commitment-information-is-bounded-by-residual-entropy"),
            DeclarationHandle.Create(Declaration),
            H("The commitment channel is bounded by conditional commitment entropy"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "A normalized nonnegative mass on a finite sample carrier constructs "
                        + "the environment, current commitment, and future behavior through "
                        + "their canonical joint pushforward law.")),
                Paragraph(Text(
                    "Enriching the future record with the commitment makes recovery exact, "
                        + "so the frozen saturation theorem identifies its information with "
                        + "the commitment entropy remaining after the environment readout.")),
                Paragraph(Text(
                    "Forgetting the added commitment coordinate recovers the actual future "
                        + "record. The frozen deterministic-forgetting theorem then gives "
                        + "the displayed upper bound."))),
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
        Formula type = F.Id("Type");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula sample = F.Id("X");
        Formula environmentCarrier = F.Id("E");
        Formula commitmentCarrier = F.Id("C");
        Formula futureCarrier = F.Id("B");
        Formula mass = Mu;
        Formula x = F.Id("x");
        Formula environment = F.Id("e");
        Formula commitment = F.Id("c");
        Formula future = F.Id("b");
        Formula jointReadout = Seq(x, Sp, Mapsto, Sp,
            Pair(Apply(environment, x),
                Pair(Apply(commitment, x), Apply(future, x))));
        Formula nonnegative = Seq(
            Forall, Sp, x, InMacro, Sp, sample, Comma, Sp,
            D(0), Sp, Leq, Sp, Apply(mass, x));
        Formula normalized = Seq(
            Sum, Underscore, Grp(x, Sp, InMacro, Sp, sample), Sp,
            Apply(mass, x), Sp, Eq, Sp, D(1));
        Formula information = Call(
            "conditionalMutualInformation",
            Call("pushforward", jointReadout, mass));
        Formula residual = Call(
            "targetResidualEntropy", mass, environment, commitment);

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
            Typed(mass, Arrow(sample, real)), Comma, Sp,
            Typed(environment, Arrow(sample, environmentCarrier)), Comma,
            RowBreak, Grp(),
            Typed(commitment, Arrow(sample, commitmentCarrier)), Comma, Sp,
            Typed(future, Arrow(sample, futureCarrier)), Comma,
            RowBreak, Grp(),
            Open, Open, nonnegative, Close, Sp, Land, Sp, normalized, Close,
            Sp, Rightarrow,
            RowBreak, Grp(),
            information, Sp, Leq, Sp, residual, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
