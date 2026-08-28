using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy.Forgetting;

internal sealed class ConditionalInformationForgettingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Deterministic forgetting of future behavior cannot increase its conditional information about the current commitment.",
        H("Conditional Information under Forgetting"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("forgetting-future-records-cannot-increase-conditional-information"),
                DeclarationHandle.Create(
                    "D5/S3/Entropy/Forgetting/ConditionalInformationForgetting."
                        + "conditional_information_forgetting"),
                H("Forgetting future records cannot increase conditional information"),
                StatementSource.FromAuthor(ForgettingFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The sample law constructs the joint environment, commitment, and future "
                            + "behavior records. A deterministic map coarsens only the future "
                            + "coordinate while leaving the environment and commitment unchanged.")),
                    Paragraph(Text(
                        "Conditional mutual information is rewritten as the commitment entropy "
                            + "remaining after the environment minus that remaining after the "
                            + "paired environment-future readout. The frozen deterministic "
                            + "postprocessing theorem makes the latter residual entropy increase, "
                            + "which proves the displayed inequality."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Arrow(Formula source, Formula target) =>
        Seq(source, Sp, To, Sp, target);

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

    private static Formula ForgettingFormula()
    {
        Formula sample = F.Id("X"), environmentCarrier = F.Id("E");
        Formula commitmentCarrier = F.Id("C"), futureCarrier = F.Id("B");
        Formula coarseCarrier = Seq(F.Id("B"), Apos);
        Formula mu = Mu, x = F.Id("x"), environment = F.Id("e");
        Formula commitment = F.Id("c"), future = F.Id("b"), forget = F.Id("g");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula probabilityLaw = Seq(
            Open, Forall, Sp, x, InMacro, Sp, sample, Comma, Sp,
            D(0), Sp, Leq, Sp, Apply(mu, x), Close,
            Sp, Land, Sp, Sum, Underscore, Grp(x), Sp,
            Apply(mu, x), Sp, Eq, Sp, D(1));
        Formula fineLaw = Call("pushforward",
            Seq(x, Sp, Mapsto, Sp,
                Open, Apply(environment, x), Comma, Sp,
                Open, Apply(commitment, x), Comma, Sp, Apply(future, x), Close, Close),
            mu);
        Formula coarseLaw = Call("pushforward",
            Seq(x, Sp, Mapsto, Sp,
                Open, Apply(environment, x), Comma, Sp,
                Open, Apply(commitment, x), Comma, Sp,
                Apply(forget, Apply(future, x)), Close, Close),
            mu);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, sample, Comma, Sp, environmentCarrier, Comma, Sp,
            commitmentCarrier, Comma, Sp, futureCarrier, Comma, Sp, coarseCarrier,
            Colon, Sp, Operatorname, Grp(F.Id("Type")), Comma, RowBreak, Grp(),
            Fintype(sample), Comma, Sp, Fintype(environmentCarrier), Comma, Sp,
            Fintype(commitmentCarrier), Comma, Sp, Fintype(futureCarrier), Comma, Sp,
            Fintype(coarseCarrier), Comma, RowBreak, Grp(),
            mu, Colon, Sp, Arrow(sample, real), Comma, Sp, probabilityLaw, Comma,
            RowBreak, Grp(),
            environment, Colon, Sp, Arrow(sample, environmentCarrier), Comma, Sp,
            commitment, Colon, Sp, Arrow(sample, commitmentCarrier), Comma, RowBreak, Grp(),
            future, Colon, Sp, Arrow(sample, futureCarrier), Comma, Sp,
            forget, Colon, Sp, Arrow(futureCarrier, coarseCarrier), Comma, RowBreak, Grp(),
            Call("conditionalMutualInformation", coarseLaw), Sp, Leq, Sp,
            Call("conditionalMutualInformation", fineLaw), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
