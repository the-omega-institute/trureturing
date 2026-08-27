using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Identifiability;

internal sealed class BehavioralChannelSeparationDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Identifiability/BehavioralChannelSeparation."
            + "behavioral_identification_requires_channel_difference";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Opposite strict reports require a type-dependent behavioral channel.",
        H("Behavioral Channel Separation"),
        Blocks(Describe.Lean(
            DescribeId.Create("behavioral-channel-separation"),
            DeclarationHandle.Create(Declaration),
            H("Strict behavioral separation exposes a differing channel"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "A report score is constructed from the mechanism outcome preference, "
                        + "verification effect, report cost, and external effect. Each channel "
                        + "is supplied independently on the source type and report carriers.")),
                Paragraph(Text(
                    "If the two types strictly prefer opposite reports, at least one channel "
                        + "must differ between them. Otherwise the common verification, cost, "
                        + "and external terms combine into a homogeneous report cost, and the "
                        + "frozen strict-separation impossibility theorem gives a contradiction."))),
            DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Arrow(Formula domain, Formula codomain) =>
        Seq(domain, Sp, To, Sp, codomain);

    private static Formula Score(
        Formula actor,
        Formula report,
        Formula mechanismResult,
        Formula outcomePreference,
        Formula verificationEffect,
        Formula reportCost,
        Formula externalEffect) =>
        Seq(
            Apply(outcomePreference, actor, Apply(mechanismResult, report)), Sp, Plus, Sp,
            Apply(verificationEffect, actor, report), Sp, Minus, Sp,
            Apply(reportCost, actor, report), Sp, Plus, Sp,
            Apply(externalEffect, actor, report));

    private static Formula TheoremFormula()
    {
        Formula type = F.Id("Theta");
        Formula report = F.Id("R");
        Formula outcome = F.Id("O");
        Formula theta = F.Id("theta");
        Formula thetaPrime = Seq(theta, Underscore, Grp(F.Id("prime")));
        Formula reportTheta = Seq(F.Id("r"), Underscore, Grp(theta));
        Formula reportThetaPrime = Seq(F.Id("r"), Underscore, Grp(thetaPrime));
        Formula mechanismResult = F.Id("M");
        Formula outcomePreference = F.Id("u");
        Formula verificationEffect = F.Id("v");
        Formula reportCost = F.Id("c");
        Formula externalEffect = F.Id("e");
        Formula arbitraryOutcome = F.Id("o");
        Formula arbitraryReport = F.Id("r");
        Formula types = Seq(Operatorname, Grp(F.Id("Type")));
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));

        Formula preferenceDiffers = Seq(
            Exists, Sp, arbitraryOutcome, Colon, Sp, outcome, Comma, Sp,
            Apply(outcomePreference, theta, arbitraryOutcome), Sp, Neq, Sp,
            Apply(outcomePreference, thetaPrime, arbitraryOutcome));
        Formula verificationDiffers = Seq(
            Exists, Sp, arbitraryReport, Colon, Sp, report, Comma, Sp,
            Apply(verificationEffect, theta, arbitraryReport), Sp, Neq, Sp,
            Apply(verificationEffect, thetaPrime, arbitraryReport));
        Formula costDiffers = Seq(
            Exists, Sp, arbitraryReport, Colon, Sp, report, Comma, Sp,
            Apply(reportCost, theta, arbitraryReport), Sp, Neq, Sp,
            Apply(reportCost, thetaPrime, arbitraryReport));
        Formula externalDiffers = Seq(
            Exists, Sp, arbitraryReport, Colon, Sp, report, Comma, Sp,
            Apply(externalEffect, theta, arbitraryReport), Sp, Neq, Sp,
            Apply(externalEffect, thetaPrime, arbitraryReport));

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, type, Comma, Sp, report, Comma, Sp, outcome,
                Colon, Sp, types, Comma),
            Seq(
                theta, Comma, Sp, thetaPrime, Colon, Sp, type, Comma, Sp,
                reportTheta, Comma, Sp, reportThetaPrime, Colon, Sp, report, Comma),
            Seq(
                mechanismResult, Colon, Sp, Arrow(report, outcome), Comma),
            Seq(
                outcomePreference, Colon, Sp, Arrow(type, Arrow(outcome, reals)), Comma, Sp,
                verificationEffect, Comma, Sp, reportCost, Comma, Sp, externalEffect,
                Colon, Sp, Arrow(type, Arrow(report, reals)), Comma),
            Seq(
                Open, Score(theta, reportTheta, mechanismResult, outcomePreference,
                    verificationEffect, reportCost, externalEffect),
                Sp, Gt, Sp,
                Score(theta, reportThetaPrime, mechanismResult, outcomePreference,
                    verificationEffect, reportCost, externalEffect), Sp, Land),
            Seq(
                Score(thetaPrime, reportThetaPrime, mechanismResult, outcomePreference,
                    verificationEffect, reportCost, externalEffect),
                Sp, Gt, Sp,
                Score(thetaPrime, reportTheta, mechanismResult, outcomePreference,
                    verificationEffect, reportCost, externalEffect), Close, Sp, Rightarrow),
            Seq(Open, preferenceDiffers, Close, Sp, Lor),
            Seq(Open, verificationDiffers, Close, Sp, Lor),
            Seq(Open, costDiffers, Close, Sp, Lor),
            Seq(Open, externalDiffers, Close, Dot),
        ]));
    }
}
