using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics;

internal sealed class StrictSeparationImpossibilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Common outcome utilities and homogeneous report costs forbid opposite strict preferences.",
        H("Strict Separation Impossibility"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("strict-separation-impossibility"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/StrictSeparationImpossibility."
                        + "strict_separation_impossible"),
                H("Common utilities forbid opposite strict report preferences"),
                StatementSource.FromAuthor(ImpossibilityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A mechanism is represented by its result map from reports to outcomes. "
                            + "Both types evaluate every outcome with the same utility, and the "
                            + "report-cost function is independent of type.")),
                    Paragraph(Text(
                        "The public conclusion rules out the conjunction in which the first type "
                            + "strictly prefers its report and the second type strictly prefers "
                            + "the other report. Transferring the first inequality across the "
                            + "common utility equality contradicts the second.")),
                    Paragraph(Text(
                        "Repository and pinned-library searches found no exact mechanism theorem. "
                            + "The proof applies equality rewriting and the asymmetry of strict order."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        Seq(domain, Sp, To, Sp, codomain);

    private static Formula ImpossibilityFormula()
    {
        Formula type = F.Id("Theta");
        Formula report = F.Id("R");
        Formula outcome = F.Id("O");
        Formula theta = F.Id("theta");
        Formula thetaPrime = Subscript(F.Id("theta"), F.Id("prime"));
        Formula reportTheta = Subscript(F.Id("r"), theta);
        Formula reportThetaPrime = Subscript(F.Id("r"), thetaPrime);
        Formula mechanismResult = F.Id("M");
        Formula utility = F.Id("u");
        Formula reportCost = F.Id("c");
        Formula outcomeValue = F.Id("o");
        Formula resultAtTheta = Apply(mechanismResult, reportTheta);
        Formula resultAtThetaPrime = Apply(mechanismResult, reportThetaPrime);
        Formula firstScore = Seq(
            Apply(utility, Seq(theta, Comma, Sp, resultAtTheta)), Sp, Minus, Sp,
            Apply(reportCost, reportTheta));
        Formula firstAlternative = Seq(
            Apply(utility, Seq(theta, Comma, Sp, resultAtThetaPrime)), Sp, Minus, Sp,
            Apply(reportCost, reportThetaPrime));
        Formula secondScore = Seq(
            Apply(utility, Seq(thetaPrime, Comma, Sp, resultAtThetaPrime)), Sp, Minus, Sp,
            Apply(reportCost, reportThetaPrime));
        Formula secondAlternative = Seq(
            Apply(utility, Seq(thetaPrime, Comma, Sp, resultAtTheta)), Sp, Minus, Sp,
            Apply(reportCost, reportTheta));
        Formula sameUtility = Seq(
            Forall, Sp, outcomeValue, Colon, Sp, outcome, Comma, Sp,
            Apply(utility, Seq(theta, Comma, Sp, outcomeValue)), Sp, Eq, Sp,
            Apply(utility, Seq(thetaPrime, Comma, Sp, outcomeValue)));
        Formula oppositePreferences = Seq(
            Open, firstScore, Sp, Gt, Sp, firstAlternative, Close, Sp, Land, Sp,
            Open, secondScore, Sp, Gt, Sp, secondAlternative, Close);

        return Disp(Seq(
            Forall, Sp, type, Comma, Sp, report, Comma, Sp, outcome,
            Colon, Sp, Operatorname, Grp(F.Id("Type")), Comma, Sp,
            theta, Comma, Sp, thetaPrime, Colon, Sp, type, Comma, Sp,
            reportTheta, Comma, Sp, reportThetaPrime, Colon, Sp, report, Comma, Sp,
            mechanismResult, Colon, Sp, Arrow(report, outcome), Comma, Sp,
            utility, Colon, Sp, Arrow(type, Arrow(outcome, F.Id("Real"))), Comma, Sp,
            reportCost, Colon, Sp, Arrow(report, F.Id("Real")), Comma, Esc,
            sameUtility, Sp, Rightarrow, Sp, Neg, Sp,
            Open, oppositePreferences, Close, Dot));
    }

    private static Formula Subscript(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));
}
