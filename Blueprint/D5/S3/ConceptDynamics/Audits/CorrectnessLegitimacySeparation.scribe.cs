using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Audits;

internal sealed class CorrectnessLegitimacySeparationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Equal correct results cannot determine opposite path legitimacy.",
        H("Correctness and Path Legitimacy"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("correct-result-does-not-determine-legitimacy"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Audits/CorrectnessLegitimacySeparation."
                        + "correct_result_does_not_determine_legitimacy"),
                H("A correct result does not determine path legitimacy"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Take two paths that reach the same result and satisfy the same correctness "
                            + "predicate. The first path is legitimate and the second is not.")),
                    Paragraph(Text(
                        "Any proposed predicate of results must assign the same proposition to both "
                            + "paths because their results are equal. Agreement with legitimacy on "
                            + "all correct paths would therefore both accept and reject that common "
                            + "result, which is impossible.")),
                    Paragraph(Text(
                        "The path predicates and result map are independent inputs, so legitimacy is "
                            + "not defined from the desired non-determination conclusion. The proof "
                            + "directly applies equality transport from the pinned library.")),
                    Paragraph(Text(
                        "Repository and pinned-library searches found no exact theorem combining "
                            + "equal correct results, opposite path legitimacy, and result-only "
                            + "decision failure."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula TheoremFormula()
    {
        Formula paths = F.Id("Gamma");
        Formula results = F.Id("R");
        Formula result = F.Id("r");
        Formula correct = F.Id("C");
        Formula legitimate = F.Id("L");
        Formula authorized = Subscript(F.Id("gamma"), F.Id("a"));
        Formula unauthorized = Subscript(F.Id("gamma"), F.Id("u"));
        Formula decide = F.Id("D");
        Formula path = F.Id("gamma");
        Formula authorizedResult = Apply(result, authorized);
        Formula unauthorizedResult = Apply(result, unauthorized);
        Formula premise = Seq(
            authorizedResult, Sp, Eq, Sp, unauthorizedResult, Sp, Land, Sp,
            Apply(correct, authorized), Sp, Land, Sp,
            Apply(correct, unauthorized), Sp, Land, Sp,
            Apply(legitimate, authorized), Sp, Land, Sp,
            Neg, Sp, Apply(legitimate, unauthorized));
        Formula agreement = Seq(
            Apply(correct, path), Sp, Rightarrow, Sp,
            Open, Apply(decide, Apply(result, path)), Sp, Iff, Sp,
            Apply(legitimate, path), Close);

        return Disp(Seq(
            Forall, Sp, paths, Comma, Sp, results, Comma, RowBreak, Grp(),
            result, Colon, Sp, paths, Sp, To, Sp, results, Comma, Sp,
            correct, Comma, Sp, legitimate, Colon, Sp, paths, Sp, To, Sp,
            F.Id("Prop"), Comma, RowBreak, Grp(),
            authorized, Comma, Sp, unauthorized, InMacro, Sp, paths, Comma,
            RowBreak, Grp(),
            premise, Sp, Rightarrow, RowBreak, Grp(),
            Neg, Sp, Exists, Sp, decide, Colon, Sp, results, Sp, To, Sp,
            F.Id("Prop"), Comma, Sp, Forall, Sp, path, InMacro, Sp, paths,
            Comma, Sp, agreement, Dot));
    }

    private static Formula Subscript(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));
}
