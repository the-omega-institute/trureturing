using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Separation;

internal sealed class CompletionCriterionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The final observation quotient is its realized range and fills the formal-family space exactly under realizability.",
        H("Completion Criterion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("kernel-quotient-range-and-completion-criterion"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/Separation/CompletionCriterion.completion_criterion"),
                H("The kernel quotient completes exactly when every family is realized"),
                StatementSource.FromAuthor(CompletionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For an arbitrary observation map, final indistinguishability is equality "
                        + "of observations. The induced kernel quotient has a unique equivalence "
                        + "to the realized range that sends each class to its observed value.")),
                    Paragraph(Text(
                        "The same quotient has a unique equivalence to the entire codomain that "
                        + "commutes with observation exactly when every formal family in that "
                        + "codomain is the observation of a global object.")),
                    Paragraph(Text(
                        "Pinned Mathlib and Loogle supplied the exact reusable declarations "
                        + "Setoid.quotientKerEquivRange and "
                        + "Setoid.quotientKerEquivOfSurjective; both are imported and applied. "
                        + "Repository searches found only special finite-itinerary and controlled-"
                        + "behavior instances, while the LeanSearch query endpoint returned HTTP 404.")),
                    Paragraph(Text(
                        "The statement retains both coupled clauses: identification with the "
                        + "realized range and the if-and-only-if criterion for filling the whole "
                        + "formal-family codomain. No finiteness, topology, or linearity assumption "
                        + "is added."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula CompletionFormula()
    {
        Formula source = F.Id("X");
        Formula limit = F.Id("L");
        Formula point = F.Id("x");
        Formula family = F.Id("family");
        Formula observation = F.Id("observe");
        Formula rangeEquiv = F.Id("rangeEquiv");
        Formula limitEquiv = F.Id("limitEquiv");
        Formula quotient = Seq(
            Operatorname, Grp(F.Id("Quotient")), Open,
            Ker, Sp, observation, Close);
        Formula range = Seq(
            Operatorname, Grp(F.Id("range")), Open, observation, Close);
        Formula pointClass = Seq(OpenBracket, point, CloseBracket);

        Formula rangeClause = Seq(
            Open,
            Exists, Bang, Sp, rangeEquiv, Colon, Sp,
            quotient, Sp, Equiv, Sp, range, Comma, Sp,
            Forall, Sp, point, Colon, Sp, source, Comma, Sp,
            Apply(rangeEquiv, pointClass), Sp, Eq, Sp,
            Apply(observation, point),
            Close);

        Formula completionClause = Seq(
            Open,
            Open,
            Exists, Bang, Sp, limitEquiv, Colon, Sp,
            quotient, Sp, Equiv, Sp, limit, Comma, Sp,
            Forall, Sp, point, Colon, Sp, source, Comma, Sp,
            Apply(limitEquiv, pointClass), Sp, Eq, Sp,
            Apply(observation, point),
            Close, Sp, Leftrightarrow, Sp,
            Forall, Sp, family, Colon, Sp, limit, Comma, Sp,
            Exists, Sp, point, Colon, Sp, source, Comma, Sp,
            Apply(observation, point), Sp, Eq, Sp, family,
            Close);

        return Disp(Seq(
            rangeClause, Sp, Land, Sp, completionClause, Dot));
    }
}
