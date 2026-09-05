using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.MeasureSeparation;

internal sealed class FourierModeDeterminationDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/MeasureSeparation/FourierModeDetermination.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite Fourier data leave regulator measures nonunique; the complete profile is exact.",
        H("Fourier-Mode Determination"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-fourier-modes-do-not-determine-measure"),
                DeclarationHandle.Create(
                    Prefix + "finite_fourier_modes_do_not_determine_measure"),
                H("Every finite Fourier table has distinct realizations"),
                StatementSource.FromAuthor(FiniteModesFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a finite mode set, choose a positive integer k beyond every listed "
                            + "absolute frequency. The construction compares normalized circle "
                            + "Haar measure with its density 1 + Re(fourier k)/2 perturbation.")),
                    Paragraph(Text(
                        "Fourier orthogonality makes the two probability measures agree on every "
                            + "listed mode. Their moments at the unused mode -k differ by one "
                            + "quarter, which proves that the measures themselves are distinct.")),
                    Paragraph(Text(
                        "The explicit nonnegative density and the unused-mode discrepancy are the "
                            + "constructive escape witness for finite non-clonability."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("all-fourier-modes-determine-measure"),
                DeclarationHandle.Create(
                    Prefix + "all_fourier_modes_determine_measure"),
                H("The complete Fourier profile determines the measure"),
                StatementSource.FromAuthor(AllModesFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The Fourier characters generate a star subalgebra that separates points "
                            + "of the additive circle.")),
                    Paragraph(Text(
                        "Equality on every character extends by linearity to that algebra. The "
                            + "pinned Mathlib finite-measure extensionality theorem then identifies "
                            + "the two finite regulator measures."))),
                DescribeRole.Theorem))));

    private static Formula FiniteModesFormula()
    {
        Formula integers = Seq(Mathbb, Grp(F.Id("Z")));
        Formula circle = CircleType();
        Formula measure = Call("Measure", circle);
        Formula modes = F.Id("S");
        Formula mu = F.Id("mu");
        Formula nu = F.Id("nu");
        Formula n = F.Id("n");

        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, Typed(modes, Call("Finset", integers)), Comma),
            Seq(Grp(), Exists, Sp, Typed(mu, measure), Comma, Sp,
                Exists, Sp, Typed(nu, measure), Comma),
            Seq(Grp(), Call("IsProbabilityMeasure", mu), Sp, Land, Sp,
                Call("IsProbabilityMeasure", nu), Sp, Land, Sp,
                mu, Sp, Neq, Sp, nu, Sp, Land),
            Seq(Grp(), Forall, Sp, n, Sp, InMacro, Sp, modes, Comma, Sp,
                Moment(mu, n), Sp, Eq, Sp, Moment(nu, n), Dot),
        ]));
    }

    private static Formula AllModesFormula()
    {
        Formula integers = Seq(Mathbb, Grp(F.Id("Z")));
        Formula measure = Call("Measure", CircleType());
        Formula mu = F.Id("mu");
        Formula nu = F.Id("nu");
        Formula n = F.Id("n");

        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, Typed(mu, measure), Comma, Sp, Typed(nu, measure), Comma),
            Seq(Grp(), Typeclass("IsFiniteMeasure", mu), Comma, Sp,
                Typeclass("IsFiniteMeasure", nu), Comma),
            Seq(Grp(), Open, Forall, Sp, Typed(n, integers), Comma, Sp,
                Moment(mu, n), Sp, Eq, Sp, Moment(nu, n), Close,
                Sp, Rightarrow, Sp, mu, Sp, Eq, Sp, nu, Dot),
        ]));
    }

    private static Formula CircleType() =>
        Call("AddCircle", Seq(D(2), Sp, Cdot, Sp, Pi));

    private static Formula Moment(Formula measure, Formula mode) =>
        Call("fourierMoment", measure, mode);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Typeclass(string name, params Formula[] arguments) =>
        Seq(OpenBracket, Call(name, arguments), CloseBracket);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}
