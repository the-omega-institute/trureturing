using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.SpectralTopology;

internal sealed class PointGapFiniteScaleStabilityDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/SpectralTopology/PointGapFiniteScaleStability.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A point-gap localizer stays invertible under a small relative position perturbation.",
        H("Point-Gap Finite-Scale Stability"),
        Blocks(
            Definition("position-direction", "positionDirection",
                "Position direction",
                "The shifted position observable defines a Hermitian block-diagonal direction on the doubled carrier."),
            Definition("relative-position-perturbation",
                "relativePositionPerturbation",
                "Relative position perturbation",
                "The scaled position direction is measured in coordinates of the inverse zero-scale localizer."),
            Definition("relative-position-factor", "relativePositionFactor",
                "Relative position factor",
                "The identity plus the relative position perturbation is the factor controlling finite-scale invertibility."),
            Describe.Lean(
                DescribeId.Create("scale-budget-stability"),
                DeclarationHandle.Create(
                    Prefix + "finite_scale_localizer_isUnit_of_scale_bound"),
                H("Explicit scale-budget stability"),
                StatementSource.FromAuthor(ScaleBudgetFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A Hermitian position observable gives a Hermitian block-diagonal position direction, and the finite-scale localizer is the zero-scale localizer plus the scaled direction; under a point gap it factors through its zero-scale value and the relative position factor, making finite-scale invertibility equivalent to invertibility of that factor.")),
                    Paragraph(Text(
                        "The relative perturbation norm is bounded by the inverse zero-scale norm times the scale and position-direction norms, and a perturbation of norm below one gives an invertible factor by the Neumann criterion; the explicit product bound is therefore a checkable sufficient stability budget, and combined with the frozen exact inertia a point gap supplies both half-dimensional chiral counts and invertibility throughout that budget."))),
                DescribeRole.Theorem)),
        []));

    private static DocumentBlock.Describe Definition(
        string id, string declaration, string heading, string paragraph) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(heading),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(paragraph))),
            DescribeRole.Definition);


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

    private static Formula NormOf(Formula inner) =>
        Seq(Lvert, inner, Rvert);

    private static Formula ScaleBudgetFormula() => Disp(Seq(
        Call("HasPointGap", F.Id("H"), F.Id("z")), Sp, Land, Sp,
        NormOf(Seq(Call("localizerZero", F.Id("X"), F.Id("H"), F.Id("x"), F.Id("z")),
            Caret, Grp(Seq(Minus, D(1))))),
        Sp, Cdot, Sp, NormOf(Seq(Kappa)), Sp, Cdot, Sp,
        NormOf(Call("positionDirection", F.Id("X"), F.Id("x"))),
        Sp, Lt, Sp, D(1),
        Sp, Implies, Sp,
        Call("IsUnit",
            Call("localizer", F.Id("X"), F.Id("H"), Kappa, F.Id("x"), F.Id("z")))));
}
