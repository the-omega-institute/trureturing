using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.PositiveResolvent;

internal sealed class MasterStripLimitsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/PositiveResolvent/MasterStripLimits.";
    private const string Summary = "The Lorentz strip weight is integrable and its vertical and reciprocal-strip integrals have the stated limits.";
    private static readonly (string Name, bool IsDefinition)[] Items =
    {
        ("stripWeight", true),
        ("lorentz_integrable", false),
        ("lorentz_integral", false),
        ("stripWeight_integrable", false),
        ("vertical_right_tendsto", false),
        ("vertical_left_tendsto", false),
        ("reciprocalStrip_integral", false),
        ("stripWeight_integral", false)
    };

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Summary,
        H("MasterStripLimits"),
        Blocks(Items.Select(item => Describe.Lean(
            DescribeId.Create("positiveresolvent-masterstriplimits-" + Slug(item.Name)),
            DeclarationHandle.Create(Prefix + item.Name),
            H(item.Name),
            StatementSource.FromAuthor(Disp(F.Id(item.Name.Replace("_", "")))),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(ResultText(item.Name, item.IsDefinition)))),
            item.IsDefinition ? DescribeRole.Definition : DescribeRole.Theorem)).ToArray())));

    private static string Slug(string name) => name.ToLowerInvariant().Replace("_", "-");

    private static string ResultText(string name, bool isDefinition) => name switch
    {
        "stripWeight" => "stripWeight is the Lorentzian weight pulled back by the exponential coordinate.",
        "lorentz_integrable" => "The displayed integrand is integrable on the positive half-line under the stated hypotheses.",
        "lorentz_integral" => "The named quantity satisfies the stated integral or closed-form identity under exactly the displayed hypotheses.",
        "stripWeight_integrable" => "The displayed integrand is integrable on the positive half-line under the stated hypotheses.",
        "vertical_right_tendsto" => "The named quantity has the stated regularity on the positive domain, including the indicated boundary or coincidence.",
        "vertical_left_tendsto" => "The named quantity has the stated regularity on the positive domain, including the indicated boundary or coincidence.",
        "reciprocalStrip_integral" => "The named quantity satisfies the stated integral or closed-form identity under exactly the displayed hypotheses.",
        "stripWeight_integral" => "The named quantity satisfies the stated integral or closed-form identity under exactly the displayed hypotheses.",
        _ => "The named analytic identity holds with exactly the hypotheses and conclusion displayed in the statement."
    };
}
