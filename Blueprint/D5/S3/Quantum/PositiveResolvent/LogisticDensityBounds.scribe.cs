using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.PositiveResolvent;

internal sealed class LogisticDensityBoundsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/PositiveResolvent/LogisticDensityBounds.";
    private const string Summary = "The logistic auxiliary functions satisfy reflection, derivative, curvature, and strict density-bracket inequalities.";
    private static readonly (string Name, bool IsDefinition)[] Items =
    {
        ("ell", true),
        ("jfun", true),
        ("jfun_deriv_lt", false),
        ("ell_deriv2_pos", false),
        ("density_bracket_pos_confluent", false),
        ("density_bracket_pos", false)
    };

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Summary,
        H("LogisticDensityBounds"),
        Blocks(Items.Select(item => Describe.Lean(
            DescribeId.Create("positiveresolvent-logisticdensitybounds-" + Slug(item.Name)),
            DeclarationHandle.Create(Prefix + item.Name),
            H(item.Name),
            StatementSource.FromAuthor(Disp(F.Id(item.Name.Replace("_", "")))),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(ResultText(item.Name, item.IsDefinition)))),
            item.IsDefinition ? DescribeRole.Definition : DescribeRole.Theorem)).ToArray())));

    private static string Slug(string name) => name.ToLowerInvariant().Replace("_", "-");

    private static string ResultText(string name, bool isDefinition) => name switch
    {
        "ell" => "ell is the logistic quadratic-over-denominator auxiliary function.",
        "jfun" => "jfun is the exponential-square logistic auxiliary function.",
        "jfun_deriv_lt" => "The stated derivative or principal-part identity holds under exactly the displayed hypotheses.",
        "ell_deriv2_pos" => "Under its positive hypotheses, the named quantity is strictly positive.",
        "density_bracket_pos_confluent" => "Under its positive hypotheses, the named quantity is strictly positive.",
        "density_bracket_pos" => "Under its positive hypotheses, the named quantity is strictly positive.",
        _ => "The named analytic identity holds with exactly the hypotheses and conclusion displayed in the statement."
    };
}
