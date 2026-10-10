using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.PositiveResolvent;

internal sealed class EulerResolventDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/PositiveResolvent/EulerResolvent.";
    private const string Summary = "Euler’s exponential-sine resolvent formulas give the positive logarithmic kernel, divided differences, and confluent limits.";
    private static readonly (string Name, bool IsDefinition)[] Items =
    {
        ("E", true),
        ("H", true),
        ("k", true),
        ("integral_exp_sin", false),
        ("integral_exp_sin_sq", false),
        ("integral_sin_sq_pi", false),
        ("H_eq_integral", false),
        ("k_eq_closed", false),
        ("k_diag", false),
        ("euler_resolvent_integrable", false),
        ("euler_resolvent", false),
        ("k_symm", false),
        ("k_pos", false),
        ("power_divdiff_integrable", false),
        ("power_divdiff_resolvent", false),
        ("power_divdiff_resolvent_diag", false)
    };

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Summary,
        H("EulerResolvent"),
        Blocks(Items.Select(item => Describe.Lean(
            DescribeId.Create("positiveresolvent-eulerresolvent-" + Slug(item.Name)),
            DeclarationHandle.Create(Prefix + item.Name),
            H(item.Name),
            StatementSource.FromAuthor(Disp(F.Id(item.Name.Replace("_", "")))),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(ResultText(item.Name, item.IsDefinition)))),
            item.IsDefinition ? DescribeRole.Definition : DescribeRole.Theorem)).ToArray())));

    private static string Slug(string name) => name.ToLowerInvariant().Replace("_", "-");

    private static string ResultText(string name, bool isDefinition) => name switch
    {
        "E" => "E is the squared logarithmic denominator in the Euler resolvent.",
        "H" => "H is the Euler resolvent numerator obtained by multiplying E by its two positive parameters.",
        "k" => "k is the positive two-variable Euler kernel.",
        "integral_exp_sin" => "The named quantity satisfies the stated integral or closed-form identity under exactly the displayed hypotheses.",
        "integral_exp_sin_sq" => "The named quantity satisfies the stated integral or closed-form identity under exactly the displayed hypotheses.",
        "integral_sin_sq_pi" => "The named quantity satisfies the stated integral or closed-form identity under exactly the displayed hypotheses.",
        "H_eq_integral" => "The named quantity satisfies the stated integral or closed-form identity under exactly the displayed hypotheses.",
        "k_eq_closed" => "The named quantity satisfies the stated integral or closed-form identity under exactly the displayed hypotheses.",
        "k_diag" => "At coincident arguments, the named quantity has the stated diagonal value.",
        "euler_resolvent_integrable" => "The displayed integrand is integrable on the positive half-line under the stated hypotheses.",
        "euler_resolvent" => "The named quantity satisfies the stated integral or closed-form identity under exactly the displayed hypotheses.",
        "k_symm" => "The stated exchange of variables leaves the named quantity unchanged.",
        "k_pos" => "Under its positive hypotheses, the named quantity is strictly positive.",
        "power_divdiff_integrable" => "The displayed integrand is integrable on the positive half-line under the stated hypotheses.",
        "power_divdiff_resolvent" => "The named quantity satisfies the stated integral or closed-form identity under exactly the displayed hypotheses.",
        "power_divdiff_resolvent_diag" => "At coincident arguments, the named quantity has the stated diagonal value.",
        _ => "The named analytic identity holds with exactly the hypotheses and conclusion displayed in the statement."
    };
}
