using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.PositiveResolvent;

internal sealed class LogMeanResolventsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/PositiveResolvent/LogMeanResolvents.";
    private const string Summary = "The logarithmic two-node and three-node resolvents have integral, positivity, symmetry, homogeneity, and continuity laws.";
    private static readonly (string Name, bool IsDefinition)[] Items =
    {
        ("L", true),
        ("m", true),
        ("L_pos", false),
        ("L_self", false),
        ("L_eq_of_ne", false),
        ("L_symm", false),
        ("L_eq_integral_Ioi", false),
        ("m_integrable", false),
        ("L_sub_L_eq_m", false),
        ("m_symm", false),
        ("m_symm_right", false),
        ("m_self", false),
        ("L_homog", false),
        ("m_homog", false),
        ("L_continuousAt", false),
        ("m_continuousAt", false)
    };

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Summary,
        H("LogMeanResolvents"),
        Blocks(Items.Select(item => Describe.Lean(
            DescribeId.Create("positiveresolvent-logmeanresolvents-" + Slug(item.Name)),
            DeclarationHandle.Create(Prefix + item.Name),
            H(item.Name),
            StatementSource.FromAuthor(Disp(F.Id(item.Name.Replace("_", "")))),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(ResultText(item.Name, item.IsDefinition)))),
            item.IsDefinition ? DescribeRole.Definition : DescribeRole.Theorem)).ToArray())));

    private static string Slug(string name) => name.ToLowerInvariant().Replace("_", "-");

    private static string ResultText(string name, bool isDefinition) => name switch
    {
        "L" => "The logarithmic mean resolvent is the positive-node integral kernel used throughout the construction.",
        "m" => "The three-node resolvent is the corresponding positive integral with three denominator factors.",
        "L_pos" => "Under its positive hypotheses, the named quantity is strictly positive.",
        "L_self" => "At coincident arguments, the named quantity has the stated diagonal value.",
        "L_eq_of_ne" => "The named quantity satisfies the stated integral or closed-form identity under exactly the displayed hypotheses.",
        "L_symm" => "The stated exchange of variables leaves the named quantity unchanged.",
        "L_eq_integral_Ioi" => "The named quantity satisfies the stated integral or closed-form identity under exactly the displayed hypotheses.",
        "m_integrable" => "The displayed integrand is integrable on the positive half-line under the stated hypotheses.",
        "L_sub_L_eq_m" => "The named quantity satisfies the stated integral or closed-form identity under exactly the displayed hypotheses.",
        "m_symm" => "The stated exchange of variables leaves the named quantity unchanged.",
        "m_symm_right" => "The stated exchange of variables leaves the named quantity unchanged.",
        "m_self" => "At coincident arguments, the named quantity has the stated diagonal value.",
        "L_homog" => "Positive simultaneous rescaling gives the stated homogeneity law.",
        "m_homog" => "Positive simultaneous rescaling gives the stated homogeneity law.",
        "L_continuousAt" => "The named quantity has the stated regularity on the positive domain, including the indicated boundary or coincidence.",
        "m_continuousAt" => "The named quantity has the stated regularity on the positive domain, including the indicated boundary or coincidence.",
        _ => "The named analytic identity holds with exactly the hypotheses and conclusion displayed in the statement."
    };
}
