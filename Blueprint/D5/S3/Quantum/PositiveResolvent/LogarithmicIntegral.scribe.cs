using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.PositiveResolvent;

internal sealed class LogarithmicIntegralDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/PositiveResolvent/LogarithmicIntegral.";
    private const string Summary = "The logarithmic master integral and its normalized density mass have the stated closed forms.";
    private static readonly (string Name, bool IsDefinition)[] Items =
    {
        ("masterValue", true),
        ("logarithmic_density_mass", false),
        ("master_integral", false)
    };

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Summary,
        H("LogarithmicIntegral"),
        Blocks(Items.Select(item => Describe.Lean(
            DescribeId.Create("positiveresolvent-logarithmicintegral-" + Slug(item.Name)),
            DeclarationHandle.Create(Prefix + item.Name),
            H(item.Name),
            StatementSource.FromAuthor(Disp(F.Id(item.Name.Replace("_", "")))),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(ResultText(item.Name, item.IsDefinition)))),
            item.IsDefinition ? DescribeRole.Definition : DescribeRole.Theorem)).ToArray())));

    private static string Slug(string name) => name.ToLowerInvariant().Replace("_", "-");

    private static string ResultText(string name, bool isDefinition) => name switch
    {
        "masterValue" => "masterValue is the closed-form logarithmic master integral.",
        "logarithmic_density_mass" => "The named analytic identity holds with exactly the hypotheses and conclusion displayed in the statement.",
        "master_integral" => "The named quantity satisfies the stated integral or closed-form identity under exactly the displayed hypotheses.",
        _ => "The named analytic identity holds with exactly the hypotheses and conclusion displayed in the statement."
    };
}
