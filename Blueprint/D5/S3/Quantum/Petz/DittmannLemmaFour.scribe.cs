using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Petz;

internal sealed class DittmannLemmaFourDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Petz/DittmannLemmaFour.";
    private const string Summary = "Strict Dittmann inequalities follow from positive Stieltjes densities and differentiation under the integral.";
    private static readonly (string Name, bool IsDefinition)[] Items =
    {
        ("dittmann65", false),
        ("dittmann63", false),
        ("dittmann62", false),
        ("claim65", false),
        ("claim63", false),
        ("claim62", false)
    };

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Summary,
        H("DittmannLemmaFour"),
        Blocks(Items.Select(item => Describe.Lean(
            DescribeId.Create("petz-dittmannlemmafour-" + Slug(item.Name)),
            DeclarationHandle.Create(Prefix + item.Name),
            H(item.Name),
            StatementSource.FromAuthor(Disp(F.Id(item.Name.Replace("_", "")))),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(ResultText(item.Name, item.IsDefinition)))),
            item.IsDefinition ? DescribeRole.Definition : DescribeRole.Theorem)).ToArray())));

    private static string Slug(string name) => name.ToLowerInvariant().Replace("_", "-");

    private static string ResultText(string name, bool isDefinition) => name switch
    {
        "dittmann65" => "The corresponding Dittmann inequality holds with the full positive-node quantifiers shown in the statement.",
        "dittmann63" => "The corresponding Dittmann inequality holds with the full positive-node quantifiers shown in the statement.",
        "dittmann62" => "The corresponding Dittmann inequality holds with the full positive-node quantifiers shown in the statement.",
        "claim65" => "The corresponding Dittmann inequality holds with the full positive-node quantifiers shown in the statement.",
        "claim63" => "The corresponding Dittmann inequality holds with the full positive-node quantifiers shown in the statement.",
        "claim62" => "The corresponding Dittmann inequality holds with the full positive-node quantifiers shown in the statement.",
        _ => "The named analytic identity holds with exactly the hypotheses and conclusion displayed in the statement."
    };
}
