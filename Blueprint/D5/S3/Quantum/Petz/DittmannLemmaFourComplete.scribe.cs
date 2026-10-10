using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Petz;

internal sealed class DittmannLemmaFourCompleteDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Petz/DittmannLemmaFourComplete.";
    private const string Summary = "The strict swap inequality and the four literal inequalities of Dittmann Lemma 4 hold for ordered positive nodes.";
    private static readonly (string Name, bool IsDefinition)[] Items =
    {
        ("dittmann64", false),
        ("claim64", false),
        ("lemma4", false)
    };

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Summary,
        H("DittmannLemmaFourComplete"),
        Blocks(Items.Select(item => Describe.Lean(
            DescribeId.Create("petz-dittmannlemmafourcomplete-" + Slug(item.Name)),
            DeclarationHandle.Create(Prefix + item.Name),
            H(item.Name),
            StatementSource.FromAuthor(Disp(F.Id(item.Name.Replace("_", "")))),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(ResultText(item.Name, item.IsDefinition)))),
            item.IsDefinition ? DescribeRole.Definition : DescribeRole.Theorem)).ToArray())));

    private static string Slug(string name) => name.ToLowerInvariant().Replace("_", "-");

    private static string ResultText(string name, bool isDefinition) => name switch
    {
        "dittmann64" => "The corresponding Dittmann inequality holds with the full positive-node quantifiers shown in the statement.",
        "claim64" => "The corresponding Dittmann inequality holds with the full positive-node quantifiers shown in the statement.",
        "lemma4" => "The corresponding Dittmann inequality holds with the full positive-node quantifiers shown in the statement.",
        _ => "The named analytic identity holds with exactly the hypotheses and conclusion displayed in the statement."
    };
}
