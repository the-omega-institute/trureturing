using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Petz;

internal sealed class DensityPositivityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Petz/DensityPositivity.";
    private const string Summary = "The boundary Stieltjes density is strictly positive for positive nodes, including the confluent branch.";
    private static readonly (string Name, bool IsDefinition)[] Items =
    {
        ("rho_pos", false)
    };

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Summary,
        H("DensityPositivity"),
        Blocks(Items.Select(item => Describe.Lean(
            DescribeId.Create("petz-densitypositivity-" + Slug(item.Name)),
            DeclarationHandle.Create(Prefix + item.Name),
            H(item.Name),
            StatementSource.FromAuthor(Disp(F.Id(item.Name.Replace("_", "")))),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(ResultText(item.Name, item.IsDefinition)))),
            item.IsDefinition ? DescribeRole.Definition : DescribeRole.Theorem)).ToArray())));

    private static string Slug(string name) => name.ToLowerInvariant().Replace("_", "-");

    private static string ResultText(string name, bool isDefinition) => name switch
    {
        "rho_pos" => "Under its positive hypotheses, the named quantity is strictly positive.",
        _ => "The named analytic identity holds with exactly the hypotheses and conclusion displayed in the statement."
    };
}
