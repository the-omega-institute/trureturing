using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Petz;

internal sealed class StieltjesRepresentationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Petz/StieltjesRepresentation.";
    private const string Summary = "The density is integrable and represents the negative symmetric kernel at every positive node, including coincidences.";
    private static readonly (string Name, bool IsDefinition)[] Items =
    {
        ("rho_integrable", false),
        ("stieltjes_representation", false)
    };

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Summary,
        H("StieltjesRepresentation"),
        Blocks(Items.Select(item => Describe.Lean(
            DescribeId.Create("petz-stieltjesrepresentation-" + Slug(item.Name)),
            DeclarationHandle.Create(Prefix + item.Name),
            H(item.Name),
            StatementSource.FromAuthor(Disp(F.Id(item.Name.Replace("_", "")))),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(ResultText(item.Name, item.IsDefinition)))),
            item.IsDefinition ? DescribeRole.Definition : DescribeRole.Theorem)).ToArray())));

    private static string Slug(string name) => name.ToLowerInvariant().Replace("_", "-");

    private static string ResultText(string name, bool isDefinition) => name switch
    {
        "rho_integrable" => "The displayed integrand is integrable on the positive half-line under the stated hypotheses.",
        "stieltjes_representation" => "The named quantity satisfies the stated integral or closed-form identity under exactly the displayed hypotheses.",
        _ => "The named analytic identity holds with exactly the hypotheses and conclusion displayed in the statement."
    };
}
