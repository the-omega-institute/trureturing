using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Petz;

internal sealed class StieltjesDensityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Petz/StieltjesDensity.";
    private const string Summary = "The boundary density has explicit off-diagonal and confluent formulas, continuity, and uniform bounds.";
    private static readonly (string Name, bool IsDefinition)[] Items =
    {
        ("rP", true),
        ("rQ", true),
        ("rho", true),
        ("rho_tendsto", false),
        ("log_factor_bound", false),
        ("rho_uniform_bound", false)
    };

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Summary,
        H("StieltjesDensity"),
        Blocks(Items.Select(item => Describe.Lean(
            DescribeId.Create("petz-stieltjesdensity-" + Slug(item.Name)),
            DeclarationHandle.Create(Prefix + item.Name),
            H(item.Name),
            StatementSource.FromAuthor(Disp(F.Id(item.Name.Replace("_", "")))),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(ResultText(item.Name, item.IsDefinition)))),
            item.IsDefinition ? DescribeRole.Definition : DescribeRole.Theorem)).ToArray())));

    private static string Slug(string name) => name.ToLowerInvariant().Replace("_", "-");

    private static string ResultText(string name, bool isDefinition) => name switch
    {
        "rP" => "rP is the first boundary density branch.",
        "rQ" => "rQ is the second boundary density branch.",
        "rho" => "rho combines the two boundary branches into the Stieltjes density.",
        "rho_tendsto" => "The named quantity has the stated regularity on the positive domain, including the indicated boundary or coincidence.",
        "log_factor_bound" => "The stated inequality or reflection identity holds for the auxiliary functions in its displayed domain.",
        "rho_uniform_bound" => "The stated inequality or reflection identity holds for the auxiliary functions in its displayed domain.",
        _ => "The named analytic identity holds with exactly the hypotheses and conclusion displayed in the statement."
    };
}
