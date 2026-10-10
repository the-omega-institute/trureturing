using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Petz;

internal sealed class DoubleStieltjesMarginalsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Petz/DoubleStieltjesMarginals.";
    private const string Summary = "Simplex marginals recover the Stieltjes density and the canonical logarithmic second divided difference.";
    private static readonly (string Name, bool IsDefinition)[] Items =
    {
        ("simplex_marginal_eq_rQ", false),
        ("A_marginal_eq_rQ", false),
        ("qIntegrand", true),
        ("Q_eq_simplex", false)
    };

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Summary,
        H("DoubleStieltjesMarginals"),
        Blocks(Items.Select(item => Describe.Lean(
            DescribeId.Create("petz-doublestieltjesmarginals-" + Slug(item.Name)),
            DeclarationHandle.Create(Prefix + item.Name),
            H(item.Name),
            StatementSource.FromAuthor(Disp(F.Id(item.Name.Replace("_", "")))),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(ResultText(item.Name, item.IsDefinition)))),
            item.IsDefinition ? DescribeRole.Definition : DescribeRole.Theorem)).ToArray())));

    private static string Slug(string name) => name.ToLowerInvariant().Replace("_", "-");

    private static string ResultText(string name, bool isDefinition) => name switch
    {
        "simplex_marginal_eq_rQ" => "The named quantity satisfies the stated integral or closed-form identity under exactly the displayed hypotheses.",
        "A_marginal_eq_rQ" => "The named quantity satisfies the stated integral or closed-form identity under exactly the displayed hypotheses.",
        "qIntegrand" => "qIntegrand is the simplex integrand for the logarithmic second divided difference.",
        "Q_eq_simplex" => "The named quantity satisfies the stated integral or closed-form identity under exactly the displayed hypotheses.",
        _ => "The named analytic identity holds with exactly the hypotheses and conclusion displayed in the statement."
    };
}
