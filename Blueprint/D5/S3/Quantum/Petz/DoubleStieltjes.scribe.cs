using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Petz;

internal sealed class DoubleStieltjesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Petz/DoubleStieltjes.";
    private const string Summary = "Positive symmetric double Stieltjes kernels and their finite positive-mixture resolvent marginals are identified.";
    private static readonly (string Name, bool IsDefinition)[] Items =
    {
        ("triangle", true),
        ("triangle_isOpen", false),
        ("triangle_subset", false),
        ("A", true),
        ("A_pos", false),
        ("A_measurable", false),
        ("A_symm", false),
        ("aMarginalIntegrand", true),
        ("A_marginal", false),
        ("B", true),
        ("B_pos", false),
        ("B_symm", false),
        ("H_divdiff_integral", false),
        ("B_marginal", false),
        ("B_measurable", false),
        ("rP_marginal", false)
    };

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Summary,
        H("DoubleStieltjes"),
        Blocks(Items.Select(item => Describe.Lean(
            DescribeId.Create("petz-doublestieltjes-" + Slug(item.Name)),
            DeclarationHandle.Create(Prefix + item.Name),
            H(item.Name),
            StatementSource.FromAuthor(Disp(F.Id(item.Name.Replace("_", "")))),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(ResultText(item.Name, item.IsDefinition)))),
            item.IsDefinition ? DescribeRole.Definition : DescribeRole.Theorem)).ToArray())));

    private static string Slug(string name) => name.ToLowerInvariant().Replace("_", "-");

    private static string ResultText(string name, bool isDefinition) => name switch
    {
        "triangle" => "triangle is the open two-dimensional simplex used for the parameter integral.",
        "triangle_isOpen" => "The stated set-theoretic property holds for the parameter domain.",
        "triangle_subset" => "The stated set-theoretic property holds for the parameter domain.",
        "A" => "A is the symmetric positive double Stieltjes density.",
        "A_pos" => "Under its positive hypotheses, the named quantity is strictly positive.",
        "A_measurable" => "The named analytic identity holds with exactly the hypotheses and conclusion displayed in the statement.",
        "A_symm" => "The stated exchange of variables leaves the named quantity unchanged.",
        "aMarginalIntegrand" => "aMarginalIntegrand is the one-row integrand of the simplex marginal.",
        "A_marginal" => "The named quantity satisfies the stated integral or closed-form identity under exactly the displayed hypotheses.",
        "B" => "B is the symmetric resolvent density built from k.",
        "B_pos" => "Under its positive hypotheses, the named quantity is strictly positive.",
        "B_symm" => "The stated exchange of variables leaves the named quantity unchanged.",
        "H_divdiff_integral" => "The named quantity satisfies the stated integral or closed-form identity under exactly the displayed hypotheses.",
        "B_marginal" => "The named quantity satisfies the stated integral or closed-form identity under exactly the displayed hypotheses.",
        "B_measurable" => "The named analytic identity holds with exactly the hypotheses and conclusion displayed in the statement.",
        "rP_marginal" => "The named quantity satisfies the stated integral or closed-form identity under exactly the displayed hypotheses.",
        _ => "The named analytic identity holds with exactly the hypotheses and conclusion displayed in the statement."
    };
}
