using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Petz;

internal sealed class KernelSmoothnessDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Petz/KernelSmoothness.";
    private const string Summary = "The symmetric kernel is smooth on the positive orthant, with explicit first and second directional derivatives.";
    private static readonly (string Name, bool IsDefinition)[] Items =
    {
        ("pos", true),
        ("hs_contDiffOn", false),
        ("hs_differentiableAt", false),
        ("hs1", true),
        ("hs1_swap", false),
        ("hs_deriv_repeated", false),
    };

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Summary,
        H("KernelSmoothness"),
        Blocks(Items.Select(item => Describe.Lean(
            DescribeId.Create("petz-kernelsmoothness-" + Slug(item.Name)),
            DeclarationHandle.Create(Prefix + item.Name),
            H(item.Name),
            StatementSource.FromAuthor(Disp(F.Id(item.Name.Replace("_", "")))),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(ResultText(item.Name, item.IsDefinition)))),
            item.IsDefinition ? DescribeRole.Definition : DescribeRole.Theorem)).ToArray())));

    private static string Slug(string name) => name.ToLowerInvariant().Replace("_", "-");

    private static string ResultText(string name, bool isDefinition) => name switch
    {
        "pos" => "pos is the positive orthant in product coordinates.",
        "hs_contDiffOn" => "The named quantity has the stated regularity on the positive domain, including the indicated boundary or coincidence.",
        "hs_differentiableAt" => "The named quantity has the stated regularity on the positive domain, including the indicated boundary or coincidence.",
        "hs1" => "hs1 is the first-slot derivative of the symmetric kernel.",
        "hs1_swap" => "At positive nodes, the derivative in the second slot at y equals hs1(y,x,z), the first-slot derivative after exchanging the first two nodes.",
        "hs_deriv_repeated" => "The stated derivative or principal-part identity holds under exactly the displayed hypotheses.",
        _ => "The named analytic identity holds with exactly the hypotheses and conclusion displayed in the statement."
    };
}
