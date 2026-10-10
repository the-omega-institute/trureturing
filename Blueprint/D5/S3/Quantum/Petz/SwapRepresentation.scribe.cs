using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Petz;

internal sealed class SwapRepresentationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Petz/SwapRepresentation.";
    private const string Summary = "The symmetric kernel and its first-slot derivative admit the fixed-density swap integral identities.";
    private static readonly (string Name, bool IsDefinition)[] Items =
    {
        ("swap_representation", false),
        ("hs1_sub_swap_integral", false)
    };

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Summary,
        H("SwapRepresentation"),
        Blocks(Items.Select(item => Describe.Lean(
            DescribeId.Create("petz-swaprepresentation-" + Slug(item.Name)),
            DeclarationHandle.Create(Prefix + item.Name),
            H(item.Name),
            StatementSource.FromAuthor(Disp(F.Id(item.Name.Replace("_", "")))),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(ResultText(item.Name, item.IsDefinition)))),
            item.IsDefinition ? DescribeRole.Definition : DescribeRole.Theorem)).ToArray())));

    private static string Slug(string name) => name.ToLowerInvariant().Replace("_", "-");

    private static string ResultText(string name, bool isDefinition) => name switch
    {
        "swap_representation" => "The named quantity satisfies the stated integral or closed-form identity under exactly the displayed hypotheses.",
        "hs1_sub_swap_integral" => "The named quantity satisfies the stated integral or closed-form identity under exactly the displayed hypotheses.",
        _ => "The named analytic identity holds with exactly the hypotheses and conclusion displayed in the statement."
    };
}
