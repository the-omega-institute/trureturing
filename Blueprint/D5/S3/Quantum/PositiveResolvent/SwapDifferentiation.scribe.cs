using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.PositiveResolvent;

internal sealed class SwapDifferentiationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/PositiveResolvent/SwapDifferentiation.";
    private const string Summary = "A fixed signed density can be differentiated along a constant-sum resolvent path with an explicit integrable derivative.";
    private static readonly (string Name, bool IsDefinition)[] Items =
    {
        ("signed_swap_hasDerivAt", false)
    };

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Summary,
        H("SwapDifferentiation"),
        Blocks(Items.Select(item => Describe.Lean(
            DescribeId.Create("positiveresolvent-swapdifferentiation-" + Slug(item.Name)),
            DeclarationHandle.Create(Prefix + item.Name),
            H(item.Name),
            StatementSource.FromAuthor(Disp(F.Id(item.Name.Replace("_", "")))),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(ResultText(item.Name, item.IsDefinition)))),
            item.IsDefinition ? DescribeRole.Definition : DescribeRole.Theorem)).ToArray())));

    private static string Slug(string name) => name.ToLowerInvariant().Replace("_", "-");

    private static string ResultText(string name, bool isDefinition) => name switch
    {
        "signed_swap_hasDerivAt" => "The stated derivative or principal-part identity holds under exactly the displayed hypotheses.",
        _ => "The named analytic identity holds with exactly the hypotheses and conclusion displayed in the statement."
    };
}
