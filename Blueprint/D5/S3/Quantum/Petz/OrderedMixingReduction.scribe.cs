using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Petz;

internal sealed class OrderedMixingReductionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Petz/OrderedMixingReduction.";
    private const string Summary = "Permutation invariance and nonnegative ordered pair directional derivatives imply monotonicity under finite majorization of positive vectors.";
    private static readonly (string Name, bool IsDefinition)[] Items =
    {
        ("pairDirection", true),
        ("pair_transfer_reduction", false),
        ("derivative_pair_transfer_reduction", false)
    };

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Summary,
        H("OrderedMixingReduction"),
        Blocks(Items.Select(item => Describe.Lean(
            DescribeId.Create("petz-ordered-mixing-reduction-" + Slug(item.Name)),
            DeclarationHandle.Create(Prefix + item.Name),
            H(item.Name),
            StatementSource.FromAuthor(Disp(F.Id(item.Name.Replace("_", "")))),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(ResultText(item.Name)))),
            item.IsDefinition ? DescribeRole.Definition : DescribeRole.Theorem)).ToArray())));

    private static string Slug(string name) => name.ToLowerInvariant().Replace("_", "-");

    private static string ResultText(string name) => name switch
    {
        "pairDirection" => "For distinct indices, pairDirection is the unit coordinate direction that increases the first coordinate and decreases the second by the same amount.",
        "pair_transfer_reduction" => "Permutation invariance and monotonicity under ordered positive pair mixings imply the comparison of positive vectors with equal sums and target prefix sums at most the initial prefix sums. The target is decreasing; the initial vector need not be sorted.",
        "derivative_pair_transfer_reduction" => "The same majorization comparison follows from permutation invariance, differentiability at every point of each closed half-transfer path, and a nonnegative unit directional derivative whenever the increased coordinate is smaller than the decreased coordinate. Affine reparametrization multiplies the unit derivative by the original positive coordinate gap; mean-value monotonicity and endpoint continuity give the finite pair comparison.",
        _ => "The named quantity has exactly the displayed mathematical meaning."
    };
}
