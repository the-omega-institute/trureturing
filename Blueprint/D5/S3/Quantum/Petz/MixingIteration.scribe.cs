using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Petz;

internal sealed class MixingIterationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Petz/MixingIteration.";
    private const string Summary = "Finite prefix majorization of positive vectors reduces to two-coordinate mixings and permutations by a strictly decreasing count of unequal coordinates.";
    private static readonly (string Name, bool IsDefinition)[] Items =
    {
        ("prefixSum", true),
        ("transfer", true),
        ("pair_transfer_reduction", false)
    };

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Summary,
        H("MixingIteration"),
        Blocks(Items.Select(item => Describe.Lean(
            DescribeId.Create("petz-mixing-iteration-" + Slug(item.Name)),
            DeclarationHandle.Create(Prefix + item.Name),
            H(item.Name),
            StatementSource.FromAuthor(Disp(F.Id(item.Name.Replace("_", "")))),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(ResultText(item.Name)))),
            item.IsDefinition ? DescribeRole.Definition : DescribeRole.Theorem)).ToArray())));

    private static string Slug(string name) => name.ToLowerInvariant().Replace("_", "-");

    private static string ResultText(string name) => name switch
    {
        "prefixSum" => "prefixSum adds the coordinates whose indices lie below the natural-number cutoff, retaining each labelled position.",
        "transfer" => "transfer replaces two distinct coordinates by their complementary convex combinations and leaves every other coordinate unchanged.",
        "pair_transfer_reduction" => "A permutation-invariant real-valued function that does not decrease under positive ordered pair mixings with parameter between zero and one half respects prefix majorization. Both vectors are positive and have equal total sums; only the target must be decreasing. The earliest deficit is filled from an earlier surplus, preserving positivity and prefix inequalities and strictly reducing the number of unequal coordinates.",
        _ => "The named quantity has exactly the displayed mathematical meaning."
    };
}
