using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Petz;

internal sealed class SymmetricStieltjesSwapDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Petz/SymmetricStieltjesSwap.";
    private const string Summary = "A symmetric double Stieltjes transform is invariant under swapping two nodes, with the corresponding derivative identity.";
    private static readonly (string Name, bool IsDefinition)[] Items =
    {
        ("symmetric_stieltjes_swap", false),
    };

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Summary,
        H("SymmetricStieltjesSwap"),
        Blocks(Items.Select(item => Describe.Lean(
            DescribeId.Create("petz-symmetricstieltjesswap-" + Slug(item.Name)),
            DeclarationHandle.Create(Prefix + item.Name),
            H(item.Name),
            StatementSource.FromAuthor(Disp(F.Id(item.Name.Replace("_", "")))),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(ResultText(item.Name, item.IsDefinition)))),
            item.IsDefinition ? DescribeRole.Definition : DescribeRole.Theorem)).ToArray())));

    private static string Slug(string name) => name.ToLowerInvariant().Replace("_", "-");

    private static string ResultText(string name, bool isDefinition) => name switch
    {
        "symmetric_stieltjes_swap" => "For a measurable nonnegative symmetric kernel K and positive x,y, integrability of its double resolvent integral implies integrability of the swap representation and equality with the single integral of (1/(x+s)+1/(y+s)) times the inner integral of K(s,t)/(x+y+s+t).",
        _ => "The named analytic identity holds with exactly the hypotheses and conclusion displayed in the statement."
    };
}
