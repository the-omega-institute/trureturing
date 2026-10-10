using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Petz;

internal sealed class DoubleStieltjesRepresentationsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Petz/DoubleStieltjesRepresentations.";
    private const string Summary = "The double Stieltjes integrals equal the power-simplex and exponential second-difference representations.";
    private static readonly (string Name, bool IsDefinition)[] Items =
    {
        ("A_double_stieltjes", false),
        ("Q_double_stieltjes", false)
    };

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Summary,
        H("DoubleStieltjesRepresentations"),
        Blocks(Items.Select(item => Describe.Lean(
            DescribeId.Create("petz-doublestieltjesrepresentations-" + Slug(item.Name)),
            DeclarationHandle.Create(Prefix + item.Name),
            H(item.Name),
            StatementSource.FromAuthor(Disp(F.Id(item.Name.Replace("_", "")))),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(ResultText(item.Name, item.IsDefinition)))),
            item.IsDefinition ? DescribeRole.Definition : DescribeRole.Theorem)).ToArray())));

    private static string Slug(string name) => name.ToLowerInvariant().Replace("_", "-");

    private static string ResultText(string name, bool isDefinition) => name switch
    {
        "A_double_stieltjes" => "The named quantity satisfies the stated integral or closed-form identity under exactly the displayed hypotheses.",
        "Q_double_stieltjes" => "The named quantity satisfies the stated integral or closed-form identity under exactly the displayed hypotheses.",
        _ => "The named analytic identity holds with exactly the hypotheses and conclusion displayed in the statement."
    };
}
