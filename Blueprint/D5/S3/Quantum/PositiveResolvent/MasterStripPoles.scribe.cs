using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.PositiveResolvent;

internal sealed class MasterStripPolesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/PositiveResolvent/MasterStripPoles.";
    private const string Summary = "The logarithmic master-strip kernel has exactly the two classified simple poles and the stated principal parts and rectangle identity.";
    private static readonly (string Name, bool IsDefinition)[] Items =
    {
        ("stripPoleKernel", true),
        ("logPole", true),
        ("exp_upper_boundary", false),
        ("logistic_zero_iff", false),
        ("principal_part_at_pi", false),
        ("principal_part_at_logPole", false),
        ("stripPoleKernel_rectangle", false)
    };

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Summary,
        H("MasterStripPoles"),
        Blocks(Items.Select(item => Describe.Lean(
            DescribeId.Create("positiveresolvent-masterstrippoles-" + Slug(item.Name)),
            DeclarationHandle.Create(Prefix + item.Name),
            H(item.Name),
            StatementSource.FromAuthor(Disp(F.Id(item.Name.Replace("_", "")))),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(ResultText(item.Name, item.IsDefinition)))),
            item.IsDefinition ? DescribeRole.Definition : DescribeRole.Theorem)).ToArray())));

    private static string Slug(string name) => name.ToLowerInvariant().Replace("_", "-");

    private static string ResultText(string name, bool isDefinition) => name switch
    {
        "stripPoleKernel" => "stripPoleKernel is the complex logarithmic master-strip integrand.",
        "logPole" => "logPole is the nonreal pole determined by the positive parameter.",
        "exp_upper_boundary" => "The stated inequality or reflection identity holds for the auxiliary functions in its displayed domain.",
        "logistic_zero_iff" => "The stated strip, pole, or boundary characterization holds under its displayed hypotheses.",
        "principal_part_at_pi" => "The stated derivative or principal-part identity holds under exactly the displayed hypotheses.",
        "principal_part_at_logPole" => "The stated derivative or principal-part identity holds under exactly the displayed hypotheses.",
        "stripPoleKernel_rectangle" => "The stated strip, pole, or boundary characterization holds under its displayed hypotheses.",
        _ => "The named analytic identity holds with exactly the hypotheses and conclusion displayed in the statement."
    };
}
