using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.PositiveResolvent;

internal sealed class ExponentialSecondDifferenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/PositiveResolvent/ExponentialSecondDifference.";
    private const string Summary = "The compact exponential second difference has diagonal value, homogeneity, Hermite–Genocchi evaluation, symmetries, and continuity.";
    private static readonly (string Name, bool IsDefinition)[] Items =
    {
        ("Q", true),
        ("Q_self", false),
        ("Q_homog", false),
        ("Q_eq_of_ne", false),
        ("Q_symm", false),
        ("Q_symm_right", false),
        ("Q_continuousAt", false)
    };

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Summary,
        H("ExponentialSecondDifference"),
        Blocks(Items.Select(item => Describe.Lean(
            DescribeId.Create("positiveresolvent-exponentialseconddifference-" + Slug(item.Name)),
            DeclarationHandle.Create(Prefix + item.Name),
            H(item.Name),
            StatementSource.FromAuthor(Disp(F.Id(item.Name.Replace("_", "")))),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(ResultText(item.Name, item.IsDefinition)))),
            item.IsDefinition ? DescribeRole.Definition : DescribeRole.Theorem)).ToArray())));

    private static string Slug(string name) => name.ToLowerInvariant().Replace("_", "-");

    private static string ResultText(string name, bool isDefinition) => name switch
    {
        "Q" => "The compact exponential second-difference integral defines the symmetric three-node quantity.",
        "Q_self" => "At coincident arguments, the named quantity has the stated diagonal value.",
        "Q_homog" => "Positive simultaneous rescaling gives the stated homogeneity law.",
        "Q_eq_of_ne" => "The named quantity satisfies the stated integral or closed-form identity under exactly the displayed hypotheses.",
        "Q_symm" => "The stated exchange of variables leaves the named quantity unchanged.",
        "Q_symm_right" => "The stated exchange of variables leaves the named quantity unchanged.",
        "Q_continuousAt" => "The named quantity has the stated regularity on the positive domain, including the indicated boundary or coincidence.",
        _ => "The named analytic identity holds with exactly the hypotheses and conclusion displayed in the statement."
    };
}
