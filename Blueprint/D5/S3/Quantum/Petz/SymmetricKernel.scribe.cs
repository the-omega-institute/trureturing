using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Petz;

internal sealed class SymmetricKernelDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Petz/SymmetricKernel.";
    private const string Summary = "The symmetric logarithmic kernel, its closed form, permutation symmetries, homogeneity, diagonal value, and continuity are established.";
    private static readonly (string Name, bool IsDefinition)[] Items =
    {
        ("P", true),
        ("hs", true),
        ("closedForm", true),
        ("hs_eq_closedForm", false),
        ("hs_symm", false),
        ("hs_symm_right", false),
        ("hs_homog", false),
        ("hs_self", false),
        ("hs_perm", false),
        ("hs_continuousAt", false),
        ("hs_continuousOn", false)
    };

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Summary,
        H("SymmetricKernel"),
        Blocks(Items.Select(item => Describe.Lean(
            DescribeId.Create("petz-symmetrickernel-" + Slug(item.Name)),
            DeclarationHandle.Create(Prefix + item.Name),
            H(item.Name),
            StatementSource.FromAuthor(Disp(F.Id(item.Name.Replace("_", "")))),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(ResultText(item.Name, item.IsDefinition)))),
            item.IsDefinition ? DescribeRole.Definition : DescribeRole.Theorem)).ToArray())));

    private static string Slug(string name) => name.ToLowerInvariant().Replace("_", "-");

    private static string ResultText(string name, bool isDefinition) => name switch
    {
        "P" => "P is the normalized square of the three-node resolvent divided by the pairwise logarithmic means.",
        "hs" => "hs is the symmetric kernel formed from P and the exponential second difference.",
        "closedForm" => "closedForm is the explicit logarithmic expression for the symmetric kernel.",
        "hs_eq_closedForm" => "The named quantity satisfies the stated integral or closed-form identity under exactly the displayed hypotheses.",
        "hs_symm" => "The stated exchange of variables leaves the named quantity unchanged.",
        "hs_symm_right" => "The stated exchange of variables leaves the named quantity unchanged.",
        "hs_homog" => "Positive simultaneous rescaling gives the stated homogeneity law.",
        "hs_self" => "At coincident arguments, the named quantity has the stated diagonal value.",
        "hs_perm" => "The stated exchange of variables leaves the named quantity unchanged.",
        "hs_continuousAt" => "The named quantity has the stated regularity on the positive domain, including the indicated boundary or coincidence.",
        "hs_continuousOn" => "The named quantity has the stated regularity on the positive domain, including the indicated boundary or coincidence.",
        _ => "The named analytic identity holds with exactly the hypotheses and conclusion displayed in the statement."
    };
}
