using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Petz;

internal sealed class SpectralKernelDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Petz/SpectralKernel.";
    private const string Summary = "The indexed spectral curvature sums, transfer derivative, permutation invariance, and Dittmann monotonicity criterion.";
    private static readonly (string Name, bool IsDefinition)[] Items =
    {
        ("spectralS", true),
        ("spectralHs", true),
        ("pairTransfer", true),
        ("spectralHs_transfer_hasDerivAt", false),
        ("spectralHs_transfer_deriv_full", false),
        ("spectralHs_perm", false),
        ("residualIndices", true),
        ("spectralHs_transfer_deriv", false),
        ("spectralHs_transfer_monotone", false),
        ("spectralS_eq_spectralHs", false)
    };

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Summary,
        H("SpectralKernel"),
        Blocks(Items.Select(item => Describe.Lean(
            DescribeId.Create("petz-spectralkernel-" + Slug(item.Name)),
            DeclarationHandle.Create(Prefix + item.Name),
            H(item.Name),
            StatementSource.FromAuthor(Disp(F.Id(item.Name.Replace("_", "")))),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(ResultText(item.Name)))),
            item.IsDefinition ? DescribeRole.Definition : DescribeRole.Theorem)).ToArray())));

    private static string Slug(string name) => name.ToLowerInvariant().Replace("_", "-");

    private static string ResultText(string name) => name switch
    {
        "spectralS" => "spectralS is the ordered labelled triple sum of d with its diagonal contribution removed.",
        "spectralHs" => "spectralHs is the corresponding indexed sum of the symmetric kernel with its diagonal contribution removed.",
        "pairTransfer" => "pairTransfer raises one labelled coordinate and lowers another by the transfer parameter.",
        "spectralHs_transfer_hasDerivAt" => "The spectralHs sum has the displayed derivative along every positive labelled pair transfer.",
        "spectralHs_transfer_deriv_full" => "The derivative of a pair transfer is the displayed full first-slot difference.",
        "spectralHs_perm" => "Relabelling the indexed positions leaves the spectralHs sum unchanged.",
        "residualIndices" => "residualIndices contains the labelled positions other than the two transferred coordinates.",
        "spectralHs_transfer_deriv" => "The pair-transfer derivative decomposes into the two positions and all residual positions.",
        "spectralHs_transfer_monotone" => "The four Dittmann inequalities imply a nonnegative derivative when the raised entry is smaller.",
        "spectralS_eq_spectralHs" => "Cyclic symmetrization identifies the ordered spectralS sum with spectralHs on positive spectra.",
        _ => "The named spectral identity holds with exactly the hypotheses and conclusion displayed in the statement."
    };
}
