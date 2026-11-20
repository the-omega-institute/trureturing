using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.PeriodicMPS.Reconstruction;

internal sealed class SevenSiteCriticalCharZeroDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/PeriodicMPS/Reconstruction/SevenSiteCriticalCharZero";
    private const string Title = "Differentiable cover of the seven-site critical slice";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        Title,
        H(Title),
        Blocks(
            Describe.Lean(DescribeId.Create("sevensitecriticalcharzero-complex-critical-quotients"),
                DeclarationHandle.Create(Module + ".complex_critical_quotients"),
                H("Relatively prime complex cofactor quotients"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A full-degree modular resultant certificate lifts through the Gaussian integers to complex quotients of both cofactors by the mixed-trace coordinate. Both quotients have total degree forty-six, the first is nonzero, and the two are relatively prime."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("sevensitecriticalcharzero-seven-site-critical-slice-cover"),
                DeclarationHandle.Create(Module + ".seven_site_critical_slice_cover"),
                H("Countable differentiable cover"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Real points of the five-coordinate slice at which the mixed trace is nonzero and every deleted-row cofactor vanishes lie in a countable union of images of subsets of three-dimensional real space. Each map is differentiable on its corresponding subset. At these points the first two cofactors force both relatively prime complex quotients to vanish."))),
                DescribeRole.Theorem))));
}
