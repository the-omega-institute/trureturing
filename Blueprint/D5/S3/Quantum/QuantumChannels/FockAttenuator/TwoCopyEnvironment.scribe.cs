using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels.FockAttenuator;
internal sealed class TwoCopyEnvironmentDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual two-copy environment in center and difference modes.",
        H("Balanced two-copy environment"), Blocks(
            Paragraph(Text("Apply the published completed balanced beam splitter to the two-copy environment e2 tensor e2. Its finite Fock expansion has amplitudes sqrt(6)/4 at occupations (4,0) and (0,4), and -1/2 at (2,2). This is a computation of the actual environment vector in the original phase convention.")),
            Node("rotated_environment_expansion", "Exact environment vector",
                "Expand the two creation factors with beamUnitary_fock. Odd difference occupations cancel. The surviving amplitudes have squared moduli 3/8, 1/4 and 3/8."),
            Node("environment_marginal", "Actual reduced environment",
                "The existing purePartialTrace is the norm-convergent sum of column rank-one operators. Only its three nonzero environment slices remain, and their orthogonal center occupations give the diagonal marginal with weights 3/8 at e0, 1/4 at e2 and 3/8 at e4."),
            Node("environment_marginal_le", "Completed-space compression bound",
                "For every complex l2 vector x, the difference between (3/8) times the identity and this marginal has quadratic form (3/8)norm(x)^2-(3/8)|x0|^2-(1/4)|x2|^2-(3/8)|x4|^2. The finite-coordinate Bessel bound makes it nonnegative. Arbitrary coordinates outside 0,2,4 remain in norm(x); there is no input cutoff."),
            Paragraph(Text("This environment computation is a supporting join. The full physical purity bound also requires the four-mode retained-swap identity, its conjugation by the actual two beam splitters, and the completion argument. The environment bound alone does not prove any all-input output-purity or entropy conclusion.")))));
    private static DocumentBlock Node(string name, string title, string text) => Describe.Lean(
        DescribeId.Create("two-copy-environment-" + name.Replace('_', '-')),
        DeclarationHandle.Create("D5/S3/Quantum/QuantumChannels/FockAttenuator/TwoCopyEnvironment." + name),
        H(title), StatementSource.FromLean(), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(text))), DescribeRole.Theorem);
}
