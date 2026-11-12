using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumChannels.ProjectionDiagnostics;

internal sealed class CyclicMonitoredPowerBoundDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual cyclic monitored operator has a strictly contracting power.",
        H("Cyclic monitored power contraction"),
        Blocks(Describe.Lean(
            DescribeId.Create("cyclic-monitored-power-contraction"),
            DeclarationHandle.Create("D5/S3/QuantumChannels/ProjectionDiagnostics/CyclicMonitoredPowerBound.cyclic_power_contraction"),
            H("A strict power bound derived from actual cyclicity"),
            StatementSource.FromAuthor(Disp(Seq(
                Exists, Sp, F.Id("N"), Ge, D(1), Comma, Quad,
                Exists, Sp, F.Id("q"), Comma, Sp,
                D(0), Le, Sp, F.Id("q"), Lt, D(1), Comma, Quad, Sp,
                new Formula.Norm(Seq(F.Id("T"), Underscore, F.Id("C"),
                    Caret, F.Id("N"))), Le, Sp, F.Id("q")))),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "For every finite dimensional complex Hilbert space, every unitary U and every "
                + "unit vector v, C is the actual span of U^n v, and T_C is the restriction of "
                + "(I-P_v)U. No stability or independent cyclicity hypothesis is imposed. "
                + "The actual cyclic future-kernel theorem proves zero dark space. "
                + "Orthogonal coordinates carry T_C and the actual click restriction to a "
                + "conservative singleton instrument. FiniteDetectionSurvivalLimit.dark_block_contraction "
                + "then supplies the strict gap; its estimate is reused directly. "
                + "The chosen N is dim C and q is the norm of T_C^N. "
                + "This proves the registered contraction witness. It does not assert the infinite "
                + "weighted return identity or identify dim C with occupied spectral cardinality. "
                + "The complete monitored-return endpoint is classical, as in Grunbaum, Velazquez, "
                + "Werner and Werner, arXiv:1202.3903v3, Theorem 2."))),
            DescribeRole.Theorem))));
}
