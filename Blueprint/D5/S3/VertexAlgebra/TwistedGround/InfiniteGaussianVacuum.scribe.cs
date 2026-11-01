using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround;

internal sealed class InfiniteGaussianVacuumDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/TwistedGround/InfiniteGaussianVacuum.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual infinite-mode bilinear Gaussian occupation vacuum equals the exponential of the genuine trace-class trace logarithm.",
        H("Infinite Gaussian vacuum sewing"),
        Blocks(
            Paragraph(Text("Let I be an arbitrary type with decidable equality. Let A and B be InfiniteGaussianFock.Data on I: genuine bounded one-particle operators on complex l2(I), with transpose-symmetric orthonormal matrix coefficients, square-summable matrix entries, and strict operator-norm bounds q_A,q_B<1. No Countable or Nonempty assumption is imposed. The kernel and finite principal blocks are derived from these operators. No commutativity, positivity, conjugation, occupation cutoff, sewing certificate or nonzero-vacuum hypothesis is added.")),
            Paragraph(Text("The native coefficient c_A(d) is InfiniteGaussianFock.coefficient on every finitely supported occupation d. It is the finite polynomial Gaussian coefficient on d's support, with quadratic normalization one half. The weight is the product of the factorials of the occupation entries. The pairing is complex bilinear. This is the classical Gaussian/Fock/Wick vacuum sewing identity; no literature novelty or physical realization is claimed.")),
            Describe.Lean(DescribeId.Create("infinite-gaussian-vacuum-vacuum-trace-log"),
                DeclarationHandle.Create(Prefix + "vacuum_trace_log"),
                H("Actual infinite-mode vacuum trace-log identity"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The series of norms of weight(d)c_A(d)c_B(d), over all occupations on I, is summable. The actual trace series sum_(m>=0) |Tr((AB)^(m+1))/(2(m+1))| is summable. The unconditional occupation sum equals exp(sum_(m>=0) Tr((AB)^(m+1))/(2(m+1))). Here AB is CountableGaussianCutoff.product A B, a genuine trace-class product of the original Hilbert-Schmidt operators. TraceClassPowerSeries.traceLog is defined by those actual positive-power traces, independently of finite cutoffs.")),
                    Paragraph(Text("Apply CountableGaussianCutoff.native_cutoff_bridge to the same A and B. For every finite F subset I, the whole occupation cutoff is exactly the occupation sum of A.block F and B.block F. Symmetry restricts to F, and Data.block_opNorm_le followed by q_lt_one supplies the strict Euclidean norms. FiniteSqueezedVacuum.vacuum_trace_log therefore identifies that cutoff with its finite trace-log exponential. The exact cutoff_power_trace identity replaces each finite matrix power trace by the original trace of the compressed trace-class product. Summability justifies moving the scalar one half inside the finite trace series, giving exactly the denominator 2(m+1).")),
                    Paragraph(Text("Both sides now belong to the same net indexed by Finset I atTop. The whole occupation cutoffs converge to the unconditional native occupation sum. The genuine trace logarithms of the compressed products converge to the original trace logarithm; continuity of complex exp gives convergence of their exponentials. Uniqueness of the limit proves the asserted equality. No enumeration, finite particle number or trace defined by a desired limit enters the argument. Empty finite blocks still contain their vacuum occupation; for empty I the occupation sum and exponential are both one, and zero operators remain in scope."))),
                DescribeRole.Theorem),
            Paragraph(Text("This scalar identity supplies the normalization for infinite Gaussian source sewing. Fixed external occupations, effective source kernels and resolvent limits remain separate obligations. It does not construct the full vertex operator algebra or conformal field theory, string theory, emergent spacetime geometry, unified dynamics or an AdS/CFT realization."))),
        []));
}
