using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.QuadraticIdeals;

internal sealed class CubicIntegralLatticeDocument : IScribeDocumentDefinition
{
    private const string Module =
        "D5/S3/Factorization/QuadraticIdeals/CubicIntegralLattice.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An integral trace lattice can be saturated using two Eisenstein witnesses and one coprime scalar.",
        H("Two-prime saturation of integral lattices"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("integral-lattice-discriminant-annihilator"),
                DeclarationHandle.Create(Module + "discr_smul_mem_integral_span"),
                H("The trace discriminant clears every integral element into the lattice"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For an integral rational basis, the trace matrix has integral entries. Cramer’s rule writes the discriminant times an integral element with integer basis coefficients. Closure under products is not assumed for the lattice."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("integral-lattice-two-prime-eisenstein"),
                DeclarationHandle.Create(Module + "integral_span_of_eisenstein_translate"),
                H("The companion and its translate supply global saturation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A clearing scalar puts the integral lattice into the monogenic order. Two Eisenstein conditions remove the denominator primes, and a Bezout identity recovers the original element in the larger lattice."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("integral-lattice-single-denominator"),
                DeclarationHandle.Create(Module + "trace_det_single_denominator"),
                H("One sheared denominator rescales the trace determinant"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The third basis vector may absorb integer combinations of the first two and be divided by P. The corresponding row and column changes multiply the trace determinant by 1/P squared."))),
                DescribeRole.Theorem))));
}
