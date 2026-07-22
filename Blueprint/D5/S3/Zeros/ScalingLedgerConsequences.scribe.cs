using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros;

internal sealed class ScalingLedgerConsequencesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() =>
        DocumentDefinition.Create(ScribeDocument.Create(
            Header(
                "D5/S3/Zeros/ScalingLedgerConsequences",
                "Factor coordinatewise spectral coefficients and prove exact scaling rigidity."),
            H("Coordinatewise Scaling Consequences"),
            Blocks(
                Paragraph(Text(
                    "The three theorems formalize all three mathematical clauses of the coordinatewise scaling definition: the displayed coefficient factorization, absolute unboundedness along multiples of a positive-length address, and invariance of coefficient norm under a unit-modulus rotation. This module does not authorize an address-dependent inverse scaling register, which remains the separate governance clause of the following source theorem.")),
                new DocumentBlock.Describe(
                    DescribeId.Create("half-density-phase-scaling-factorization"),
                    DescribeKind.Theorem,
                    H("Every coefficient has the three exact factors"),
                    DescribeStatement.FromLean(LeanTheorem(
                        "D5/S3/Zeros/ScalingLedgerConsequences.half_density_phase_scaling_factorization")),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "At a spectral parameter with real displacement delta and imaginary coordinate t, the exponential coefficient splits into its half-density, unit-phase, and real-scaling exponentials. The theorem is pointwise at one ledger address and does not assert a statement about an analytically continued sum."))),
                    LatexStatement.Create(@"$$\forall a,\delta,t,\quad Z_{1/2+\delta+it}(a)=e^{-\ell(a)/2}e^{-it\ell(a)}e^{-\delta\ell(a)}$$")),
                new DocumentBlock.Describe(
                    DescribeId.Create("scaling-ledger-unbounded-on-multiples"),
                    DescribeKind.Theorem,
                    H("Off-line scaling is unbounded along address multiples"),
                    DescribeStatement.FromLean(LeanTheorem(
                        "D5/S3/Zeros/ScalingLedgerConsequences.scaling_ledger_unbounded_on_multiples")),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "For any positive-length address and any spectral parameter off the critical line, every real bound is exceeded by the absolute scaling entry at some natural multiple of that address. This proves genuine unboundedness, not merely the linear formula from which it follows."))),
                    LatexStatement.Create(@"$$\ell(a)>0\land\Re(s)\neq\frac12\Rightarrow\forall B\in\mathbb{R},\ \exists m\in\mathbb{N},\ B<\left|\Lambda_s(ma)\right|$$")),
                new DocumentBlock.Describe(
                    DescribeId.Create("unit-rotation-preserves-coefficient-norm"),
                    DescribeKind.Theorem,
                    H("Unit rotations preserve every coefficient norm"),
                    DescribeStatement.FromLean(LeanTheorem(
                        "D5/S3/Zeros/ScalingLedgerConsequences.unit_rotation_preserves_coefficient_norm")),
                    DescribeProvenance.RepoDerived(),
                    Blocks(Paragraph(Text(
                        "Multiplication by any complex factor of norm one leaves the norm of the actual labeled coefficient unchanged. The claim is uniform in the ledger, spectral parameter, and address."))),
                    LatexStatement.Create(@"$$\left\Vert u\right\Vert=1\Rightarrow\left\Vert uZ_s(a)\right\Vert=\left\Vert Z_s(a)\right\Vert$$")))));
}
