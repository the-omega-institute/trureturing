using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.ForwardKernel;

internal sealed class FiniteMellinDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/ForwardKernel/FiniteMellin.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Bounded intervals of the original adjoint contribute entire Mellin corrections.",
        H("Finite Mellin corrections"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("compact-mellin-entire"),
                DeclarationHandle.Create(Prefix + "compact_mellin_entire"),
                H("An integrable density on positive compact centers"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If a>0 and f is complex-valued and integrable on [a,b], "
                    + "then the integral of f(x)*x^(-s-1) over that interval is entire "
                    + "in s. Extend f by zero outside [a,b]. This integrable extension "
                    + "vanishes near zero and at infinity, so Mathlib's "
                    + "mellin_differentiableAt_of_isBigO_rpow applies at every complex "
                    + "parameter. Composing with negation gives the stated exponent."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("adjoint-kernel-entire"),
                DeclarationHandle.Create(Prefix + "adjointKernel_entire"),
                H("Entire dependence at a fixed adjoint point"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For x0>=4 and every real t, the actual adjoint q_s(t) is entire "
                    + "in s. Its center integral has compact support in [x0,max(x0,t)], "
                    + "so the compact Mellin theorem applies to the original price kernel."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("adjoint-kernel-finite-integral-entire"),
                DeclarationHandle.Create(Prefix + "adjointKernel_finite_integral_entire"),
                H("A bounded interval of adjoint points"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For 4<=x0<=b, the integral of q_s(t) over [1,b] is entire. "
                    + "All its center integrals lie in [x0,b]. The original kernel "
                    + "lies between zero and one, and the Mellin powers are uniformly "
                    + "bounded on compact parameter sets. These bounds allow "
                    + "integration of the entire parameter family."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-correction-entire"),
                DeclarationHandle.Create(Prefix + "finiteCorrection_entire"),
                H("The bounded signed correction"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Subtract n^(-s-1/2)/2 from q_s(n) in the finite complete "
                    + "Mangoldt sum up to floor(b), and subtract the corresponding "
                    + "Lebesgue integral on [1,b]. The resulting correction is entire. "
                    + "The zero index has zero Mangoldt weight; every positive base "
                    + "in the finite sum and integral has an entire complex power."))),
                DescribeRole.Theorem))));
}
