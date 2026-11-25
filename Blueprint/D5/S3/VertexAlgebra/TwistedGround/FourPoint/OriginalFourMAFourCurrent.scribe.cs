using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.FourPoint;

internal sealed class OriginalFourMAFourCurrentDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMAFourCurrent.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Real A/B crossing for four lowest-mode currents",
        H("Fixed-charge coefficients and native slit channels"),
        Blocks(
            Describe.Lean(DescribeId.Create("original-fourm-chart-a-four-current-fixed-charge"),
                DeclarationHandle.Create(Prefix + "chartA_four_current_fixed_charge"),
                H("The A-chart coefficient at fixed charge"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Choose one lowest-mode current colour at each of P, Q, R, S, "
                    + "allowing repeated colours, and an integral charge q of nonnegative energy. For either "
                    + "choice of A lip and real 1/2 < x < 1, take degree one in each of the four independent "
                    + "marks and degree zero in each displacement at the origin. Multiply the physical "
                    + "charge coefficient by the inverse twelfth power of the A period. The result is "
                    + "−i/(x³(1−x)) times the native A slit charge term projected in P, Q, R, S order "
                    + "with projection arguments (2, 2, 0, −1)."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-fourm-chart-b-four-current-fixed-charge"),
                DeclarationHandle.Create(Prefix + "chartB_four_current_fixed_charge"),
                H("The B-chart coefficient at fixed charge"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Use the same marked currents, nonnegative-energy charge and lip choice. "
                    + "For real 0 < x < 1, take the same mark and displacement degrees at the origin in B "
                    + "and use the inverse twelfth power of the B period. The coefficient equals "
                    + "−i(1−x)³/x times the native B slit charge term with projection arguments (2, 2, 0, −1) "
                    + "and current order Q, R, P, S. The scalar includes the relative sign at S."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-fourm-four-current-slit-crossing"),
                DeclarationHandle.Create(Prefix + "four_current_slit_crossing"),
                H("Crossing of the native A and B slit channels"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let the lattice have rank 24, positive definite real Gram form and unit "
                        + "Gram determinant. Put one lowest-mode current of full weight two at each puncture. "
                        + "For all integers m, n, r with m + n + r = 2, every mod-two charge sector and real "
                        + "1/2 < x < 1, the native A slit channel at parameter 1−1/x equals 2¹²x⁴ times "
                        + "the native B slit channel at parameter x. The channel definitions retain their "
                        + "Fourier and quadratic charge signs.")),
                    Paragraph(Text("Sum the two fixed-charge identities over their charge fibres and apply "
                        + "the physical A/B Taylor coefficient comparison. The inverse twelfth power of "
                        + "the A root is x⁶. At total mode two the B lowering cutoff is one, leaving the "
                        + "Laurent factor x⁻⁴. The A Laurent factor and the two fixed-charge scalars then "
                        + "give the stated crossing factor."))),
                DescribeRole.Theorem))));
}
