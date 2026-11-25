using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class BKMRankOneInactiveRigidityDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Recovery/BKMRankOneInactiveRigidity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Active and inactive blocks at zero actual BKM gap for a rank-one observable.",
        H("Rank-one BKM gap and the active retained span"), Blocks(
            Describe.Lean(DescribeId.Create("bkm-gap-rank-one-active-block"),
                DeclarationHandle.Create(Module + "bkmGap_rankOne_eq_zero_iff_activeBlock"),
                H("The faithful auxiliary density on the active span"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let A be a positive definite joint matrix, S its actual retained partial "
                    + "trace, and w a unit retained vector. For every distinct eigenvalue of S, "
                    + "take the component of w in its full eigenspace. The projection P onto the "
                    + "span of these components is the sum of their normalized outer products, "
                    + "with a zero component contributing zero. Let Q be its complement and B "
                    + "the joint relative density formed with the lifted inverse square root of S. "
                    + "The BKM gap for the rank-one projection of w vanishes exactly when B is "
                    + "the sum of P tensored with a unique positive definite trace-one auxiliary "
                    + "matrix and the compression of B by the lift of Q. This compression has "
                    + "actual retained partial trace Q and is positive definite on the range "
                    + "of the lifted Q.")),
                Paragraph(Text(
                    "Use the grouped modular equality criterion on every auxiliary matrix slice. "
                    + "The sum of the ratio groups gives scalar action on w. If some spectral "
                    + "component fails to have this same scalar action, take a largest "
                    + "eigenvalue with a nonzero error and divide it by the smallest eigenvalue "
                    + "with a nonzero component of w. In the test for this ratio, higher errors "
                    + "vanish and smaller eigenvalues cannot pair with an occupied component. "
                    + "The coefficient of the remaining error is the squared norm at the "
                    + "smallest occupied eigenvalue, which is positive. This argument permits "
                    + "repeated eigenvalues and colliding ratios. Compress B along the isometry "
                    + "that tensors each auxiliary vector with w to obtain the faithful active "
                    + "density. The actual partial trace of B is the identity, giving the two "
                    + "trace conditions. The nonzero projection P makes the auxiliary factor "
                    + "unique. Conversely the grouped ratio matrices are supported on P, so "
                    + "the two-block form commutes with every lifted ratio matrix."))),
                DescribeRole.Theorem))));
}
