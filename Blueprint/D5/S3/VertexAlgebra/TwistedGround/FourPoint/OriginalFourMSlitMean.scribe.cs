using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround.FourPoint;

internal sealed class OriginalFourMSlitMeanDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/VertexAlgebra/TwistedGround/FourPoint/OriginalFourMSlitMean.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Native signed mean on the Euler slit",
        H("Principal branch and Taylor centre"),
        Blocks(
            Describe.Lean(DescribeId.Create("fourm-slit-mean"),
                DeclarationHandle.Create(Prefix + "slitMean"),
                H("Principal half-current source"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Write b(u) = 1−u. For the negative sign use h(e,u,r) = 1−r−u, "
                    + "and for the positive sign use h(e,u,r) = 1−(1−r)u. "
                    + "The source is b(u)⁻¹ times the principal inverse square root of h(e,u,r)/b(u)."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("fourm-slit-mean-source-mode"),
                DeclarationHandle.Create(Prefix + "slitMean_eq_sourceMode"),
                H("Agreement with the literal source"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For either sign and ‖u‖ + ‖r‖ < 1, the principal expression "
                    + "equals the signed source-mode generator."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fourm-slit-mean-analytic"),
                DeclarationHandle.Create(Prefix + "slitMean_joint_analytic"),
                H("Joint holomorphic germ"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If 1−r lies in the principal slit plane, the source is jointly "
                    + "analytic at (0,r) in the external variable and radial parameter. "
                    + "At u = 0 the branch argument is 1−r for the negative sign and 1 for the positive sign."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fourm-slit-mean-weighted-positive"),
                DeclarationHandle.Create(Prefix + "slitMean_weighted_re_pos"),
                H("Positive real part of the regularizing factor"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("On the Euler slit, h times the source at u = 0 has positive real part. "
                    + "The negative sign gives the principal square root of 1−r and the positive sign gives 1."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fourm-slit-period-correction-analytic"),
                DeclarationHandle.Create(Prefix + "slitPeriodCorrection_analyticOnNhd"),
                H("Analytic period correction"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For the Euler period P, the correction r(1−r)P′(r)/P(r) is analytic "
                    + "in a neighborhood of every point of the Euler slit, where P is nonzero."))),
                DescribeRole.Theorem))));
}
