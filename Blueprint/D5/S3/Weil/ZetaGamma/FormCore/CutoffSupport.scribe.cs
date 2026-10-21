using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaGamma.FormCore;

internal sealed class CutoffSupportDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For positive epsilon the constructed eta has topological support in Icc(-a+epsilon,a-epsilon), strictly inside the original open interval, and is smooth with compact support. Multiplication by eta preserves inward support for the measurable representative; the physical L2 error tends to zero by dominated convergence. Empty or nonpositive windows are not excluded by an added a>0 hypothesis.",
        H("Actual Gamma form core: CutoffSupport"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("gamma-form-core-cutoffsupport-actualcutoffeta-mul-eq-sub-mask"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/CutoffSupport.actualCutoffEta_mul_eq_sub_mask"),
                H("actualCutoffEta mul eq sub mask"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For positive epsilon the constructed eta has topological support in Icc(-a+epsilon,a-epsilon), strictly inside the original open interval, and is smooth with compact support. Multiplication by eta preserves inward support for the measurable representative; the physical L2 error tends to zero by dominated convergence. Empty or nonpositive windows are not excluded by an added a>0 hypothesis."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-cutoffsupport-actualcutoffeta-mul-tsupport-subset-icc"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/CutoffSupport.actualCutoffEta_mul_tsupport_subset_Icc"),
                H("actualCutoffEta mul tsupport subset Icc"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For positive epsilon the constructed eta has topological support in Icc(-a+epsilon,a-epsilon), strictly inside the original open interval, and is smooth with compact support. Multiplication by eta preserves inward support for the measurable representative; the physical L2 error tends to zero by dominated convergence. Empty or nonpositive windows are not excluded by an added a>0 hypothesis."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-cutoffsupport-actualcutoffeta-mul-hascompactsupport"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/CutoffSupport.actualCutoffEta_mul_hasCompactSupport"),
                H("actualCutoffEta mul hasCompactSupport"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For positive epsilon the constructed eta has topological support in Icc(-a+epsilon,a-epsilon), strictly inside the original open interval, and is smooth with compact support. Multiplication by eta preserves inward support for the measurable representative; the physical L2 error tends to zero by dominated convergence. Empty or nonpositive windows are not excluded by an added a>0 hypothesis."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-cutoffsupport-actualcutoffeta-mul-sub-mass-tendsto-zero"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/CutoffSupport.actualCutoffEta_mul_sub_mass_tendsto_zero"),
                H("actualCutoffEta mul sub mass tendsto zero"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For positive epsilon the constructed eta has topological support in Icc(-a+epsilon,a-epsilon), strictly inside the original open interval, and is smooth with compact support. Multiplication by eta preserves inward support for the measurable representative; the physical L2 error tends to zero by dominated convergence. Empty or nonpositive windows are not excluded by an added a>0 hypothesis."))),
                DescribeRole.Theorem))));
}
