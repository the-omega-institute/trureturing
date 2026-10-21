using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaGamma.FormCore;

internal sealed class MollifierDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Start from a measurable L2 representative with compact support in Icc(-a+eta,a-eta), eta>0, and finite actual-Gamma energy. Convolve with the actual normalized ContDiffBump approximate identity. Its Fourier multiplier is bounded by one and tends to one; dominated convergence against mass and the actual digamma-weighted spectral measure proves joint mass-plus-energy convergence. Small outer bump radius keeps support strictly within Ioo(-a,a).",
        H("Actual Gamma form core: Mollifier"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("gamma-form-core-mollifier-corel2mass"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/Mollifier.coreL2Mass"),
                H("coreL2Mass"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Start from a measurable L2 representative with compact support in Icc(-a+eta,a-eta), eta>0, and finite actual-Gamma energy. Convolve with the actual normalized ContDiffBump approximate identity. Its Fourier multiplier is bounded by one and tends to one; dominated convergence against mass and the actual digamma-weighted spectral measure proves joint mass-plus-energy convergence. Small outer bump radius keeps support strictly within Ioo(-a,a)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("gamma-form-core-mollifier-exists-smooth-actual-gamma-approximation-of-inward-support"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/Mollifier.exists_smooth_actual_gamma_approximation_of_inward_support"),
                H("exists smooth actual gamma approximation of inward support"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Start from a measurable L2 representative with compact support in Icc(-a+eta,a-eta), eta>0, and finite actual-Gamma energy. Convolve with the actual normalized ContDiffBump approximate identity. Its Fourier multiplier is bounded by one and tends to one; dominated convergence against mass and the actual digamma-weighted spectral measure proves joint mass-plus-energy convergence. Small outer bump radius keeps support strictly within Ioo(-a,a)."))),
                DescribeRole.Theorem))));
}
