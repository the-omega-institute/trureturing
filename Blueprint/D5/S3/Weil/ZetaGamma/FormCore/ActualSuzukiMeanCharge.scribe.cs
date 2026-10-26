using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZetaGamma.FormCore;

internal sealed class ActualSuzukiMeanChargeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original actual Suzuki mean",
        H("The original actual Suzuki mean"),
        Blocks(
            Paragraph(Text("Here mu(F) is the integral over the full real line of actualSuzukiEvenBProfile(F), exactly the original H6 mean constraint. It is distinct from the positive-half-line Gaussian central Mellin charge used by the weighted coefficient core. These are source-relative analytic consequences of the existing original physical domain and complete-theta constructions, with no RH-resolution or literature-priority claim.")),
            Describe.Lean(
                DescribeId.Create("actual-suzuki-mean-charge-formula"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiMeanCharge.actual_h6_suzuki_mean_charge_formula"),
                H("The actual original mean has a bounded kernel"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every original H6 source F, the full-line even-B profile is genuinely integrable. Its original mean mu(F) equals the positive-half-line integral of K(t) actualGammaProfile(F,t), with K(t)=(6 exp(-5t/4)-1)/5. The even doubling formula, genuine L1 tail mass and Bochner integral algebra retain the endpoint contribution."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-suzuki-mean-charge-norm"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiMeanCharge.actual_h6_suzuki_mean_charge_norm_le"),
                H("The original mean has an L1 bound"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The kernel lies between -1/5 and 1 on the positive half-line. Consequently the norm of the original mean is at most the L1 norm of the same actual complete-theta profile; no coefficient-charge reinterpretation enters."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-suzuki-mean-charge-real"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiMeanCharge.actual_h6_suzuki_mean_charge_im_eq_zero_of_profile_ae"),
                H("A real actual profile gives a real original mean"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An almost-everywhere real actual complete-theta profile gives a real original mean. The original H6 hypothesis supplies the true integral domain; this theorem does not assume pointwise real behavior at the boundary."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-suzuki-mean-charge-profile-linear"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiMeanCharge.actual_h6_suzuki_mean_charge_linear_of_profile_ae"),
                H("The original mean respects actual profile relations"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For three original H6 sources whose actual complete-theta profiles satisfy the stated almost-everywhere complex linear relation, the original means satisfy that relation. This conditional interface retains its profile hypothesis."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("actual-suzuki-mean-charge-source-linear"),
                DeclarationHandle.Create("D5/S3/Weil/ZetaGamma/FormCore/ActualSuzukiMeanCharge.actual_h6_suzuki_mean_charge_linear"),
                H("The original mean is linear on actual H6 source combinations"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For arbitrary complex a,b and original H6 sources F,G such that H(x)=a F(x)+b G(x) is also original H6, mu(H)=a mu(F)+b mu(G). There is no additional assumption about the profiles. The proof uses the existing almost-everywhere summability of the literal physical-mode series, derives actual fullTheta linearity, and transports it through the genuine physical moments of orders 0 and 5/4. It then reconstructs the original full-line even-B mean from those moments. No stronger endpoint convergence or Gamma Fourier form-domain is inferred."))),
                DescribeRole.Theorem))));
}
