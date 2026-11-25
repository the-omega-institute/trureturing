using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.PureState;

internal sealed class DistillationProfileDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/PureState/DistillationProfile.";
    private static LibraryNoteRef Distillation => LibraryNoteRef.Create("D5/L/Resource/regula2018oneshotcoherence");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Clipping solves the scalar optimization for finite phase-memory profiles.",
        H("The clipped profile and its certificate"),
        Blocks(
            Paragraph(Text("A profile d is feasible if every dᵢ lies in [0,1] and the sum of the dᵢ is at most M. Its value is the sum of tᵢ√dᵢ. For nonnegative amplitudes and positive integer M, the substitution xᵢ = √dᵢ turns this into the dual maximization in Regula, Fang, Wang and Adesso, supplement Eq. (S12). Their Theorem 2 evaluates the optimum.")),
            Describe.Lean(DescribeId.Create("distillation-profile-optimality-certificate"),
                DeclarationHandle.Create(Module + "profileValue_le_of_certificate"),
                H("A saturated profile with a common slope below the cap is optimal"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Distillation),
                Blocks(Paragraph(Text("Write tᵢ = √dᵢ rᵢ with rᵢ at least c ≥ 0 and rᵢ = c whenever dᵢ < 1. For a competitor v, the inequality 2√(dᵢvᵢ) ≤ dᵢ + vᵢ reduces the comparison to a linear one. The common coefficient c is controlled by the total budget. The remaining coefficient rᵢ − c can contribute only where dᵢ = 1, where vᵢ is already capped."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("distillation-clipped-profile-certificate"),
                DeclarationHandle.Create(Module + "clippedProfile_certificate"),
                H("A clipped squared amplitude satisfies the slope conditions"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Distillation),
                Blocks(Paragraph(Text("For c > 0 take dᵢ = min(1, (tᵢ/c)²) and rᵢ = max(tᵢ,c). The constraints on individual coordinates and the factorization hold at every nonnegative amplitude, including tᵢ = 0. Supplement Eq. (S13) gives the corresponding clipped witness in the dual norm variables."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("distillation-clipped-profile-budget"),
                DeclarationHandle.Create(Module + "exists_clippedProfile_sum"),
                H("Clipping can exhaust any positive budget up to the support size"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Distillation),
                Blocks(Paragraph(Text("For a real budget M within this range, vary 1/c from zero to a finite value that saturates every positive coordinate. The sum of the clipped squares is continuous and reaches both endpoints. A positive budget forces the chosen reciprocal threshold to be positive."))),
                DescribeRole.Theorem))));
}
