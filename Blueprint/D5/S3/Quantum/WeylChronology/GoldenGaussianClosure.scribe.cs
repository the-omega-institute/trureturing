using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.WeylChronology;

internal sealed class GoldenGaussianClosureDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Quantum/WeylChronology/GoldenGaussianClosure.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Gaussian endpoint closure connects actual displacement integrals to the existing Ramsey and finite-shot interfaces.",
        H("GoldenGaussianClosure"),
        Blocks(
            Paragraph(Text("The source is a candidate proof. Exact statements and kernel status belong to the Lean producer. No hardware experiment or metrological advantage is asserted.")),
            Describe.Lean(
                DescribeId.Create("compensationphase"),
                DeclarationHandle.Create(Prefix + "compensationPhase"),
                H("compensationPhase"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An erroneous single Weyl compensator creates the symplectic phase X dy - Y dx, where X and Y are the count-dependent endpoint."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("residualcompensatedword"),
                DeclarationHandle.Create(Prefix + "residualCompensatedWord"),
                H("residualCompensatedWord"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This is the literal existing word action followed by D(-X+dx,-Y+dy). The error model fixes the composition order and its phase convention."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("compensationoverlap"),
                DeclarationHandle.Create(Prefix + "compensationOverlap"),
                H("compensationOverlap"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The residual factor contains both the computed Gaussian overlap and the compensator cocycle. Reducing it to a real visibility alone would discard phase information."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("compensatedgaussianexpectation"),
                DeclarationHandle.Create(Prefix + "compensatedGaussianExpectation"),
                H("compensatedGaussianExpectation"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The normalized expectation is taken directly on the Gaussian seed after the actual erroneous compensator."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("residual-compensated-word-normal-form"),
                DeclarationHandle.Create(Prefix + "residual_compensated_word_normal_form"),
                H("residual compensated word normal form"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The remaining displacement is (dx,dy), while the full phase is a b m plus X dy - Y dx. The latter is linear in compensation errors for a fixed endpoint."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("compensated-gaussian-expectation-factorizes"),
                DeclarationHandle.Create(Prefix + "compensated_gaussian_expectation_factorizes"),
                H("compensated gaussian expectation factorizes"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual normalized integral factors into the existing chronology phase and the residual overlap. The expression is proved from the concrete action and integral linearity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("compensation-overlap-exact"),
                DeclarationHandle.Create(Prefix + "compensation_overlap_exact"),
                H("compensation overlap exact"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Positive-width Gaussian integration evaluates the residual factor as exp(i eta) exp(-cost). No complex overlap is supplied as a hypothesis."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("compensation-overlap-contracts"),
                DeclarationHandle.Create(Prefix + "compensation_overlap_contracts"),
                H("compensation overlap contracts"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The phase has unit norm and the derived Gaussian overlap is contractive."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gaussianclosurefringe"),
                DeclarationHandle.Create(Prefix + "gaussianClosureFringe"),
                H("gaussianClosureFringe"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The existing overlap-sensitive Ramsey readout is applied to the derived residual factor. Its coupling is a b/2 for count-compensated interference."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("gaussianclosurecalibration"),
                DeclarationHandle.Create(Prefix + "gaussianClosureCalibration"),
                H("gaussianClosureCalibration"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The existing record is instantiated with visibility V exp(-cost), phase offset eta, coupling a b/2, baseline one half, and zero additive closure residual."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("gaussian-closure-fringe-eq-calibration"),
                DeclarationHandle.Create(Prefix + "gaussian_closure_fringe_eq_calibration"),
                H("gaussian closure fringe eq calibration"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This exact identity connects the physical overlap readout to the existing calibration owner, with no replacement noise model."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gaussian-closure-fringe-mem-unit"),
                DeclarationHandle.Create(Prefix + "gaussian_closure_fringe_mem_unit"),
                H("gaussian closure fringe mem unit"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The derived overlap and visibility between zero and one yield a valid probability."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gaussian-closure-budget-le"),
                DeclarationHandle.Create(Prefix + "gaussian_closure_budget_le"),
                H("gaussian closure budget le"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The total deviation budget is at most abs(V)/2 times (cost + abs(eta)). Quadratic overlap attenuation and first-order geometric phase are retained separately."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gaussian-closure-finite-shot-bound"),
                DeclarationHandle.Create(Prefix + "gaussian_closure_finite_shot_bound"),
                H("gaussian closure finite shot bound"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A nominal gap exceeding both explicit displacement budgets certifies a margin delta. For each fixed pair of acquired laws, the existing independent-shot optimal equal-prior Bayes risk is bounded by (sqrt(1-delta squared)) to the N divided by two. This does not construct a single minimax classifier for all unknown calibration records."))),
                DescribeRole.Theorem))));
}
