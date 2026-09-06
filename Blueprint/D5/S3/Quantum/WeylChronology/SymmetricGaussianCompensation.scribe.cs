using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.WeylChronology;

internal sealed class SymmetricGaussianCompensationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/WeylChronology/SymmetricGaussianCompensation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A source-linked control and shared-decision construction with explicit error assumptions.",
        H("SymmetricGaussianCompensation"),
        Blocks(
            Paragraph(Text("The exact statements and proof status are owned by Lean. This is a candidate source without a local compilation verdict, and it does not report a hardware experiment or independent model review.")),
            Describe.Lean(
                DescribeId.Create("splitPhase"),
                DeclarationHandle.Create(Prefix + "splitPhase"),
                H("splitPhase"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact residual cocycle retains both differential half-error and cross-error terms."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("splitCompensatedWord"),
                DeclarationHandle.Create(Prefix + "splitCompensatedWord"),
                H("splitCompensatedWord"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A literal pre-compensator, the existing runWord action, and a literal post-compensator. Their errors are initially independent."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("split-compensation-normal-form"),
                DeclarationHandle.Create(Prefix + "split_compensation_normal_form"),
                H("split compensation normal form"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The final displacement is the sum of the two errors. Its extra phase is computed rather than dropped."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("matched-split-phase-zero"),
                DeclarationHandle.Create(Prefix + "matched_split_phase_zero"),
                H("matched split phase zero"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Equal realized half-errors cancel the extra real cocycle for every endpoint without a small-error assumption."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("universal-split-cancellation-iff-matched"),
                DeclarationHandle.Create(Prefix + "universal_split_cancellation_iff_matched"),
                H("universal split cancellation iff matched"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Matching is also necessary for cancellation at all real endpoints within this two-half architecture. This is not a converse for a single fixed endpoint."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("symmetricCompensatedWord"),
                DeclarationHandle.Create(Prefix + "symmetricCompensatedWord"),
                H("symmetricCompensatedWord"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Each compensator uses half of the same total residual displacement."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("symmetric-compensation-phase-free"),
                DeclarationHandle.Create(Prefix + "symmetric_compensation_phase_free"),
                H("symmetric compensation phase free"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The useful chronology phase survives while the endpoint-dependent nuisance phase cancels exactly."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("symmetricGaussianExpectation"),
                DeclarationHandle.Create(Prefix + "symmetricGaussianExpectation"),
                H("symmetricGaussianExpectation"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The proposed control is evaluated by an actual normalized Gaussian integral, reusing the existing seed and mass."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("symmetric-gaussian-expectation-exact"),
                DeclarationHandle.Create(Prefix + "symmetric_gaussian_expectation_exact"),
                H("symmetric gaussian expectation exact"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The expectation equals exp(iabm) exp(-Q). There is no compensator-induced phase when the halves match."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("symmetricClosureFringe"),
                DeclarationHandle.Create(Prefix + "symmetricClosureFringe"),
                H("symmetricClosureFringe"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The already-owned overlap-sensitive Ramsey readout is used with the evaluated Gaussian residual."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("symmetric-closure-fringe-eq-visible"),
                DeclarationHandle.Create(Prefix + "symmetric_closure_fringe_eq_visible"),
                H("symmetric closure fringe eq visible"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Centered Gaussian mismatch acts as a real attenuation V exp(-Q) for this symmetric control."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("symmetric-closure-quadratic-budget"),
                DeclarationHandle.Create(Prefix + "symmetric_closure_quadratic_budget"),
                H("symmetric closure quadratic budget"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The probability-level closure budget is at most abs(V) Q/2; the one-sided endpoint phase is absent."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("symmetric-uncertainty-budget"),
                DeclarationHandle.Create(Prefix + "symmetric_uncertainty_budget"),
                H("symmetric uncertainty budget"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A contrast interval and a quadratic residual-cost ceiling give one deterministic probability envelope."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("symmetric-fringe-strict"),
                DeclarationHandle.Create(Prefix + "symmetric_fringe_strict"),
                H("symmetric fringe strict"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Visibility strictly below one guarantees that the acquired count probability is in the open unit interval."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("symmetricProbability"),
                DeclarationHandle.Create(Prefix + "symmetricProbability"),
                H("symmetricProbability"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A valid parameter for the existing Binomial count measure, with its physical bounds proved."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("one-test-for-all-symmetric-acquisitions"),
                DeclarationHandle.Create(Prefix + "one_test_for_all_symmetric_acquisitions"),
                H("one test for all symmetric acquisitions"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Choose one count event first. It bounds risk for every pair of fixed acquisitions satisfying the visibility and closure envelopes. Matched pre/post errors within each run remain a physical premise."))),
                DescribeRole.Theorem))));
}
