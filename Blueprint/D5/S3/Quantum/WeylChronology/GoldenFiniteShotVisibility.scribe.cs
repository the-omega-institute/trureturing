using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.WeylChronology;

internal sealed class GoldenFiniteShotVisibilityDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Quantum/WeylChronology/GoldenFiniteShotVisibility.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ramsey contrast maps the golden chronology fringe into the existing symmetric Bernoulli and finite-estimation truth sources.",
        H("Golden Chronology with Visibility and Finite Shots"),
        Blocks(
            Paragraph(Text(
                "This module is an adapter over existing repository owners. It reuses the "
                    + "canonical positive and negative Bool bias laws, their exact total "
                    + "variation and Bhattacharyya formulas, iidPower, the finite-repetition "
                    + "law-kernel theorem, and the Bhattacharyya testing floor. It introduces "
                    + "no parallel probability or divergence definition.")),
            Paragraph(Text(
                "The physical model is the standard contrast-damped Ramsey fringe. A contrast "
                    + "V multiplies the sine signal produced by the already-defined chronology "
                    + "phase. Rapid exchange cooling with trapped ions, Nature Communications "
                    + "15 (2024), reports Ramsey fringes fit by a sinusoid about one half, a "
                    + "96 percent contrast, and binomial state-population confidence intervals. "
                    + "Ramsey contrast decay is also a standard decoherence observable across "
                    + "interferometric platforms. These references motivate the observation "
                    + "model and do not claim experimental realization of the golden sequence.")),
            Paragraph(Text(
                "The adjacent open draft PR #4504 contains a finite Fourier-Magnus matrix "
                    + "commutator and free-Lie interpretation. It is deliberately not copied "
                    + "or imported here. This file treats the stochastic readout of the scalar "
                    + "central phase already present in the current stack.")),
            Describe.Lean(
                DescribeId.Create("visibility-signal"),
                DeclarationHandle.Create(Prefix + "visibilitySignal"),
                H("Contrast-weighted chronology signal"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The signal is V times sin of twice kappa times the existing integer Magnus center."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("visible-chronology-fringe"),
                DeclarationHandle.Create(Prefix + "visibleChronologyFringe"),
                H("Visible plus-port probability"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The observed plus probability is one half plus one half of the contrast-weighted signal."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("chronology-bias"),
                DeclarationHandle.Create(Prefix + "chronologyBias"),
                H("Canonical Bernoulli bias parameter"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The Bernoulli bias is exactly half the visible signal, matching the frozen symmetric Bool law coordinate."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("visible-chronology-law"),
                DeclarationHandle.Create(Prefix + "visibleChronologyLaw"),
                H("One-shot readout law"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "One Ramsey shot is represented by positiveBiasLaw at the chronology bias. No new two-point probability primitive is declared."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("visible-fringe-affine-ideal"),
                DeclarationHandle.Create(Prefix + "visible_chronology_fringe_eq_affine_ideal"),
                H("Contrast is affine damping of the ideal fringe"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The visible fringe equals (1-V)/2 plus V times the ideal pi-over-two analyzer fringe. This is the exact bridge to the preceding physical module."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("visible-law-true"),
                DeclarationHandle.Create(Prefix + "visible_chronology_law_true"),
                H("The true outcome is the visible plus port"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The true mass of the frozen Bool bias law is exactly the visible plus-port probability."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("visible-probability-data"),
                DeclarationHandle.Create(Prefix + "visible_chronology_probability_data"),
                H("Physical contrast gives probability data"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For contrast between zero and one, both Bool masses are nonnegative and sum to one by the frozen closed-range probability-data theorem."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("zero-visibility-collapse"),
                DeclarationHandle.Create(Prefix + "zero_visibility_law_collapse"),
                H("Zero contrast erases chronology"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At zero visibility every word has the same one-shot law, independently of its phase or Magnus center."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("positive-visibility-kernel"),
                DeclarationHandle.Create(Prefix + "positive_visibility_law_kernel"),
                H("Positive contrast preserves the calibrated center kernel"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "With nonzero coupling, positive visibility, and the existing no-alias calibration on both words, equality of one-shot laws is equivalent to equality of their Magnus centers."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("positive-repetition-kernel"),
                DeclarationHandle.Create(Prefix + "positive_repetition_law_kernel"),
                H("Finite repetition never crosses the one-shot kernel"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every positive finite shot count, equality of iid product laws is still exactly center equality. The proof consumes the frozen finite-repetition law-kernel theorem rather than rebuilding product-measure reasoning."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("reversal-total-variation"),
                DeclarationHandle.Create(Prefix + "word_reverse_total_variation"),
                H("Exact one-shot reversal separation"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A word and its reversal have opposite Bernoulli biases. Their one-shot total variation is exactly the absolute contrast-weighted sine signal."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("reversal-bhattacharyya"),
                DeclarationHandle.Create(Prefix + "word_reverse_bhattacharyya"),
                H("Exact reversal affinity"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For contrast strictly below one, the Bhattacharyya affinity is sqrt(1-signal squared), obtained by direct specialization of the frozen symmetric-Bernoulli closed form."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-shot-error-floor"),
                DeclarationHandle.Create(Prefix + "word_reverse_iid_testing_error_floor"),
                H("Necessary finite-shot testing floor"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every decision event on N independent Bool outcomes has total two-hypothesis error at least (1-signal squared)^N divided by two. This is a universal lower bound, not a proposed classifier."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sample-complexity-product"),
                DeclarationHandle.Create(Prefix + "word_reverse_sample_complexity_product"),
                H("Necessary product-form shot count condition"),
                StatementSource.FromLean(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If a test reaches total error eps, then (1-signal squared)^N is at most 2 eps. The result is inherited from the repository's Bhattacharyya sample-complexity owner."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "The result separates deterministic identifiability from statistical "
                    + "certainty. Positive finite repetition preserves the same equality "
                    + "kernel, while its affinity changes with the shot count. Residual "
                    + "displacement, contrast uncertainty, offsets, correlated drift, and "
                    + "constructive upper bounds remain explicit next obligations."))))));
}
