using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.PureState;

internal sealed class PhaseMemoryOptimizedSeparationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/PureState/PhaseMemoryOptimizedSeparation.";
    private static LibraryNoteRef Distillation => LibraryNoteRef.Create("D5/L/Resource/regula2018oneshotcoherence");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual finite qubit guessing optima for dominant four-state Walsh and Fourier ensembles.",
        H("Optimized Walsh and Fourier phase-memory separation"),
        Blocks(
            Paragraph(Text("Four equiprobable phase signals have a common amplitude vector t with tᵢ > 0, Σᵢtᵢ² = 1 and t₀² ≥ 1/2. One CPTP encoder receives the unknown quantum signal. One four-outcome POVM acts only on its qubit output. Visible encoding knows the label, and a retained classical branch permits conditioned readout. The optimization here ranges over every CPTP encoder to a single qubit and every such POVM.")),
            Describe.Lean(DescribeId.Create("dominant-qubit-phase-memory-upper"),
                DeclarationHandle.Create(Module + "score_le_dominantBound"),
                H("The scalar clipping certificate bounds every qubit strategy"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Distillation),
                Blocks(Paragraph(Text("The scalar M-distillation norm of Regula, Fang, Wang and Adesso gives the optimum of the diagonal-budget relaxation. For M = 2, put r = √(t₁² + t₂² + t₃²) and choose the feasible profile (1,(t₁/r)²,(t₂/r)²,(t₃/r)²). Its profile value is t₀ + r. Squaring and dividing by N = 4 gives the guessing bound for any unit-modulus phase entries. The coherence-distillation fidelity in Theorem 4 of Regula et al. uses division by M and optimizes a different task."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("dominant-walsh-four-optimum"),
                DeclarationHandle.Create(Module + "walsh4_optimum_eq"),
                H("Walsh attains the bound throughout the dominant family"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Distillation),
                Blocks(Paragraph(Text("The common Pauli encoder and its four effects realize (t₀ + r)²/4, which is also the upper bound for every qubit strategy."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("dominant-fourier-four-optimum-iff"),
                DeclarationHandle.Create(Module + "fourier4_optimum_eq_iff"),
                H("Fourier attains the bound exactly when t₁ = t₃"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The symmetric construction attains the bound at t₁ = t₃. If the two amplitudes differ, the real projector Gram required by saturated equality contradicts the virtual Gram. Compactness realizes the supremum, so exclusion of equality forces strict inequality for the actual optimum."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("dominant-phase-matrix-dependence"),
                DeclarationHandle.Create(Module + "phase_matrix_dependence"),
                H("Asymmetric Fourier phases give a strictly smaller optimized score than Walsh"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For t = (4,1,2,2)/5, the squared amplitudes sum to one, t₀² = 16/25 and r = 3/5. Walsh attains ((4/5 + 3/5)²)/4 = 49/100. The same amplitudes give a strictly smaller Fourier optimum.")),
                    Paragraph(Text("The virtual amplitudes before unit normalization are (1,1/3,2/3,2/3). With Fourier rows (1,1,1,1) and (1,i,−1,−i) for labels 0 and 1, the unit Gram entry is (1 + i/9 − 4/9 − 4i/9)/2 = 5/18 − i/6. The imaginary part witnesses the contradiction with a projector Gram."))),
                DescribeRole.Theorem))));
}
