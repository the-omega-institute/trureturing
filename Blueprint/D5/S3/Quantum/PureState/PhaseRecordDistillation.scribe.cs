using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.PureState;

internal sealed class PhaseRecordDistillationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/PureState/PhaseRecordDistillation.";
    private static LibraryNoteRef Distillation => LibraryNoteRef.Create("D5/L/Resource/regula2018oneshotcoherence");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact guessing optimum for finite Fourier character records in dimension N − 1.",
        H("Exact finite Fourier phase memory"),
        Blocks(
            Paragraph(Text("The input ensemble comprises uniformly labeled characters of a finite abelian group G of order N ≥ 2, with nonnegative amplitudes of squared sum one. One common CPTP channel sends the input into a finite quantum memory. The decoder measures only that memory.")),
            Describe.Lean(DescribeId.Create("fourier-memory-translate-optimum"),
                DeclarationHandle.Create(Module + "isGreatest_characterMemory_of_translate"),
                H("A feasible optimal profile realized by translates gives an attained maximum"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Distillation),
                Blocks(Paragraph(Text("If a profile saturates the budget, satisfies the common-slope certificate and is a mixture of translates of the output subset A, the universal upper bound and translate encoder agree. The success set has a greatest element equal to the squared profile value divided by N."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fourier-memory-one-deficit-certificate"),
                DeclarationHandle.Create(Module + "isGreatest_oneDeficit_of_certificate"),
                H("Every saturated certified profile is realizable in dimension N − 1"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Take A = G minus {0}. The translate A + z omits precisely z, so choosing b(z) = 1 − d_z realizes every profile of total mass N − 1. The saturation condition makes b a probability distribution."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fourier-memory-one-deficit-clipped"),
                DeclarationHandle.Create(Module + "isGreatest_oneDeficit_clipped"),
                H("Positive amplitudes give the exact clipped optimum"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Distillation),
                Blocks(Paragraph(Text("Choose c > 0 so the sum of min(1, (tᵢ/c)²) is N − 1. The maximum guessing probability is (sum of tᵢ√dᵢ)²/N. For G = ℤ/3ℤ and amplitudes (12, 4, 3)/13, c = 5/13 gives d = (1, 16/25, 9/25). The two-dimensional optimum is (17/13)²/3 = 289/507."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fourier-memory-one-deficit-zero"),
                DeclarationHandle.Create(Module + "isGreatest_oneDeficit_of_zero"),
                H("A zero amplitude gives the full-carrier success in dimension N − 1"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If t_z = 0, put d_z = 0 and all other dᵢ = 1. The translate weights form a point mass at z, which omits that zero coordinate. The maximum is (sum of the amplitudes)²/N, the full-carrier value."))),
                DescribeRole.Theorem))));
}
