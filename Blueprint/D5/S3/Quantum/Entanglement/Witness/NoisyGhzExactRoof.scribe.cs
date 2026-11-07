using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.Witness;

internal sealed class NoisyGhzExactRoofDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/Witness/NoisyGhzExactRoof.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Independent-coordinate phase cancellation and exact noisy-GHZ parameter checkpoints.",
        H("Noisy GHZ finite phase characters"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("noisy-ghz-phase-character-sum"),
                DeclarationHandle.Create(Prefix + "phaseCharacter_sum"),
                H("Independent-coordinate character orthogonality"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every natural d and every coefficient vector v : Fin d → ZMod 3, "
                    + "the sum of phaseCharacter v over the full independent phase group "
                    + "Fin d → ZMod 3 is 3^d when v is zero and zero otherwise. The proof "
                    + "factors the finite sum into one coordinate at a time and applies the "
                    + "primitive standard additive character sum on ZMod 3. This is the "
                    + "arbitrary-dimensional cancellation needed for the full matrix witness."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("noisy-ghz-pair-phase-sum"),
                DeclarationHandle.Create(Prefix + "pair_phase_sum"),
                H("Ordered-pair phase cancellation"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The coefficient vector for an ordered pair (i,j) is the coordinate "
                    + "indicator of i minus the coordinate indicator of j. It is zero exactly "
                    + "when i=j, so averaging its phase character over independent coordinates "
                    + "keeps precisely the diagonal terms. No claim that scalar differences "
                    + "of indices are distinct modulo three is used."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("noisy-ghz-qutrit-arithmetic"),
                DeclarationHandle.Create(Prefix + "qutrit_source_arithmetic"),
                H("Exact qutrit parameter checkpoint"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At n=d=3 the checked source parameters are M=27, K=3, R=21, "
                    + "k=8/9 and p_W=3/4. The same module evaluates the exact two-mean "
                    + "formula at f=23/36 and y=11/12 to (14−√115)/27."))),
                DescribeRole.Theorem))));
}
