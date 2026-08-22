using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Divergence;

internal sealed class QuantumRelativeEntropyDefectCompositionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Quantum relative-entropy loss telescopes along composable matrix channels.",
        H("Quantum Relative-Entropy Defect Composition"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("quantum-relative-entropy-defect-composition"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Divergence/QuantumRelativeEntropyDefectComposition."
                        + "relative_entropy_defect_composition"),
                H("Quantum relative-entropy defects form an additive channel chain"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The states are positive finite complex matrices of trace one. The "
                            + "channels are completely positive complex-linear maps that preserve "
                            + "the trace, and composition is constructed in that channel class.")),
                    Paragraph(Text(
                        "Relative entropy is the real trace expression Re Tr(rho (log rho - "
                            + "log sigma)), using the pinned continuous-functional-calculus "
                            + "matrix logarithm. The defect is its value before the channel minus "
                            + "its value after the channel.")),
                    Paragraph(Text(
                        "Expanding the three defects cancels the intermediate matrix-state "
                            + "relative entropy and gives the displayed identity."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula sourceState = Seq(Rho, Comma, Sp, SigmaLower, Sp, InMacro, Sp,
            Operatorname, Grp(F.Id("DensityState")), Open, F.Id("a"), Close);
        Formula firstChannel = Seq(Phi, Sp, InMacro, Sp,
            Operatorname, Grp(F.Id("QuantumChannel")), Open,
            F.Id("a"), Comma, Sp, F.Id("b"), Close);
        Formula secondChannel = Seq(Psi, Sp, InMacro, Sp,
            Operatorname, Grp(F.Id("QuantumChannel")), Open,
            F.Id("b"), Comma, Sp, F.Id("c"), Close);

        return Disp(Seq(
            Forall, Sp, sourceState, Comma, Sp, firstChannel, Comma, Sp,
            secondChannel, Comma, Sp,
            DeltaLower, Underscore, Grp(Psi, Circ, Phi),
            Open, Rho, Comma, Sp, SigmaLower, Close, Sp, Eq, Sp,
            DeltaLower, Underscore, Grp(Phi),
            Open, Rho, Comma, Sp, SigmaLower, Close, Sp, Plus, Sp,
            DeltaLower, Underscore, Grp(Psi), Open,
            Phi, Rho, Comma, Sp, Phi, SigmaLower, Close, Dot));
    }
}
