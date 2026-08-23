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
        Formula a = F.Id("a");
        Formula b = F.Id("b");
        Formula c = F.Id("c");
        Formula carrier = Seq(Operatorname, Grp(F.Id("Type")));
        Formula stateA = Seq(
            Operatorname, Grp(F.Id("DensityState")), Open, a, Close);
        Formula channelAB = Seq(
            Operatorname, Grp(F.Id("QuantumChannel")), Open,
            a, Comma, Sp, b, Close);
        Formula channelBC = Seq(
            Operatorname, Grp(F.Id("QuantumChannel")), Open,
            b, Comma, Sp, c, Close);
        Formula composition = Seq(
            Operatorname, Grp(F.Id("comp")), Open,
            Psi, Comma, Sp, Phi, Close);
        Formula mappedRho = Seq(
            Operatorname, Grp(F.Id("mapState")), Open,
            Phi, Comma, Sp, Rho, Close);
        Formula mappedSigma = Seq(
            Operatorname, Grp(F.Id("mapState")), Open,
            Phi, Comma, Sp, SigmaLower, Close);
        Formula compositeDefect = Seq(
            Operatorname, Grp(F.Id("relativeEntropyDefect")), Open,
            composition, Comma, Sp, Rho, Comma, Sp, SigmaLower, Close);
        Formula firstDefect = Seq(
            Operatorname, Grp(F.Id("relativeEntropyDefect")), Open,
            Phi, Comma, Sp, Rho, Comma, Sp, SigmaLower, Close);
        Formula secondDefect = Seq(
            Operatorname, Grp(F.Id("relativeEntropyDefect")), Open,
            Psi, Comma, Sp, mappedRho, Comma, Sp, mappedSigma, Close);

        return Disp(Seq(
            Forall, Sp, a, Comma, Sp, b, Comma, Sp, c, Colon, Sp, carrier,
            Comma, Esc,
            OpenBracket, Operatorname, Grp(F.Id("Fintype")), Open, a, Close,
            CloseBracket, Comma, Sp,
            OpenBracket, Operatorname, Grp(F.Id("DecidableEq")), Open, a, Close,
            CloseBracket, Comma, Esc,
            OpenBracket, Operatorname, Grp(F.Id("Fintype")), Open, b, Close,
            CloseBracket, Comma, Sp,
            OpenBracket, Operatorname, Grp(F.Id("DecidableEq")), Open, b, Close,
            CloseBracket, Comma, Esc,
            OpenBracket, Operatorname, Grp(F.Id("Fintype")), Open, c, Close,
            CloseBracket, Comma, Sp,
            OpenBracket, Operatorname, Grp(F.Id("DecidableEq")), Open, c, Close,
            CloseBracket, Comma, Esc,
            Phi, Colon, Sp, channelAB, Comma, Sp,
            Psi, Colon, Sp, channelBC, Comma, Esc,
            Rho, Comma, Sp, SigmaLower, Colon, Sp, stateA, Comma, Esc,
            compositeDefect, Sp, Eq, Sp,
            firstDefect, Sp, Plus, Sp, secondDefect, Dot));
    }
}
