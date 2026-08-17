using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumContext;

internal sealed class CliffordPhaseKernelDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The frequency-48 cosine kernel is constant on extended Clifford phase orbits.",
        H("An Extended Clifford Phase Invariant"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("frequency-48-cosine-kernel-is-clifford-invariant"),
                DeclarationHandle.Create(
                    "D5/S3/QuantumContext/CliffordPhaseKernel."
                    + "clifford_phase_kernel_invariant"),
                H("The frequency-48 cosine kernel is Clifford invariant"),
                StatementSource.FromAuthor(InvarianceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every real phase theta and integer shift k, the kernel "
                            + "2 cos(48 theta) is unchanged after adding k times 2 pi / 24. "
                            + "It remains unchanged when the phase is first reversed, so it is "
                            + "constant under both unitary phase shifts and the antiunitary branch.")),
                    Paragraph(Text(
                        "Pinned Mathlib supplies the exact integer-period theorem "
                            + "Real.cos_add_int_mul_two_pi and the evenness theorem Real.cos_neg. "
                            + "The Lean proof only normalizes the frequency and phase-step factors "
                            + "before applying those two upstream results.")),
                    Paragraph(Text(
                        "This declaration closes only the kernel-invariance sentence of residual "
                            + "remark 27.602, clause 3. It does not formalize the two displayed "
                            + "numerical multisets, prove that those multisets differ, classify the "
                            + "extended Clifford orbits, or certify the stated Galois identity."))),
                DescribeRole.Theorem))));

    private static Formula Kernel(Formula phase) => Seq(
        D(2), Sp, Operatorname, Grp(F.Id("cos")), Open,
        D(4, 8), Sp, phase, Close);

    private static Formula Shifted(Formula phase) => Grp(
        phase, Plus, F.Id("k"), Cdot, Frac, Grp(D(2), Pi), Grp(D(2, 4)));

    private static Formula InvarianceFormula() => Disp(Seq(
        Forall, Sp, Theta, InMacro, Sp, Mathbb, Grp(F.Id("R")), Comma, Sp,
        F.Id("k"), InMacro, Sp, Mathbb, Grp(F.Id("Z")), Comma, Esc,
        Kernel(Shifted(Theta)), Eq, Kernel(Theta), Sp, Land, Sp,
        Kernel(Shifted(Seq(Minus, Theta))), Eq, Kernel(Theta), Dot));
}
