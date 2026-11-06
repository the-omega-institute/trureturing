using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Tomography;

internal sealed class C139FourierOverlapRigidityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Three phase readouts on three spanning probe directions recover a complex cross-term vector.",
        H("C139 Fourier Cross-Term Rigidity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("nine-phase-probes-recover-cross-term"),
                DeclarationHandle.Create(
                    "D5/S3/Quantum/Tomography/C139FourierOverlapRigidity."
                        + "nine_phase_probes_recover_cross_term"),
                H("Nine common unit probes determine the Fourier cross term"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let ζ be a primitive cubic phase, B a three-coordinate Fourier "
                            + "window, and x,y the old and transformed cross-term columns. "
                            + "Assume the nine common probes, formed from the three directions "
                            + "(1,-1,0), (0,1,-1), and (1,-ζ,0) with phases ζ^r, all have "
                            + "zero signed real readout.")),
                    Paragraph(Text(
                        "The proof uses the zero-phase readout to eliminate the real part "
                            + "of each probe value and the first nontrivial cubic phase to eliminate "
                            + "its imaginary part. The first two directions give z0=z1=z2 for "
                            + "z=x-By; the third gives z0=conjugate(ζ)z1. Primitivity forces "
                            + "all three coordinates to vanish, hence x=By. "
                            + "The unitary identity B*B=I then gives y=B*x.")),
                    Paragraph(Text(
                        "This is the finite algebraic content of AURIC C139 continuation "
                            + "Theorem 1.4. It formalizes the cross-term recovery step and does "
                            + "not add any new physical readout, continuity assumption, or "
                            + "unframed projection domain."))),
                DescribeRole.Theorem))));

    private static Formula Apply(string name, params Formula[] arguments)
    {
        var content = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                content.Add(Comma);
                content.Add(Sp);
            }
            content.Add(arguments[index]);
        }
        content.Add(Close);
        return Seq([.. content]);
    }

    private static Formula TheoremFormula() => Disp(Seq(
        Apply("primitiveCubicPhase", F.Id("zeta")), Sp, Land, Sp,
        Apply("fourierWindow", F.Id("B")), Sp, Land, Sp,
        Apply("ninePhaseProbeReadouts", F.Id("zeta"), F.Id("B"), F.Id("x"), F.Id("y")),
        Sp, Rightarrow, RowBreak,
        Apply("crossTermCovariance", F.Id("B"), F.Id("x"), F.Id("y")), Dot));
}
