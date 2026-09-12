using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.GoldenPrimeCircle;

internal sealed class GoldenClockLatticeDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Observer/GoldenPrimeCircle/GoldenClockLattice.";

    public DocumentDefinition Create() => DocumentDefinition.Create(
        ScribeNode.Create(
            "Unimodular Fibonacci lattices give an exact, all-resolution bridge "
                + "between nonzero Beatty indices and oriented golden phase windows.",
            H("Golden Clock Lattice"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("golden-clock-lattice-phase"),
                    DeclarationHandle.Create(Prefix + "lattice_phase_identity"),
                    H("The full lattice map preserves the phase residual"),
                    StatementSource.FromAuthor(PhaseFormula()),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "For every natural resolution L and every pair of integers m,k, "
                                + "A=F(L+3), B=F(L+2), C=F(L+1), and d=goldenConj^(L+2). "
                                + "The determinant A*C-B*B is (-1)^L, so the displayed map "
                                + "has an explicit integer inverse.")),
                        Paragraph(Text(
                            "The declaration hits_iff_entry proves both directions: "
                                + "there exists an integer h with 0<(e*alpha-h)/d<1 exactly "
                                + "when e=A*m+B*floor(m*alpha) for a nonzero integer m. "
                                + "The integer h is retained; no scalar observation is "
                                + "silently substituted for the full lattice point.")),
                        Paragraph(Text(
                            "This module proves the Beatty/phase bridge. Identification "
                                + "with actual low-digit Zeckendorf successor events is a "
                                + "separate bridge and is not an assumption of this theorem."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create("golden-clock-relative-resolution"),
                    DeclarationHandle.Create(Prefix + "relativeSeparation_succ"),
                    H("Every cross-resolution separation reflects and contracts"),
                    StatementSource.FromAuthor(SeparationFormula()),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "relativeSeparation(L,r)=d(L)-d(L+r). For every r>0 it is "
                                + "nonzero. The two additional phase-event results "
                                + "hits_two_steps and hits_preceding_boundary give "
                                + "same-parity nesting and the exact F(L+2)-step predecessor.")),
                        Paragraph(Text(
                            "The alternating sign is indexed by observation resolution. "
                                + "It is a contracting eigenmode, without an identification "
                                + "with a physical pendulum or a periodic natural-time orbit."))),
                    DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) { items.Add(Comma); items.Add(Sp); }
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula PhaseFormula() => Disp(Seq(
        Call("residual", Call("lattice", F.Id("L"), F.Id("m"), F.Id("k"))),
        Sp, Eq, Sp,
        Call("signedWidth", F.Id("L")), Sp, Cdot, Sp,
        Call("residual", F.Id("m"), F.Id("k"))));

    private static Formula SeparationFormula() => Disp(Seq(
        Call("relativeSeparation", Seq(F.Id("L"), Plus, F.Id("1")), F.Id("r")),
        Sp, Eq, Sp,
        Call("goldenConj"), Sp, Cdot, Sp,
        Call("relativeSeparation", F.Id("L"), F.Id("r"))));
}
