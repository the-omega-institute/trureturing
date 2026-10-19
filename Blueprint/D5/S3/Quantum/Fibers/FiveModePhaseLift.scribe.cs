using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fibers;

internal sealed class FiveModePhaseLiftDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A phase-sensitive projector separates a convex segment invisible to the actual real menu and the odd-rejection branch.",
        H("Five-Mode Phase Lift"), Blocks(
            Paragraph(Text("Use the coordinate order of FiveModeRealResponse and ReadoutInstrument. The rays have coordinate 2 equal to one, coordinate 4 equal to plus or minus i, and all other coordinates zero. Pplus and Pminus denote one half of their outer products with their conjugates. Thus they are the pure states of the normalized vectors obtained by dividing the rays by the square root of two. For q in the real closed unit interval, rho(q) is q times Pplus plus (1 minus q) times Pminus. Born(X) means the real part of trace(X Pplus). Branch(X) is the trace of the original branch-7 Kraus map applied to X. Response(X,P,h) is ludersLaw menu P X h for the actual menu of FiveModeRealResponse.")),
            Describe.Lean(DescribeId.Create("five-mode-phase-lift-certificate"),
                DeclarationHandle.Create("D5/S3/Quantum/Fibers/FiveModePhaseLift.phase_lift_certificate"),
                H("A constant response fiber with an exact phase readout"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("q"), InMacro, Sp, C("IccReal", D(0), D(1)), Comma,
                    C("PSD", F.Id("Pplus")), Land, Sp, C("Tr", F.Id("Pplus")), Eq, D(1), Land, Sp,
                    C("PSD", F.Id("Pminus")), Land, Sp, C("Tr", F.Id("Pminus")), Eq, D(1), Land, Sp,
                    F.Id("Pplus"), F.Id("Pplus"), Eq, F.Id("Pplus"), Land, Sp,
                    F.Id("Pminus"), F.Id("Pminus"), Eq, F.Id("Pminus"), Land, Sp,
                    F.Id("Pplus"), F.Id("Pminus"), Eq, D(0), Land, Sp, RowBreak,
                    C("PSD", Seq(D(1), Minus, F.Id("Pplus"))), Land, Sp,
                    Neg, Sp, C("IsDiag", F.Id("Pplus")), Land, Sp,
                    C("PSD", C("rho", F.Id("q"))), Land, Sp,
                    C("Tr", C("rho", F.Id("q"))), Eq, D(1), Land, Sp, RowBreak,
                    Open, Forall, Sp, F.Id("r"), InMacro, Sp, C("IccReal", D(0), D(1)), Comma,
                    Forall, Sp, F.Id("P"), Colon, C("Protocol", C("Fin", D(5))), Comma,
                    Forall, Sp, F.Id("h"), Colon, C("Record", F.Id("P")), Comma,
                    C("Response", C("rho", F.Id("q")), F.Id("P"), F.Id("h")), Eq,
                    C("Response", C("rho", F.Id("r")), F.Id("P"), F.Id("h")), Close, Land, Sp, RowBreak,
                    C("Branch", C("rho", F.Id("q"))), Eq, Seq(Frac, Grp(D(1)), Grp(D(2))), Land, Sp,
                    C("Born", C("rho", F.Id("q"))), Eq, F.Id("q")))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The two endpoint matrices are positive trace-one orthogonal rank-one projections. The complement of Pplus is positive, so Pplus defines a projective two-outcome measurement together with its complement. Its coordinate (2,4) is nonzero and purely imaginary, hence it is non-diagonal. Convexity gives positivity of rho(q), and linearity of trace gives normalization. Every rho(q) has the same entrywise real part: its diagonal coordinates 2 and 4 are one half and all its real off-diagonal coordinates vanish. The exact real-response fiber theorem therefore supplies equality for every finite feedback protocol and each retained record, with arbitrary nonnegative real waits.")),
                    Paragraph(Text("The arbitrary-input branch theorem gives Branch(rho(q)) equal to rho(q) at coordinate (4,4), namely one half. Orthogonality and idempotence give trace(rho(q) Pplus) equal to q, exactly and without an error term. Distinct real mixing parameters therefore have distinct Born readouts even though all old responses and branch masses agree. This is a finite-dimensional operational construction. It supplies no Source, event map, or common stochastic realization connecting q to the Fibonacci JointLaw parameter. In particular q, kappa, p at coordinate 4, the (4,4) population, and the (2,4) coherence are not identified. No physical preparation, QFT realization, compression channel, or literature novelty is asserted."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("five-mode-phase-readout-not-determined"),
                DeclarationHandle.Create("D5/S3/Quantum/Fibers/FiveModePhaseLift.result"),
                H("The old menu and diagonal branch do not determine the phase measurement"),
                StatementSource.FromAuthor(Disp(Seq(Neg, Sp, F.Id("claim")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Here claim asserts the following universal implication for every pair X,Y of five-dimensional positive trace-one matrices: if Response(X,P,h) equals Response(Y,P,h) for every finite protocol P and record h, and Branch(X) equals Branch(Y), then Born(X) equals Born(Y). The endpoint mixtures q equal to zero and one satisfy the premises and have Born values zero and one. Thus no rule defined only by the complete old responses and branch trace can predict this added observable on all density states. The obstruction concerns the specified observation family; adding the phase-sensitive measurement resolves the mixing coordinate on this segment."))),
                DescribeRole.Theorem))));

    private static Formula C(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < arguments.Length; i++)
        {
            if (i > 0) items.Add(Comma);
            items.Add(arguments[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
}
