using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fibers;

internal sealed class FiveModeTwoCopyPhaseDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A real joint rank-one effect on two copies detects the squared hidden phase magnitude.",
        H("Five-Mode Two-Copy Phase Magnitude"), Blocks(
            Paragraph(Text("Use the five-coordinate phase mixture from FiveModePhaseLift. On two copies, the ray supported at (2,2) and (4,4) with coefficients 1 and -1 defines bellEffect. For q in the real closed unit interval, twoCopyProbability(q) is the real part of the trace of this effect against the Kronecker square of mixture(q).")),
            Describe.Lean(DescribeId.Create("five-mode-two-copy-phase-readout"),
                DeclarationHandle.Create("D5/S3/Quantum/Fibers/FiveModeTwoCopyPhase.two_copy_bell_readout"),
                H("Two-copy Bell readout"),
                StatementSource.FromAuthor(Disp(TwoCopyStatement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The normalized real Bell effect is positive, trace one, and idempotent. Its two-copy probability on the phase mixture is exactly (1 + (1 - 2q)^2) / 4. The readout distinguishes the balanced mixture from the endpoints but is invariant under q ↦ 1-q.")),
                    Paragraph(Text("This is a finite-dimensional operational result. It supplies no Source, kappa, p4, rho44, or rho24 bridge, no physical preparation, and no QFT realization."))),
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

    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Square(Formula value) => new Formula.Power(value, D(2));

    private static Formula TwoCopyStatement() => Seq(
        Forall, Sp, F.Id("q"), InMacro, Sp, C("IccReal", D(0), D(1)), Comma,
        C("PSD", F.Id("bellEffect")), Land, Sp,
        C("Tr", F.Id("bellEffect")), Eq, D(1), Land, Sp,
        Mul(F.Id("bellEffect"), F.Id("bellEffect")), Eq, F.Id("bellEffect"), Land, Sp,
        C("twoCopyProbability", F.Id("q")), Eq,
        Seq(Frac, Grp(D(1), Plus, Square(Grp(D(1), Minus, D(2), F.Id("q")))), Grp(D(4))));
}
