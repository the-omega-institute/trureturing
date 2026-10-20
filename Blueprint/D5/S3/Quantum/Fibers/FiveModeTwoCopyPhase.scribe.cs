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
                    Paragraph(Text("This is a finite-dimensional operational result. It supplies no Source, kappa, p4, rho44, or rho24 bridge, no physical preparation, and no QFT realization.")),
                    Paragraph(Text("For the same-family comparison, the input at q is two independent copies mixture(q) ⊗ mixture(q), and the input at r is mixture(r) ⊗ mixture(r). Write B(q) for the single specified Bell effect's value twoCopyProbability(q). For q and r in the real closed unit interval, the complete observational fiber of this readout is:")),
                    new DocumentBlock.DisplayFormula(FiberFormula()),
                    Paragraph(Text("To derive it, assume B(q) = B(r) and substitute the existing two_copy_bell_readout equality at q and r. Cancelling the common affine map x ↦ (1 + x) / 4 gives equality of the squares (1 - 2q)^2 and (1 - 2r)^2. The pinned Mathlib lemma sq_eq_sq_iff_eq_or_eq_neg then gives either 1 - 2q = 1 - 2r or 1 - 2q = -(1 - 2r); normalizing these affine equalities yields q = r or q + r = 1. Conversely, either normalized equality makes the two squares, and hence B, equal. At q = 1/2 the two alternatives coincide, so its fiber is a singleton; elsewhere the fiber is the pair {q, 1 - q}.")),
                    Paragraph(Text("This fiber describes this one fixed real Bell readout and the same-family preparation parameter. It does not classify all two-copy protocols, adaptive measurements, other joint effects, or arbitrary post-processing. The native Source, kappa, density/QFT, and preparation bridges remain absent, so the result does not assert a physical realization of the modeled mixtures."))),
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

    private static Formula FiberFormula()
    {
        var q = F.Id("q");
        var r = F.Id("r");
        var domain = C("IccReal", D(0), D(1));
        var left = Equal(
            C("twoCopyProbability", q),
            C("twoCopyProbability", r));
        var right = Seq(
            Open, q, Eq, r, Close, Sp, Lor, Sp,
            Open, q, Plus, r, Eq, D(1), Close);
        return Seq(
            Forall, Sp, q, InMacro, Sp, domain, Comma, Sp,
            Forall, Sp, r, InMacro, Sp, domain, Comma, Sp,
            Open, left, Close, Sp, Iff, Sp, right);
    }

    private static Formula TwoCopyStatement() => Seq(
        Forall, Sp, F.Id("q"), InMacro, Sp, C("IccReal", D(0), D(1)), Comma,
        C("PSD", F.Id("bellEffect")), Land, Sp,
        C("Tr", F.Id("bellEffect")), Eq, D(1), Land, Sp,
        Mul(F.Id("bellEffect"), F.Id("bellEffect")), Eq, F.Id("bellEffect"), Land, Sp,
        C("twoCopyProbability", F.Id("q")), Eq,
        Seq(Frac, Grp(D(1), Plus, Square(Grp(D(1), Minus, D(2), F.Id("q")))), Grp(D(4))));
}
