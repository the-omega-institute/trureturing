using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.MetricGeometry;

internal sealed class ArithmeticHorizonDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Accuracy of a finite autonomous predictor along one fixed irrational rotation orbit gives a strict arithmetic horizon bound.",
        H("Arithmetic Horizon"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-predictor-fixed-phase-arithmetic-horizon"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/MetricGeometry/ArithmeticHorizon."
                    + "finite_predictor_horizon"),
                H("Finite prediction at one phase has a strict arithmetic horizon"),
                StatementSource.FromAuthor(HorizonFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let S be any finite state type, G its autonomous update, h any complex-valued "
                        + "readout, and s0 its actual initial state. Fix x in AddCircle 1 and an irrational "
                        + "real rotation increment alpha. Write c(z) for the complex value of z.toCircle. "
                        + "The accuracy premise concerns only h(G^[n](s0)) and c(x+n alpha), for natural "
                        + "times zero through H inclusive. The phase x and initial state remain fixed "
                        + "throughout this premise.")),
                    Paragraph(Text(
                        "The definition torusNorm(t) is exactly the quotient norm of the class of t "
                        + "in AddCircle 1, or distance to the nearest integer. For a positive natural "
                        + "state budget s, Psi(alpha,s) is the maximum of p/torusNorm(p alpha) over "
                        + "all natural p with 1 <= p <= s. The definition sets Psi(alpha,0)=0. "
                        + "Irrationality makes every denominator in the positive-budget maximum "
                        + "strictly positive. The initial state makes the actual cardinality s positive.")),
                    Paragraph(Text(
                        "Put a=arcsin(epsilon)/pi. The range 0 < epsilon < 1/2 gives 0 < a < 1/6. "
                        + "For z in AddCircle 1, a chord estimate ||c(z)-1|| <= 2 epsilon implies "
                        + "||z|| <= a. To see this, choose the representative t in [-1/2,1/2). "
                        + "Its quotient norm is |t| and the chord length is 2 sin(pi |t|). "
                        + "Monotonicity of sine on [0,pi/2], expressed by the inverse-sine inequality, "
                        + "converts the chord bound to the stated arc bound.")),
                    Paragraph(Text(
                        "The small-arc step uses every sampled multiple. If ||k z|| <= a for "
                        + "0 <= k <= K, induction proves k||z|| <= a over the same finite range. "
                        + "For the induction step the preceding bound and ||z|| <= a give "
                        + "|(k+1)t| <= 2a < 1/3 < 1/2. Thus the next real lift is still inside "
                        + "the interval where quotient norm equals absolute value. Applying the "
                        + "next sampled bound completes the step. This establishes K||z|| <= a "
                        + "without assuming that the rotation stays unwrapped.")),
                    Paragraph(Text(
                        "Apply finite_orbit_and_readout_eventually_periodic from "
                        + "D5.S3.ObserverMemory.Prediction.FiniteOrbitPeriodBound to G, h, and s0. "
                        + "It supplies a preperiod mu and a positive period p with mu+p <= s. "
                        + "The readout at every time mu+kp equals the readout at mu. If H >= s, "
                        + "let K=(H-mu)/p using natural-number division. Both sampled times lie "
                        + "within the accuracy interval for 0 <= k <= K. Their two errors give "
                        + "a chord bound of 2 epsilon. Multiplication by the unit complex phase "
                        + "c(x+mu alpha) preserves the norm, so the chord bound concerns k(p alpha) "
                        + "alone. The small-arc step therefore yields K torusNorm(p alpha) <= a.")),
                    Paragraph(Text(
                        "The strict division remainder bound gives H < mu+(K+1)p. Since "
                        + "mu+p <= s, division by the positive torus norm yields "
                        + "H < s+a p/torusNorm(p alpha) <= s+a Psi(alpha,s). "
                        + "If H < s, nonnegativity of a Psi(alpha,s) gives the result directly. "
                        + "This branch includes H=0 because an actual initial state forces s >= 1. "
                        + "The strict inequality comes from the remainder bound, even though "
                        + "the accuracy and small-arc inequalities are non-strict.")),
                    Paragraph(Text(
                        "For a Diophantine consequence, keep the same finite S, update G, arbitrary "
                        + "complex readout h, actual initial state s0, irrational alpha, fixed phase x, "
                        + "and accuracy at every natural time 0 <= n <= H with 0 < epsilon < 1/2. "
                        + "Set s=card S >= 1 and a=arcsin(epsilon)/pi. Let kappa and nu be real "
                        + "numbers with kappa > 0 and nu >= 1, and assume "
                        + "torusNorm(p alpha) >= kappa p^(-nu) for every positive natural p. "
                        + "The positive Diophantine constant, often denoted c, is written kappa "
                        + "to distinguish it from the complex-valued map c(z). Powers here are "
                        + "real powers, represented by Real.rpow; nu need not be an integer.")),
                    Paragraph(Text(
                        "For each natural p with 1 <= p <= s, positivity of p and kappa gives "
                        + "torusNorm(p alpha) >= kappa p^(-nu) > 0. The real-power identity "
                        + "p^(nu+1) p^(-nu)=p, supplied by Real.rpow_add and Real.rpow_one, then "
                        + "gives p/torusNorm(p alpha) <= p^(nu+1)/kappa. Since nu+1 >= 0, "
                        + "Real.rpow_le_rpow applied to p <= s yields "
                        + "p^(nu+1)/kappa <= s^(nu+1)/kappa.")),
                    Paragraph(Text(
                        "The range 1 <= p <= s is nonempty because the actual initial state "
                        + "forces s >= 1. Taking its exact finite maximum, as expressed by "
                        + "Finset.sup'_le in the definition of Psi, proves "
                        + "Psi(alpha,s) <= s^(nu+1)/kappa. Multiplying by the positive a and "
                        + "combining with finite_predictor_horizon gives the complete chain "
                        + "H < s+a Psi(alpha,s) <= s+(a/kappa)s^(nu+1). Thus the resulting "
                        + "Diophantine horizon bound is strict for every real nu >= 1.")),
                    Paragraph(Text(
                        "The first strict bound H < s+a Psi(alpha,s) uses no Diophantine "
                        + "hypothesis; the extra assumption is used only to estimate Psi. Both "
                        + "bounds concern the same fixed phase and initial state and allow any "
                        + "complex-valued h. The case H=0 remains included, while an empty state "
                        + "type cannot supply the required initial state.")),
                    Paragraph(Text(
                        "Periodicity is derived from finiteness of the autonomous state map. "
                        + "The readout may take arbitrary complex values, and the accuracy premise "
                        + "requires neither other initial states nor other phases. The conclusion "
                        + "is an arithmetic upper bound for this finite horizon; its hypotheses "
                        + "contain no physical realization, resource cost, or least-state assertion."))),
                DescribeRole.Theorem))));

    private static Formula Card() =>
        Seq(Operatorname, Grp(F.Id("card")), Open, F.Id("S"), Close);

    private static Formula CircleType() =>
        Seq(Operatorname, Grp(F.Id("AddCircle")), Open, D(1), Close);

    private static Formula Initial() => Seq(F.Id("s"), Underscore, Grp(D(0)));

    private static Formula Accuracy()
    {
        Formula n = F.Id("n");
        Formula predicted = Seq(F.Id("h"), Open, F.Id("G"), Caret, Grp(n),
            Open, Initial(), Close, Close);
        Formula target = Seq(F.Id("c"), Open, F.Id("x"), Plus, n, Alpha, Close);
        return Seq(Forall, Sp, n, InMacro, Mathbb, Grp(F.Id("N")), Comma, Sp,
            n, Leq, Sp, F.Id("H"), Sp, Rightarrow, Sp,
            Vert, Sp, predicted, Minus, target, Vert, Leq, Varepsilon);
    }

    private static Formula HorizonFormula() => Disp(Seq(
        Forall, Sp, F.Id("S"), Comma, Sp,
        OpenBracket, Operatorname, Grp(F.Id("Fintype")), Sp, F.Id("S"), CloseBracket, Comma, Esc,
        Forall, Sp, F.Id("G"), Colon, F.Id("S"), To, Sp, F.Id("S"), Comma, Sp,
        F.Id("h"), Colon, F.Id("S"), To, Sp, Mathbb, Grp(F.Id("C")), Comma, Esc,
        Forall, Sp, Initial(), InMacro, Sp, F.Id("S"), Comma, Sp,
        F.Id("x"), InMacro, CircleType(), Comma, Esc,
        Forall, Sp, Alpha, Comma, Varepsilon, InMacro, Mathbb, Grp(F.Id("R")), Comma, Sp,
        Operatorname, Grp(F.Id("Irrational")), Open, Alpha, Close, Sp, Rightarrow, Sp,
        D(0), Lt, Varepsilon, Sp, Rightarrow, Sp,
        Varepsilon, Lt, Frac, Grp(D(1)), Grp(D(2)), Sp, Rightarrow, Esc,
        Forall, Sp, F.Id("H"), InMacro, Mathbb, Grp(F.Id("N")), Comma, Sp,
        Open, Accuracy(), Close, Sp, Rightarrow, Esc,
        F.Id("H"), Lt, Card(), Plus,
        Frac, Grp(Operatorname, Grp(F.Id("arcsin")), Open, Varepsilon, Close), Grp(Pi),
        Sp, Psi, Open, Alpha, Comma, Card(), Close, Dot));
}
