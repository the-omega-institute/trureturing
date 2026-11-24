using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.Concentration;

internal sealed class FiniteSineMissingWindowDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Fourier/Concentration/FiniteSineMissingWindow";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One assignment of tail signs keeps a finite sine score below a strict bound "
            + "throughout a closed interval.",
        H("Finite Sine-Score Missing Windows"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("signed-score"),
                DeclarationHandle.Create(Owner + ".signedScore"),
                H("Signed linear score"),
                StatementSource.FromAuthor(SignedScore()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The sign σ is +1 for true and −1 for false. Only coordinates of "
                    + "the given finite set contribute. Coefficient families and scores "
                    + "are real-valued."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("signs-on-grid"),
                DeclarationHandle.Create(Owner + ".exists_signs_on_grid"),
                H("One sign vector for all grid nodes"),
                StatementSource.FromAuthor(Grid()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Take finite types J and K, a subset s of J, nonnegative weights w, "
                        + "and real coefficients c indexed by K and J. The output b is "
                        + "Boolean valued. Sample independent fair signs, using the same sign space for every "
                        + "node. At a fixed node, each signed coefficient is centered and lies "
                        + "between minus its coordinate weight and that weight. The pinned "
                        + "Hoeffding inequality bounds the probability that the score reaches "
                        + "the positive threshold δ by exp(−δ²/(2V)), where V is the sum of "
                        + "the squared weights. Subadditivity over the nodes gives total bad "
                        + "probability at most the node count times this bound. A strict "
                        + "budget below one leaves a sign vector that works at every node.")),
                    Paragraph(Text(
                        "When V vanishes, each selected coefficient is zero, so every sign "
                        + "vector works for a positive threshold. The argument also applies "
                        + "to a singleton tail.")),
                    Paragraph(Text(
                        "The finite-family concentration argument is related to the "
                        + "Kahane–Salem–Zygmund estimate in Defant and Mastyło, "
                        + "Aspects of the Kahane–Salem–Zygmund inequalities in Banach "
                        + "spaces, Theorem 3.1 (DOI 10.1007/s13398-022-01369-4)."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("sine-score"),
                DeclarationHandle.Create(Owner + ".sineScore"),
                H("Weighted sine score with initial phases"),
                StatementSource.FromAuthor(SineScore()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Frequencies are angular rates. For ordinates γ and time scale r, "
                    + "use the rates γ/r."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("phases-on-closed-window"),
                DeclarationHandle.Create(Owner + ".exists_phases_on_closed_window"),
                H("Prescribed head phases and a uniform tail bound"),
                StatementSource.FromAuthor(Window()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let H be the head in the finite index type J, Hᶜ its complement, "
                        + "f and θ real-valued frequencies and head phases, and w nonnegative "
                        + "weights. For length R and positive mesh h, use the nodes kh from k = 0 "
                        + "through the natural floor of R/h. Each t in [0,R] is within "
                        + "h of its left node, including the right endpoint. Apply the "
                        + "grid theorem to the tail coefficients wⱼ sin(fⱼ kh), then lift "
                        + "the two signs to phases 0 and π.")),
                    Paragraph(Text(
                        "The head contributes at most its weight, with its phases fixed "
                        + "at their prescribed values. The unit Lipschitz bound for sine "
                        + "extends the tail estimate between nodes at a cost no greater "
                        + "than h times the sum of wⱼ|fⱼ| over the tail. The bound is "
                        + "strict over the entire closed interval.")),
                    Paragraph(Text(
                        "For nine frequencies j/9 with j from 1 through 9 and unit weights, "
                        + "take the first frequency as the head and prescribe phase π/2. "
                        + "On [0, 1/8], the mesh h = 1/8 has two nodes, and δ = 4 gives "
                        + "budget 2 exp(−1) < 1 with tail variance 8. The tail slope is "
                        + "at most 8, so the selected phases give a score strictly below 6 "
                        + "and a normalized deficit strictly above 1/3."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("arbitrarily-late-missing-window"),
                DeclarationHandle.Create(Owner + ".exists_arbitrarily_late_missing_window"),
                H("Arbitrarily late windows in the original orbit"),
                StatementSource.FromAuthor(Orbit()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Rational linear independence rules out nonzero integer relations. "),
                        Ref("D5/S3/Fourier/WeightedPhaseRelationLattice.closure_real_phase_orbit"),
                        Text(
                            " then gives a time strictly above any start whose unit phases "
                            + "approximate the selected phase vector. Multiplication by the "
                            + "same unit phase during the window preserves each chord error. "
                            + "Taking imaginary parts and summing against the weights bounds "
                            + "the score error uniformly over the interval.")),
                    Paragraph(Text(
                        "Let M denote head mass plus the grid threshold and slope allowance, "
                        + "and let W be the total weight. For any target B > M, "
                        + "the chord tolerance (B − M)/(W + 1) spends at most the "
                        + "available margin. For W > 0 and B = (1 − ε)W, "
                        + "the normalized sine deficit throughout the translated window "
                        + "is strictly greater than ε.")),
                    Paragraph(Text(
                        "For the zeta application, assume RH and rational linear independence "
                        + "of the distinct positive ordinates γ. Use the inclusive cutoff γ ≤ T, "
                        + "weights wγ = mγ γ/(1/4 + γ²) with analytic multiplicities mγ, "
                        + "and rates γ/r for fixed r > 0. Write W(T) for the sum of these weights "
                        + "and S(T,v) for their sine score at v. For fixed 0 < β < 1 and "
                        + "0 < ε < 1 − β², choose β < κ < α < √(1 − ε). "
                        + "Take the head cutoff X = T^α and window length R = exp(T^β).")),
                    Paragraph(Text(
                        "The harmonic mass asymptotic W(T) ∼ log²(T)/(4π) gives W(T) ≥ 1 "
                        + "eventually and W(X)/W(T) → α². Choose c > 0 such that "
                        + "α² < 1 − ε − 3c. The head mass is then at most "
                        + "(1 − ε − 3c)W(T) for all sufficiently large T. The multiplicity "
                        + "in (γ − 1, γ] bounds mγ by O(log(γ + 2)). Consequently the largest "
                        + "weight on X < γ ≤ T is O(log(T + 2)/T^α) = O(T^(−κ)). "
                        + "Multiplying this cap by the tail mass gives V ≤ C T^(−κ) W(T) "
                        + "for some C > 0.")),
                    Paragraph(Text(
                        "Set δ = cW(T) and h = cr/T. The mesh has at most "
                        + "exp(2T^β) nodes eventually, since its count is bounded above "
                        + "by T exp(T^β)/(cr) + 1. If V > 0, then δ²/(2V) ≥ "
                        + "c²T^κ W(T)/(2C) > 2T^β eventually. The tail slope allowance "
                        + "is at most h(T/r)W(T) = cW(T). These inequalities give "
                        + "M ≤ (1 − ε − c)W(T) < (1 − ε)W(T). The orbit theorem applies "
                        + "with B = (1 − ε)W(T), since restricting the ordinates and dividing "
                        + "by r preserves independence over ℚ. For every sufficiently large "
                        + "T and every A there is an a > A with 1 − S(T,u/r)/W(T) > ε "
                        + "for all u in [a,a + exp(T^β)]. The equality ε = 1 − β² is "
                        + "outside this estimate.")),
                    Paragraph(Text(
                        "For a singleton frequency and weight both equal to one, take "
                        + "R = 1/16, h = 1/8, and δ = 1/4. The sole grid node gives "
                        + "budget exp(−1/32) < 1, and the upper bound 3/8 leaves a "
                        + "strict margin below B = 1/2. Thus sin(u) stays below 1/2 "
                        + "on intervals of length 1/16 beginning arbitrarily late."))),
                DescribeRole.Theorem))));

    private static Formula At(Formula family, Formula index) =>
        Seq(family, Underscore, Grp(index));

    private static Formula Terms(Formula subset, Formula body) =>
        Seq(Sum, Underscore, Grp(F.Id("j"), Sp, InMacro, Sp, subset), Sp, body);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Call(Formula family, params Formula[] arguments) =>
        new Formula.Apply(family, [.. arguments]);

    private static Formula Tail() => new Formula.Power(F.Id("H"), F.Id("c"));

    private static Formula Budget(Formula count) =>
        Seq(Open, F.Id("V"), Eq, D(0), Sp, Lor, Sp,
            Multiply(count, Call("exp", new Formula.Fraction(
                Seq(Minus, new Formula.Power(DeltaLower, D(2))), Multiply(D(2), F.Id("V"))))),
            Lt, D(1), Close);

    private static Formula MeshCount()
    {
        var quotient = new Formula.Fraction(F.Id("R"), F.Id("h"));
        var naturalFloor = Seq(new Formula.Floor(quotient), Underscore, Grp(Plus));
        return Seq(Open, Add(naturalFloor, D(1)), Close);
    }

    private static Formula SignedScore()
    {
        var j = F.Id("j");
        return Disp(Equal(
            Call("signedScore", F.Id("s"), F.Id("c"), F.Id("b")),
            Terms(F.Id("s"), Multiply(
                Call(SigmaLower, Call("b", j)), At(F.Id("c"), j)))));
    }

    private static Formula Grid()
    {
        var c = At(F.Id("c"), Seq(F.Id("k"), Comma, F.Id("j")));
        return Disp(new Formula.Aligned([
            Seq(F.Id("V"), Eq, Terms(F.Id("s"), new Formula.Power(
                At(F.Id("w"), F.Id("j")), D(2))), Comma, Quad,
                DeltaLower, Gt, D(0), Comma, Quad,
                Budget(new Formula.Absolute(F.Id("K"))), Comma),
            Seq(Open, Forall, Sp, F.Id("k"), Sp, InMacro, Sp, F.Id("K"), Comma,
                F.Id("j"), Sp, InMacro, Sp, F.Id("s"), Comma, Sp,
                new Formula.Absolute(c), Sp, Le, Sp, At(F.Id("w"), F.Id("j")), Close),
            Seq(Longrightarrow, Sp, Exists, Sp, F.Id("b"), Colon, Sp, F.Id("J"),
                Sp, To, Sp, Mathbb, Grp(F.Id("B")), Comma, Quad,
                Forall, Sp, F.Id("k"), Sp, InMacro, Sp, F.Id("K"), Comma, Quad,
                Call("signedScore", F.Id("s"), At(F.Id("c"), F.Id("k")), F.Id("b")),
                Lt, DeltaLower)
        ]));
    }

    private static Formula SineScore()
    {
        var j = F.Id("j");
        var angle = Add(At(Varphi, j), Multiply(At(F.Id("f"), j), F.Id("t")));
        return Disp(Equal(
            Call("sineScore", F.Id("f"), Varphi, F.Id("w"), F.Id("t")),
            Terms(F.Id("J"), Multiply(At(F.Id("w"), j), Call("sin", angle)))));
    }

    private static Formula Variance()
    {
        var weight = At(F.Id("w"), F.Id("j"));
        return Equal(F.Id("V"), Terms(Tail(), new Formula.Power(weight, D(2))));
    }

    private static Formula Ceiling()
    {
        var j = F.Id("j");
        return Equal(F.Id("M"), Add(Add(Terms(F.Id("H"), At(F.Id("w"), j)), DeltaLower),
            Multiply(F.Id("h"), Terms(Tail(), Multiply(At(F.Id("w"), j),
                new Formula.Absolute(At(F.Id("f"), j)))))));
    }

    private static Formula Interval(Formula start, Formula end) =>
        Seq(OpenBracket, start, Comma, end, CloseBracket);

    private static Formula Window()
    {
        var j = F.Id("j");
        return Disp(new Formula.Aligned([
            Seq(Variance(), Comma, Quad, Sp, Ceiling(), Comma),
            Seq(F.Id("h"), Gt, D(0), Comma, Quad, Sp, DeltaLower, Gt, D(0), Comma, Quad,
                Budget(MeshCount())),
            Seq(Longrightarrow, Sp, Exists, Sp, Varphi, Colon, Sp, F.Id("J"), Sp,
                To, Sp, Mathbb, Grp(F.Id("R")), Comma),
            Seq(Open, Forall, Sp, j, Sp, InMacro, Sp, F.Id("H"), Comma, Sp,
                Equal(At(Varphi, j), At(Theta, j)), Close, Quad, Sp, Land, Sp,
                Open, Forall, Sp, j, Sp, InMacro, Sp, Tail(), Comma, Sp,
                At(Varphi, j), Sp, InMacro, Sp, OpenBrace, D(0), Comma, Pi, Sp,
                CloseBrace, Close),
            Seq(Land, Sp, Open, Forall, Sp, F.Id("t"), Sp, InMacro, Sp,
                Interval(D(0), F.Id("R")), Comma, Sp,
                Call("sineScore", F.Id("f"), Varphi, F.Id("w"), F.Id("t")),
                Lt, F.Id("M"), Close)
        ]));
    }

    private static Formula Orbit()
    {
        var a = F.Id("a");
        var r = F.Id("R");
        return Disp(new Formula.Aligned([
            Seq(Variance(), Comma, Quad, Sp, Ceiling(), Comma),
            Seq(Call("LinearIndependent", Seq(Mathbb, Grp(F.Id("Q"))), F.Id("f")), Comma,
                Quad, Sp, F.Id("h"), Gt, D(0), Comma, Quad, Sp, DeltaLower, Gt, D(0), Comma),
            Seq(Budget(MeshCount()), Comma, Quad, Sp, F.Id("M"), Lt, F.Id("B")),
            Seq(Longrightarrow, Sp, Forall, Sp, F.Id("A"), Sp, InMacro, Sp,
                Mathbb, Grp(F.Id("R")), Comma, Quad, Sp, Exists, Sp, a, Gt, F.Id("A"), Comma),
            Seq(Forall, Sp, F.Id("u"), Sp, InMacro, Sp, Interval(a, Add(a, r)), Comma,
                Quad, Sp, Call("sineScore", F.Id("f"), D(0), F.Id("w"), F.Id("u")),
                Lt, F.Id("B"))
        ]));
    }
}
