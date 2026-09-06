using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZeroInfinitude;

internal sealed class CosinePacketDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Weil/ZeroInfinitude/CosinePacket.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A normalized convolution-square Weil packet has positive transform near zero, "
            + "and cosine modulation gives uniform prime control and finite-side decay.",
        H("Cosine-Modulated Packet"),
        Blocks(
            Paragraph(Text(
                "This is the packet half of the zero-infinitude argument of 增订三十. "
                    + "The explicit formula EF_lit holds for every ZeroConfig regardless "
                    + "of carrier cardinality; only the packet, its modulation, and the "
                    + "finite-side limits are proved here.")),
            Paragraph(Text(
                "The prime bound needs neither Chebyshev nor the prime number theorem, "
                    + "because the support of the cosine-modulated packet is fixed. The "
                    + "test functions are this repository's WeilTestFunction.")),
            Paragraph(Text(
                "No statement about zeta's zeros beyond the finite-carrier limit is made "
                    + "here. In particular, this document is not a proof of the Riemann "
                    + "hypothesis.")),
            Item("packet-seed", "packetSeed", "The normalized packet seed",
                PacketSeedDefinition(), DescribeRole.Definition,
                "The value is the repository's canonical volume-normalized smooth bump."),
            Item("packet-seed-fourier-laplace-zero", "packetSeed_fourierLaplace_zero",
                "The seed is normalized at zero", PacketSeedZero(), DescribeRole.Theorem,
                "Its Fourier-Laplace transform at the origin is exactly one."),
            Item("packet-square", "packetSquare", "The convolution-square packet",
                PacketSquareDefinition(), DescribeRole.Definition,
                "The positive packet is the repository convolution square of packetSeed."),
            Item("packet-transform-real-nonnegative", "packetTransform_real_nonneg",
                "The packet transform is real and nonnegative", PacketRealNonnegative(),
                DescribeRole.Theorem,
                "On the real axis, the imaginary part vanishes and the real part is nonnegative."),
            Item("packet-transform-zero", "packetTransform_zero",
                "The packet transform equals one at zero", PacketTransformZero(),
                DescribeRole.Theorem,
                "Convolution-square positivity combines with seed normalization at the origin."),
            Item("packet-transform-integrable", "packetTransform_integrable",
                "The packet transform is integrable", PacketTransformIntegrable(),
                DescribeRole.Theorem,
                "Two derivatives and compact support give real-axis integrability."),
            Item("packet-transform-ge-half-near-zero",
                "packetTransform_ge_half_near_zero",
                "The packet transform stays above one half near zero", PacketNearZero(),
                DescribeRole.Theorem,
                "Continuity at the normalized value one supplies a positive neighborhood."),
            Item("cosine-modulation", "cosineModulation",
                "Cosine modulation of a Weil test function", CosineDefinition(),
                DescribeRole.Definition,
                "Multiplication by cos(Tx) preserves smoothness, compact support, and evenness."),
            Item("paper-ft-cosine-modulation", "paperFT_cosineModulation",
                "Cosine modulation shifts the transform", CosineTransform(),
                DescribeRole.Theorem,
                "The two frequency shifts occur with equal coefficient one half."),
            Item("paper-ft-cosine-modulation-tendsto-zero",
                "paperFT_cosineModulation_tendsto_zero",
                "The modulated transform decays pointwise on the unit strip",
                ModulatedPointwiseDecay(), DescribeRole.Theorem,
                "Closed-strip quadratic decay sends both translated packet transforms to zero."),
            Item("paper-ft-cosine-modulation-pole-pos-tendsto-zero",
                "paperFT_cosineModulation_pole_pos_tendsto_zero",
                "The positive pole specialization tends to zero", PoleDecay(false),
                DescribeRole.Theorem,
                "This is the pointwise strip limit specialized to positive i over two."),
            Item("paper-ft-cosine-modulation-pole-neg-tendsto-zero",
                "paperFT_cosineModulation_pole_neg_tendsto_zero",
                "The negative pole specialization tends to zero", PoleDecay(true),
                DescribeRole.Theorem,
                "This is the pointwise strip limit specialized to negative i over two."),
            Item("prime-term-cosine-modulation-bounded",
                "primeTerm_cosineModulation_bounded",
                "The modulated prime term has a uniform bound", PrimeBound(),
                DescribeRole.Theorem,
                "Fixed compact support reduces the prime series to one finite carrier, "
                    + "while the cosine factor has absolute value at most one."),
            Item("finite-carrier-zero-side-tendsto-zero",
                "finiteCarrier_zeroSide_tendsto_zero",
                "Every finite-carrier zero side tends to zero", FiniteCarrierDecay(),
                DescribeRole.Theorem,
                "Pointwise strip decay passes through the finite multiplicity-weighted sum.")),
        []));

    private static DocumentBlock.Describe Item(string id, string declaration,
        string heading, Formula formula, DescribeRole role, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(heading), StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula PacketSeedDefinition()
    {
        Formula x = F.Id("x");
        return Disp(ForAll([Bound("x", Reals())], Equal(
            Call("packetSeed", x), Call("standardBumpNormed", F.Id("volume"), x))));
    }

    private static Formula PacketSeedZero() =>
        Disp(Equal(Call("fourierLaplace", F.Id("packetSeed"), D(0)), D(1)));

    private static Formula PacketSquareDefinition() => Disp(Equal(
        F.Id("packetSquare"), Call("convolutionSquare", F.Id("packetSeed"))));

    private static Formula PacketRealNonnegative()
    {
        Formula t = F.Id("t"); Formula transform = Paper(F.Id("packetSquare"), t);
        return Disp(ForAll([Bound("t", Reals())], And(
            Equal(ImaginaryPart(transform), D(0)),
            AtMost(D(0), RealPart(transform)))));
    }

    private static Formula PacketTransformZero() =>
        Disp(Equal(Paper(F.Id("packetSquare"), D(0)), D(1)));

    private static Formula PacketTransformIntegrable()
    {
        Formula t = F.Id("t");
        return Disp(Call("Integrable", Lambda(t, Reals(), Paper(F.Id("packetSquare"), t))));
    }

    private static Formula PacketNearZero()
    {
        Formula delta = F.Id("delta"); Formula t = F.Id("t");
        Formula local = Implies(AtMost(new Formula.Absolute(t), delta),
            AtMost(Half(), RealPart(Paper(F.Id("packetSquare"), t))));
        return Disp(Exists([Bound("delta", Reals())], And(
            Less(D(0), delta), ForAll([Bound("t", Reals())], local))));
    }

    private static Formula CosineDefinition()
    {
        Formula q = F.Id("q"); Formula t = F.Id("T"); Formula x = F.Id("x");
        return Disp(ForAll([
            Bound("q", F.Id("WeilTestFunction")), Bound("T", Reals()), Bound("x", Reals())
        ], Equal(Modulated(q, t, x),
            Multiply(Call("cos", Multiply(t, x)), Call("apply", q, x)))));
    }

    private static Formula CosineTransform()
    {
        Formula q = F.Id("q"); Formula t = F.Id("T"); Formula z = F.Id("z");
        Formula shifted = new Formula.Fraction(
            Add(Paper(q, Add(z, t)), Paper(q, Subtract(z, t))), D(2));
        return Disp(ForAll([
            Bound("q", F.Id("WeilTestFunction")), Bound("T", Reals()),
            Bound("z", Complexes())
        ], Equal(PaperModulated(q, t, z), shifted)));
    }

    private static Formula ModulatedPointwiseDecay()
    {
        Formula z = F.Id("z"); Formula t = F.Id("T");
        Formula premise = AtMost(new Formula.Absolute(ImaginaryPart(z)), D(1));
        Formula limit = TendsToZero(t, PaperModulated(F.Id("packetSquare"), t, z));
        return Disp(ForAll([Bound("z", Complexes())], Implies(premise, limit)));
    }

    private static Formula PoleDecay(bool negative)
    {
        Formula t = F.Id("T");
        Formula pole = new Formula.Fraction(F.Id("i"), D(2));
        if (negative) pole = new Formula.Negate(pole);
        return Disp(TendsToZero(t, PaperModulated(F.Id("packetSquare"), t, pole)));
    }

    private static Formula PrimeBound()
    {
        Formula b = F.Id("B"); Formula t = F.Id("T"); Formula n = F.Id("n");
        Formula logn = Call("log", n);
        Formula coefficient = new Formula.Fraction(Call("vonMangoldt", n), Call("sqrt", n));
        Formula samples = Add(
            Modulated(F.Id("packetSquare"), t, logn),
            Modulated(F.Id("packetSquare"), t, new Formula.Negate(logn)));
        Formula sum = Tsum(n, Naturals(), Multiply(coefficient, samples));
        Formula uniform = ForAll([Bound("T", Reals())],
            AtMost(new Formula.Norm(sum), b));
        return Disp(Exists([Bound("B", Reals())], uniform));
    }

    private static Formula FiniteCarrierDecay()
    {
        Formula zc = F.Id("Z"); Formula t = F.Id("T"); Formula rho = F.Id("rho");
        Formula carrier = Call("carrier", zc);
        Formula term = Multiply(Call("mult", zc, rho),
            PaperModulated(F.Id("packetSquare"), t, Call("gammaOf", rho)));
        Formula limit = TendsToZero(t, Tsum(rho, carrier, term));
        Formula finite = Call("Finite", carrier);
        return Disp(ForAll([Bound("Z", F.Id("ZeroConfig"))], Implies(finite, limit)));
    }

    private static Formula Paper(Formula q, Formula z) => Call("paperFT", q, z);

    private static Formula PaperModulated(Formula q, Formula t, Formula z) =>
        Paper(Call("cosineModulation", q, t), z);

    private static Formula Modulated(Formula q, Formula t, Formula x) =>
        Call("cosineModulation", q, t, x);

    private static Formula TendsToZero(Formula variable, Formula expression) =>
        Call("Tendsto", Lambda(variable, Reals(), expression),
            F.Id("atTop"), Call("nhds", D(0)));

    private static Formula Tsum(Formula variable, Formula domain, Formula body) =>
        Seq(Sum, Underscore, Grp(variable, Sp, InMacro, Sp, domain), Sp, body);

    private static Formula Lambda(Formula variable, Formula domain, Formula body) =>
        Seq(Open, variable, Colon, Sp, domain, Sp, Mapsto, Sp, body, Close);

    private static Formula RealPart(Formula value) =>
        Seq(Re, Sp, Open, value, Close);

    private static Formula ImaginaryPart(Formula value) =>
        Seq(Operatorname, Grp(F.Id("Im")), Sp, Open, value, Close);

    private static Formula Half() => new Formula.Fraction(D(1), D(2));

    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));

    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula ForAll(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    private static Formula Exists(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [.. variables], body);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula AtMost(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
}
