using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZeroInfinitude;

internal sealed class ArchimedeanDivergenceDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Weil/ZeroInfinitude/ArchimedeanDivergence.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "This is the Archimedean half of the zero-infinitude argument in Addendum Thirty, "
            + "stated for an abstract profile H. A later module instantiates H with the "
            + "cosine packet.",
        H("Archimedean Divergence of Translated Packets"),
        Blocks(
            Paragraph(Text(
                "Growth comes from the frozen Stirling bound mu_stirling and monotonicity "
                    + "of mu on the nonnegative real axis. The quantified lower bound is "
                    + "the escape witness that connects those facts to translated packet mass.")),
            Paragraph(Text(
                "This module is not a proof of the Riemann hypothesis and makes no statement "
                    + "about zeros.")),
            Describe.Lean(
                DescribeId.Create("packet"),
                DeclarationHandle.Create(Prefix + "packet"),
                H("The translated packet"),
                StatementSource.FromAuthor(PacketDefinition()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The packet is the symmetric average of the two opposite translations "
                        + "of H."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("packet-integral"),
                DeclarationHandle.Create(Prefix + "packet_integral"),
                H("Translation preserves packet mass"),
                StatementSource.FromAuthor(PacketIntegral()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Translation invariance of Lebesgue integration makes the average retain "
                        + "the total integral of H."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("mu-add-one-pos"),
                DeclarationHandle.Create(Prefix + "mu_add_one_pos"),
                H("The shifted Archimedean weight is positive"),
                StatementSource.FromAuthor(MuAddOnePos()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The frozen global lower bound for mu combines with its strict value at "
                        + "zero to give positivity after adding one."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("mu-tendsto-at-top"),
                DeclarationHandle.Create(Prefix + "mu_tendsto_atTop"),
                H("The Archimedean weight tends to infinity"),
                StatementSource.FromAuthor(MuTendsto()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The frozen Stirling estimate bounds mu below by its logarithmic main "
                        + "term minus a constant."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("packet-weighted-integrable-of-decay"),
                DeclarationHandle.Create(Prefix + "packet_weighted_integrable_of_decay"),
                H("Quadratic decay makes the weighted packet integrable"),
                StatementSource.FromAuthor(PacketWeightedIntegrable()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Quadratic decay is stable under each fixed translation and dominates "
                        + "the logarithmic growth of mu by an integrable power tail."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("archimedean-lower-bound"),
                DeclarationHandle.Create(Prefix + "archimedean_lower_bound"),
                H("A translated interval gives the escape lower bound"),
                StatementSource.FromAuthor(ArchimedeanLowerBound()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "On the interval from T-delta to T+delta, one translated copy contributes "
                        + "at least one half and the other remains nonnegative. Monotonicity "
                        + "of mu then yields the displayed delta-over-two lower bound."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("archimedean-divergence-of-decay"),
                DeclarationHandle.Create(Prefix + "archimedean_divergence_of_decay"),
                H("The real weighted packet integral diverges"),
                StatementSource.FromAuthor(ArchimedeanDivergence()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The escape lower bound and the logarithmic growth of mu force the real "
                        + "weighted integral to positive infinity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("archimedean-divergence-complex-of-decay"),
                DeclarationHandle.Create(Prefix + "archimedean_divergence_complex_of_decay"),
                H("The real part of the complex integral diverges"),
                StatementSource.FromAuthor(ArchimedeanDivergenceComplex()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Complexification preserves the real integrand, so taking the real part "
                        + "recovers the real divergence statement exactly."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("gamma-term-packet"),
                DeclarationHandle.Create(Prefix + "gamma_term_packet"),
                H("The explicit-formula gamma term is the packet integral"),
                StatementSource.FromAuthor(GammaTermPacket()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The frozen gamma_term identity rewrites the explicit-formula density, "
                        + "and the supplied pointwise paper-transform identity replaces it by "
                        + "the translated packet."))),
                DescribeRole.Theorem))));

    private static Formula PacketDefinition()
    {
        var context = Context();
        return Disp(ForAll(
            [Bound("H", context.Function), Bound("T", context.Real), Bound("r", context.Real)],
            Equal(
                Packet(context.H, context.T, context.R),
                Div(
                    Add(
                        Apply(context.H, Add(context.R, context.T)),
                        Apply(context.H, Sub(context.R, context.T))),
                    D(2)))));
    }

    private static Formula PacketIntegral()
    {
        var context = Context();
        return Disp(ForAll(
            [Bound("H", context.Function)],
            Implies(
                Call("Integrable", context.H),
                ForAll(
                    [Bound("T", context.Real)],
                    Equal(
                        Integral(context.R, context.Real, Packet(context.H, context.T, context.R)),
                        Integral(context.R, context.Real, Apply(context.H, context.R)))))));
    }

    private static Formula MuAddOnePos()
    {
        var context = Context();
        return Disp(ForAll(
            [Bound("r", context.Real)],
            Less(D(0), Add(Mu(context.R), D(1)))));
    }

    private static Formula MuTendsto()
    {
        var context = Context();
        return Disp(Call("Tendsto", Lambda(context.R, context.Real, Mu(context.R)),
            F.Id("atTop"), F.Id("atTop")));
    }

    private static Formula PacketWeightedIntegrable()
    {
        var context = Context();
        return Disp(ForAll(
            [Bound("H", context.Function), Bound("K", context.Real), Bound("T", context.Real)],
            Implies(
                All(
                    Call("Integrable", context.H),
                    LessEqual(D(0), context.K),
                    Decay(context)),
                Call("Integrable", Lambda(
                    context.R,
                    context.Real,
                    Mul(Packet(context.H, context.T, context.R), Mu(context.R)))))));
    }

    private static Formula ArchimedeanLowerBound()
    {
        var context = Context();
        var weighted = ForAll(
            [Bound("S", context.Real)],
            Call("Integrable", Lambda(
                context.R,
                context.Real,
                Mul(Packet(context.H, context.S, context.R), Mu(context.R)))));
        var lower = Sub(
            Mul(
                Div(context.Delta, D(2)),
                Add(Mu(Sub(context.T, context.Delta)), D(1))),
            Integral(context.R, context.Real, Apply(context.H, context.R)));
        var packetIntegral = Integral(
            context.R,
            context.Real,
            Mul(Packet(context.H, context.T, context.R), Mu(context.R)));

        return Disp(ForAll(
            [
                Bound("H", context.Function),
                Bound("delta", context.Real),
                Bound("T", context.Real),
            ],
            Implies(
                All(
                    Call("Integrable", context.H),
                    Nonnegative(context),
                    Less(D(0), context.Delta),
                    LocalHalf(context),
                    weighted,
                    LessEqual(context.Delta, context.T)),
                LessEqual(lower, packetIntegral))));
    }

    private static Formula ArchimedeanDivergence()
    {
        var context = Context();
        var integralAtT = Integral(
            context.R,
            context.Real,
            Mul(Packet(context.H, context.T, context.R), Mu(context.R)));
        return Disp(ForAll(
            [
                Bound("H", context.Function),
                Bound("delta", context.Real),
                Bound("K", context.Real),
            ],
            Implies(
                All(
                    Call("Integrable", context.H),
                    Nonnegative(context),
                    Less(D(0), context.Delta),
                    LocalHalf(context),
                    LessEqual(D(0), context.K),
                    Decay(context)),
                Call(
                    "Tendsto",
                    Lambda(context.T, context.Real, integralAtT),
                    F.Id("atTop"),
                    F.Id("atTop")))));
    }

    private static Formula ArchimedeanDivergenceComplex()
    {
        var context = Context();
        var complexIntegral = Integral(
            context.R,
            context.Real,
            Mul(
                ComplexCast(Packet(context.H, context.T, context.R)),
                ComplexCast(Mu(context.R))));
        var realPart = Seq(Re, Open, complexIntegral, Close);
        return Disp(ForAll(
            [
                Bound("H", context.Function),
                Bound("delta", context.Real),
                Bound("K", context.Real),
            ],
            Implies(
                All(
                    Call("Integrable", context.H),
                    Nonnegative(context),
                    Less(D(0), context.Delta),
                    LocalHalf(context),
                    LessEqual(D(0), context.K),
                    Decay(context)),
                Call(
                    "Tendsto",
                    Lambda(context.T, context.Real, realPart),
                    F.Id("atTop"),
                    F.Id("atTop")))));
    }

    private static Formula GammaTermPacket()
    {
        var context = Context();
        var complexFunction = Arrow(context.Real, ComplexNumbers());
        var k = F.Id("k");
        var pointwise = ForAll(
            [Bound("r", context.Real)],
            Equal(
                Call("paperFT", k, context.R),
                ComplexCast(Packet(context.H, context.T, context.R))));
        var left = Mul(
            ComplexCast(Div(D(1), Mul(D(2), Pi))),
            Integral(
                context.R,
                context.Real,
                Mul(
                    Call("paperFT", k, context.R),
                    ComplexCast(Call("gammaBracket", context.R)))));
        var right = Integral(
            context.R,
            context.Real,
            Mul(
                ComplexCast(Packet(context.H, context.T, context.R)),
                ComplexCast(Mu(context.R))));
        return Disp(ForAll(
            [Bound("k", complexFunction), Bound("H", context.Function), Bound("T", context.Real)],
            Implies(pointwise, Equal(left, right))));
    }

    private static Formula Nonnegative(FormulaContext context) => ForAll(
        [Bound("r", context.Real)],
        LessEqual(D(0), Apply(context.H, context.R)));

    private static Formula LocalHalf(FormulaContext context) => ForAll(
        [Bound("t", context.Real)],
        Implies(
            LessEqual(new Formula.Absolute(context.LittleT), context.Delta),
            LessEqual(Div(D(1), D(2)), Apply(context.H, context.LittleT))));

    private static Formula Decay(FormulaContext context) => ForAll(
        [Bound("x", context.Real)],
        LessEqual(
            new Formula.Absolute(Apply(context.H, context.X)),
            Div(context.K, Add(D(1), new Formula.Power(context.X, D(2))))));

    private static Formula Packet(Formula h, Formula t, Formula r) =>
        Call("packet", h, t, r);

    private static Formula Mu(Formula r) => Call("mu", r);

    private static Formula ComplexNumbers() =>
        Seq(Mathbb, Grp(F.Id("C")));

    private static Formula ComplexCast(Formula value) =>
        Grp(value, Colon, Sp, ComplexNumbers());

    private static Formula Integral(Formula variable, Formula domain, Formula integrand) =>
        Seq(Int, Underscore, Grp(domain), Sp, integrand, Sp, F.Id("d"), variable);

    private static Formula Lambda(Formula variable, Formula domain, Formula body) =>
        Seq(Open, variable, Colon, Sp, domain, Sp, Mapsto, Sp, body, Close);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula ForAll(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Div(Formula numerator, Formula denominator) =>
        new Formula.Fraction(numerator, denominator);

    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula LessEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula All(params Formula[] formulas) =>
        formulas.Aggregate((left, right) =>
            new Formula.Logic(left, FormulaLogicOperator.And, right));

    private static FormulaContext Context() => new(
        Seq(Mathbb, Grp(F.Id("R"))),
        F.Id("H"),
        F.Id("T"),
        F.Id("S"),
        F.Id("r"),
        F.Id("t"),
        F.Id("x"),
        F.Id("delta"),
        F.Id("K"));

    private sealed record FormulaContext(
        Formula Real,
        Formula H,
        Formula T,
        Formula S,
        Formula R,
        Formula LittleT,
        Formula X,
        Formula Delta,
        Formula K)
    {
        public Formula Function => new Formula.TypeArrow(Real, Real);
    }
}
