using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.ZeroInfinitude;

internal sealed class ExplicitFormulaObstructionDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Weil/ZeroInfinitude/ExplicitFormulaObstruction.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The frozen unconditional explicit formula rules out every finite zero carrier, "
            + "so the nontrivial zeta-zero set is infinite and ZeroData is inhabited.",
        H("Explicit-Formula Obstruction to a Finite Zero Carrier"),
        Blocks(
            Paragraph(Text(
                "This closes the zero-infinitude argument of 增订三十 by contradiction. "
                    + "For a finite carrier, the zero side of the frozen explicit formula "
                    + "tends to zero along the cosine-modulated packet. Its right side instead "
                    + "diverges because the Archimedean term grows, while the pole terms vanish "
                    + "and the fixed-support prime term stays bounded.")),
            Paragraph(Text(
                "Applied to the repository's canonical zetaZeroConfig and its frozen "
                    + "unconditional EF_lit theorem, this proves that the full set of "
                    + "nontrivial zeta zeros is infinite. It is not Hardy's theorem asserting "
                    + "infinitely many zeros on the critical line.")),
            Paragraph(Text(
                "The Nonempty ZeroData theorem is a bind-only companion obtained through the "
                    + "frozen M1-a bridge. Neither zero infinitude nor that companion proves the "
                    + "Riemann hypothesis.")),
            Item(
                "paper-ft-cosine-modulation-packet",
                "paperFT_cosineModulation_packet",
                "The modulated transform is the translated real packet",
                PaperFTPacket(),
                "On the real axis, reality of the convolution-square transform identifies "
                    + "the complex transform with the real translated-packet profile."),
            Item(
                "packet-transform-re-decay",
                "packetTransform_re_decay",
                "The real packet transform has quadratic decay",
                PacketTransformDecay(),
                "The frozen closed-strip estimate dominates the absolute real part by the "
                    + "same quadratic majorant."),
            Item(
                "carrier-infinite-of-ef-lit",
                "carrier_infinite_of_EF_lit",
                "The explicit formula forces an infinite carrier",
                CarrierInfinite(),
                "The finite zero-side limit and the divergent literature right-hand side "
                    + "cannot both be the real part of the frozen explicit-formula identity."),
            Item(
                "zeta-zero-config-carrier-identification",
                "zetaZeroConfig_carrier_identification",
                "The canonical carrier is the nontrivial-zero set",
                CarrierIdentification(),
                "This public bridge binds the frozen carrier identification for zetaZeroConfig."),
            Item(
                "is-nontrivial-zero-infinite",
                "isNontrivialZero_infinite",
                "The nontrivial zeta-zero set is infinite",
                NontrivialZerosInfinite(),
                "The frozen unconditional explicit formula instantiates the carrier theorem, "
                    + "and the canonical carrier identification transports infinitude."),
            Item(
                "nonempty-zero-data",
                "nonempty_zeroData",
                "ZeroData is inhabited",
                NonemptyZeroData(),
                "This is the bind-only direction from zero infinitude through the frozen "
                    + "ZeroData nonemptiness equivalence.")),
        []));

    private static DocumentBlock.Describe Item(
        string id,
        string declaration,
        string heading,
        Formula formula,
        string prose) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(heading),
            StatementSource.FromAuthor(formula),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))),
            DescribeRole.Theorem);

    private static Formula PaperFTPacket()
    {
        Formula t = F.Id("T");
        Formula r = F.Id("r");
        Formula x = F.Id("t");
        Formula profile = Lambda(
            x,
            Reals(),
            RealPart(Call("paperFT", F.Id("packetSquare"), x)));
        Formula left = Call(
            "paperFT",
            Call("cosineModulation", F.Id("packetSquare"), t),
            r);
        Formula right = ComplexCast(Call("packet", profile, t, r));
        return Disp(ForAll(
            [Bound("T", Reals()), Bound("r", Reals())],
            Equal(left, right)));
    }

    private static Formula PacketTransformDecay()
    {
        Formula k = F.Id("K");
        Formula x = F.Id("x");
        Formula transform = Call("paperFT", F.Id("packetSquare"), x);
        Formula decay = LessEqual(
            new Formula.Absolute(RealPart(transform)),
            Div(k, Add(D(1), new Formula.Power(x, D(2)))));
        return Disp(Exists(
            [Bound("K", Reals())],
            And(
                LessEqual(D(0), k),
                ForAll([Bound("x", Reals())], decay))));
    }

    private static Formula CarrierInfinite()
    {
        Formula z = F.Id("Z");
        return Disp(ForAll(
            [Bound("Z", F.Id("ZeroConfig"))],
            Implies(
                Call("EFlit", z),
                Call("Infinite", Call("carrier", z)))));
    }

    private static Formula CarrierIdentification() => Disp(Equal(
        Call("carrier", F.Id("zetaZeroConfig")),
        NontrivialZeroSet()));

    private static Formula NontrivialZerosInfinite() =>
        Disp(Call("Infinite", NontrivialZeroSet()));

    private static Formula NonemptyZeroData() =>
        Disp(Call("Nonempty", F.Id("ZeroData")));

    private static Formula NontrivialZeroSet()
    {
        Formula rho = Rho;
        return new Formula.SetBuilder(
            Call("IsNontrivialZero", rho),
            rho,
            Complexes());
    }

    private static Formula Lambda(Formula variable, Formula domain, Formula body) =>
        Seq(Open, variable, Colon, Sp, domain, Sp, Mapsto, Sp, body, Close);

    private static Formula RealPart(Formula value) =>
        Seq(Re, Sp, Open, value, Close);

    private static Formula ComplexCast(Formula value) =>
        Grp(value, Colon, Sp, Complexes());

    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));

    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));

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

    private static Formula LessEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Div(Formula numerator, Formula denominator) =>
        new Formula.Fraction(numerator, denominator);
}
