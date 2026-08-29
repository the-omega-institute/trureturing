using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Budget;

internal sealed class LinearCayleyScaleFlowDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Weil/Budget/LinearCayleyScaleFlow.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The canonical logarithmic Cayley flow has a transport-decay generator and "
            + "invariant characteristics.",
        H("Linear Cayley Scale Flow"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("cayley-characteristic"),
                DeclarationHandle.Create(Prefix + "cayleyCharacteristic"),
                H("Cayley characteristic"),
                StatementSource.FromAuthor(CharacteristicFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The characteristic is the imported real disk automorphism with the "
                        + "negative half-time hyperbolic parameter."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("disk-artanh"),
                DeclarationHandle.Create(Prefix + "diskArtanh"),
                H("Disk artanh branch"),
                StatementSource.FromAuthor(ArtanhFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "This half-log expression fixes the analytic branch on the complex "
                        + "unit disk."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("linear-cayley-scale-pde"),
                DeclarationHandle.Create(Prefix + "linear_cayley_scale_pde"),
                H("Linear Cayley scale PDE"),
                StatementSource.FromAuthor(FlowFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Differentiation under the finite resolvent integral supplies the "
                        + "spatial derivative. The imported finite scale-covariance law "
                        + "then gives the time generator, while the explicit characteristic "
                        + "makes the disk-artanh coordinate invariant."))),
                DescribeRole.Theorem))));

    private static Formula CharacteristicFormula()
    {
        Formula seed = F.Id("u");
        Formula tau = F.Id("tau");
        Formula parameter = Call("tanh", Negate(Fraction(tau, D(2))));
        return Disp(Seq(
            Forall, Sp, seed, Colon, Sp, ComplexType(), Comma, Sp,
            tau, Colon, Sp, RealType(), Comma, Sp,
            Characteristic(seed, tau), Sp, Eq, Sp,
            DiskAutomorphism(parameter, seed), Dot));
    }

    private static Formula ArtanhFormula()
    {
        Formula w = F.Id("w");
        return Disp(Seq(
            Forall, Sp, w, Colon, Sp, ComplexType(), Comma, Sp,
            DiskArtanh(w), Sp, Eq, Sp,
            Fraction(Seq(
                Call("log", Seq(D(1), Sp, Plus, Sp, w)), Sp, Minus, Sp,
                Call("log", Seq(D(1), Sp, Minus, Sp, w))), D(2)), Dot));
    }

    private static Formula FlowFormula()
    {
        Formula source = F.Id("nu");
        Formula scale = F.Id("a");
        Formula tau = F.Id("tau");
        Formula t = F.Id("t");
        Formula w = F.Id("w");
        Formula seed = F.Id("u");
        Formula x = F.Id("x");
        Formula flowAtTau = Caratheodory(Call("exp", tau), source, w);
        Formula spatialDerivative = Call(
            "deriv",
            Seq(w, Sp, Mapsto, Sp, Caratheodory(Call("exp", tau), source, w)),
            w);
        Formula pdeDerivative = Seq(
            Fraction(Seq(D(1), Sp, Minus, Sp, Square(w)), D(2)),
            Sp, Cdot, Sp, spatialDerivative, Sp, Minus, Sp, flowAtTau);
        Formula pde = Call(
            "HasDerivAt",
            Seq(t, Sp, Mapsto, Sp, Caratheodory(Call("exp", t), source, w)),
            pdeDerivative,
            tau);
        Formula characteristicAtTau = Characteristic(seed, tau);
        Formula characteristic = Call(
            "HasDerivAt",
            Seq(t, Sp, Mapsto, Sp, Characteristic(seed, t)),
            Negate(Fraction(
                Seq(D(1), Sp, Minus, Sp, Square(characteristicAtTau)), D(2))),
            tau);
        Formula invariant = Call(
            "HasDerivAt",
            Seq(t, Sp, Mapsto, Sp,
                DiskArtanh(Characteristic(seed, t)), Sp, Plus, Sp,
                Fraction(Call("ofReal", t), D(2))),
            D(0),
            tau);
        Formula evenness = Seq(
            Call("map", Seq(x, Sp, Mapsto, Sp, Minus, Sp, x), source),
            Sp, Eq, Sp, source);
        Formula finiteAtEveryScale = Seq(
            Forall, Sp, scale, Colon, Sp, RealType(), Comma, Sp,
            D(0), Sp, Lt, Sp, scale, Sp, Rightarrow, Sp,
            Call("FiniteMeasure", WeightedMeasure(scale, source)));
        Formula hypotheses = Seq(
            evenness, Sp, Land, RowBreak, Grp(),
            Grp(finiteAtEveryScale), Sp, Land, RowBreak, Grp(),
            new Formula.Norm(w), Sp, Lt, Sp, D(1), Sp, Land, Sp,
            new Formula.Norm(seed), Sp, Lt, Sp, D(1));
        return Disp(Seq(
            Forall, Sp, source, Colon, Sp, MeasureType(RealType()), Comma, Sp,
            tau, Colon, Sp, RealType(), Comma, Sp,
            w, Comma, Sp, seed, Colon, Sp, ComplexType(), Comma, RowBreak, Grp(),
            hypotheses, Sp, Rightarrow, RowBreak, Grp(),
            Grp(pde), Sp, Land, RowBreak, Grp(),
            Grp(characteristic), Sp, Land, RowBreak, Grp(), Grp(invariant), Dot));
    }

    private static Formula Characteristic(Formula seed, Formula tau) =>
        Call("chi", seed, tau);

    private static Formula DiskArtanh(Formula w) => Call("diskArtanh", w);

    private static Formula Caratheodory(
        Formula scale,
        Formula source,
        Formula w) => Call("F", scale, source, w);

    private static Formula WeightedMeasure(Formula scale, Formula source) =>
        Apply(new Formula.Subscript(F.Id("W"), scale), source);

    private static Formula DiskAutomorphism(Formula parameter, Formula w) =>
        Call("Phi", parameter, w);

    private static Formula Square(Formula value) => new Formula.Power(Seq(value), D(2));

    private static Formula Negate(Formula value) => Seq(Minus, Sp, value);

    private static Formula RealType() => Seq(Mathbb, Grp(F.Id("R")));

    private static Formula ComplexType() => Seq(Mathbb, Grp(F.Id("C")));

    private static Formula MeasureType(Formula carrier) => Call("Measure", carrier);

    private static Formula Fraction(Formula numerator, Formula denominator) =>
        Seq(Frac, Grp(numerator), Grp(denominator));

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (int i = 0; i < arguments.Length; i++)
        {
            if (i > 0)
            {
                items.Add(Comma);
                items.Add(Sp);
            }

            items.Add(arguments[i]);
        }

        items.Add(Close);
        return Seq(items.ToArray());
    }
}
