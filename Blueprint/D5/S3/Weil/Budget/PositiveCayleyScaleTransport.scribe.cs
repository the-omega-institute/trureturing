using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Budget;

internal sealed class PositiveCayleyScaleTransportDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Weil/Budget/PositiveCayleyScaleTransport.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Resolvent-weighted Cayley spectral measures obey the explicit positive "
            + "pushforward law under a change of scale.",
        H("Positive Cayley Scale Transport"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("resolvent-weighted-source-measure"),
                DeclarationHandle.Create(Prefix + "resolventWeightedMeasure"),
                H("Resolvent-weighted source measure"),
                StatementSource.FromAuthor(ResolventMeasureFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The density is constructed directly from the real spectral variable "
                        + "and the positive resolvent denominator."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cayley-spectral-measure"),
                DeclarationHandle.Create(Prefix + "cayleySpectralMeasure"),
                H("Cayley spectral measure"),
                StatementSource.FromAuthor(CayleyMeasureFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "This is the actual pushforward of the resolvent-weighted source "
                        + "measure by the scale-dependent Cayley coordinate."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("positive-scale-transport-weight"),
                DeclarationHandle.Create(Prefix + "scaleTransportWeight"),
                H("Positive scale-transport weight"),
                StatementSource.FromAuthor(TransportWeightFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The real weight is the source's explicit norm-square quotient."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("positive-cayley-scale-transport"),
                DeclarationHandle.Create(Prefix + "positive_cayley_scale_transport"),
                H("Positive scale transport"),
                StatementSource.FromAuthor(TransportFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The proof combines the pointwise resolvent-density identity with "
                        + "the Cayley scale-change law and functoriality of measure maps."))),
                DescribeRole.Theorem))));

    private static Formula ResolventMeasureFormula()
    {
        Formula source = F.Id("nu");
        Formula scale = F.Id("a");
        Formula spectral = F.Id("xi");
        Formula denominator = Seq(
            new Formula.Power(spectral, D(2)), Sp, Plus, Sp,
            new Formula.Power(scale, D(2)));
        Formula density = Call("ofReal", Fraction(D(1), denominator));
        return Disp(Seq(
            Forall, Sp, source, Colon, Sp, MeasureType(RealType()), Comma, Sp,
            scale, Colon, Sp, RealType(), Comma, Sp,
            WeightedMeasure(scale, source), Sp, Eq, Sp,
            Call("withDensity", source,
                Seq(spectral, Sp, Mapsto, Sp, density)), Dot));
    }

    private static Formula CayleyMeasureFormula()
    {
        Formula source = F.Id("nu");
        Formula scale = F.Id("a");
        return Disp(Seq(
            Forall, Sp, source, Colon, Sp, MeasureType(RealType()), Comma, Sp,
            scale, Colon, Sp, RealType(), Comma, Sp,
            SpectralMeasure(scale, source), Sp, Eq, Sp,
            Call("map", Cayley(scale), WeightedMeasure(scale, source)), Dot));
    }

    private static Formula TransportWeightFormula()
    {
        Formula a = F.Id("a");
        Formula b = F.Id("b");
        Formula z = F.Id("z");
        Formula r = ScaleParameter(a, b);
        Formula onePlusR = Seq(D(1), Sp, Plus, Sp, r);
        Formula numerator = Seq(
            Grp(onePlusR), Sp, Cdot, Sp, Grp(onePlusR));
        Formula denominator = Call("normSq", Seq(
            D(1), Sp, Plus, Sp, r, Sp, Cdot, Sp, z));
        return Disp(Seq(
            Forall, Sp, a, Comma, Sp, b, Colon, Sp, RealType(), Comma, Sp,
            z, Colon, Sp, ComplexType(), Comma, Sp,
            TransportWeight(a, b, z), Sp, Eq, Sp,
            Fraction(numerator, denominator), Dot));
    }

    private static Formula TransportFormula()
    {
        Formula source = F.Id("nu");
        Formula a = F.Id("a");
        Formula b = F.Id("b");
        Formula z = F.Id("z");
        Formula transportedDensity = Seq(
            z, Sp, Mapsto, Sp, Call("ofReal", TransportWeight(a, b, z)));
        Formula weightedAtA = Call(
            "withDensity", SpectralMeasure(a, source), transportedDensity);
        Formula pushforward = Call(
            "map", DiskAutomorphism(ScaleParameter(a, b)), weightedAtA);
        return Disp(Seq(
            Forall, Sp, source, Colon, Sp, MeasureType(RealType()), Comma, Sp,
            a, Comma, Sp, b, Colon, Sp, RealType(), Comma, Sp,
            D(0), Sp, Lt, Sp, a, Sp, Land, Sp, D(0), Sp, Lt, Sp, b,
            Sp, Rightarrow, RowBreak, Grp(),
            SpectralMeasure(b, source), Sp, Eq, Sp, pushforward, Dot));
    }

    private static Formula WeightedMeasure(Formula scale, Formula source) =>
        Apply(new Formula.Subscript(F.Id("W"), scale), source);

    private static Formula SpectralMeasure(Formula scale, Formula source) =>
        Apply(new Formula.Subscript(F.Id("mu"), scale), source);

    private static Formula TransportWeight(Formula a, Formula b, Formula z) =>
        Apply(new Formula.Subscript(F.Id("q"), Seq(a, Comma, b)), z);

    private static Formula ScaleParameter(Formula a, Formula b) =>
        new Formula.Subscript(F.Id("r"), Seq(a, Comma, b));

    private static Formula Cayley(Formula scale) =>
        new Formula.Subscript(F.Id("c"), scale);

    private static Formula DiskAutomorphism(Formula parameter) =>
        Apply(Seq(Operatorname, Grp(F.Id("Phi"))), parameter);

    private static Formula RealType() => Seq(Mathbb, Grp(F.Id("R")));

    private static Formula ComplexType() => Seq(Mathbb, Grp(F.Id("C")));

    private static Formula MeasureType(Formula carrier) => Call("Measure", carrier);

    private static Formula Fraction(Formula numerator, Formula denominator) =>
        Seq(Frac, Grp(numerator), Grp(denominator));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);
}
