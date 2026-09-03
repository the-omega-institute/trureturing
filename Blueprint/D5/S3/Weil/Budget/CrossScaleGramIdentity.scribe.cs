using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Budget;

internal sealed class CrossScaleGramIdentityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integer moments at one positive Cayley scale are Gram pairings of the explicit "
            + "rational features transported from another positive scale.",
        H("Cross-Scale Gram Identity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("cross-scale-gram-identity"),
                DeclarationHandle.Create(
                    "D5/S3/Weil/Budget/CrossScaleGramIdentity."
                        + "cross_scale_gram_identity"),
                H("Transported moments are rational-feature Gram pairings"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The displayed statement constructs the scale parameter, every "
                            + "integer moment, and every rational feature from the supplied "
                            + "positive real measure and the canonical Cayley primitives.")),
                    Paragraph(Text(
                        "The proof applies positive Cayley scale transport and then identifies "
                            + "its density pointwise with the product of a feature and the "
                            + "complex conjugate of a second feature."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula real = RealType();
        Formula natural = NaturalType();
        Formula integer = IntegerType();
        Formula complex = ComplexType();
        Formula source = F.Id("nu");
        Formula a = F.Id("a");
        Formula b = F.Id("b");
        Formula j = F.Id("j");
        Formula k = F.Id("k");
        Formula scale = F.Id("s");
        Formula n = F.Id("n");
        Formula index = F.Id("ell");
        Formula z = F.Id("z");
        Formula r = F.Id("r");
        Formula moment = F.Id("m");
        Formula feature = F.Id("e");

        Formula rDefinition = Seq(
            Operatorname, Grp(F.Id("let")), Sp,
            Typed(r, real), Sp, Colon, Eq, Sp,
            Fraction(
                Seq(a, Sp, Minus, Sp, b),
                Seq(a, Sp, Plus, Sp, b)), Comma);

        Formula momentDefinition = Seq(
            Operatorname, Grp(F.Id("let")), Sp,
            Typed(moment, Arrow(real, Arrow(integer, complex))), Sp, Colon, Eq, Sp,
            Lambda(
                Seq(Typed(scale, real), Comma, Sp, Typed(n, integer)),
                Call(
                    "integral",
                    Call("cayleySpectralMeasure", source, scale),
                    Lambda(Typed(z, complex), Power(z, n)))), Comma);

        Formula coefficient = Fraction(
            Call("sqrt", Seq(D(1), Sp, Minus, Sp, Power(r, D(2)))),
            Seq(D(1), Sp, Plus, Sp, r, Sp, Cdot, Sp, z));
        Formula transportedCoordinate =
            Apply(new Formula.Subscript(Phi, r), z);
        Formula featureDefinition = Seq(
            Operatorname, Grp(F.Id("let")), Sp,
            Typed(feature, Arrow(natural, Arrow(complex, complex))), Sp, Colon, Eq, Sp,
            Lambda(
                Seq(Typed(index, natural), Comma, Sp, Typed(z, complex)),
                Seq(coefficient, Sp, Cdot, Sp,
                    Power(transportedCoordinate, index))), Comma);

        Formula left = Apply(
            moment,
            b,
            Seq(j, Sp, Minus, Sp, k));
        Formula featureJ = Apply(feature, j, z);
        Formula featureKConjugate = Seq(
            Overline, Grp(Apply(feature, k, z)));
        Formula gram = Call(
            "integral",
            Call("cayleySpectralMeasure", source, a),
            Lambda(
                Typed(z, complex),
                Seq(featureJ, Sp, Cdot, Sp, featureKConjugate)));
        Formula right = Seq(
            Fraction(a, b), Sp, Cdot, Sp, gram);

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, Typed(source, Call("Measure", real)), Comma, Sp,
                Typed(a, real), Comma, Sp, Typed(b, real), Comma, Sp,
                Typed(j, natural), Comma, Sp, Typed(k, natural), Comma),
            Seq(
                D(0), Sp, Lt, Sp, a, Sp, Land, Sp,
                D(0), Sp, Lt, Sp, b, Sp, Rightarrow),
            rDefinition,
            momentDefinition,
            featureDefinition,
            Seq(left, Sp, Eq, Sp, right, Dot),
        ]));
    }

    private static Formula Lambda(Formula binder, Formula body) =>
        Seq(Open, binder, Close, Sp, Mapsto, Sp, body);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Power(Formula value, Formula exponent) =>
        new Formula.Power(value, exponent);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        Seq(domain, Sp, To, Sp, codomain);

    private static Formula Fraction(Formula numerator, Formula denominator) =>
        new Formula.Fraction(numerator, denominator);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula RealType() => Seq(Mathbb, Grp(F.Id("R")));

    private static Formula NaturalType() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula IntegerType() => Seq(Mathbb, Grp(F.Id("Z")));

    private static Formula ComplexType() => Seq(Mathbb, Grp(F.Id("C")));
}
