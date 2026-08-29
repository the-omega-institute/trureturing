using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.TestFunctions;

internal sealed class WhiteToHaarIdentityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Weil/TestFunctions/WhiteToHaarIdentity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Resolvent-weighted Cayley compactification carries normalized white spectrum to "
            + "normalized circle Haar spectrum with the exact scale factor.",
        H("White to Haar Identity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("normalized-lebesgue-spectrum"),
                DeclarationHandle.Create(Prefix + "normalizedLebesgueSpectrum"),
                H("Normalized Lebesgue spectrum"),
                StatementSource.FromAuthor(NormalizedLebesgueFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The source white spectrum is constructed as Lebesgue measure on the real "
                        + "line scaled by the reciprocal of two pi."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cayley-circle-map"),
                DeclarationHandle.Create(Prefix + "cayleyCircle"),
                H("Cayley map into the unit circle"),
                StatementSource.FromAuthor(CayleyCircleFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The map is the canonical conjugate-over-self circle point. Its nonzero "
                        + "scale premise ensures that the denominator never vanishes."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("resolvent-compactification"),
                DeclarationHandle.Create(Prefix + "resolventCompactification"),
                H("Resolvent compactification"),
                StatementSource.FromAuthor(CompactificationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Compactification first weights the source measure by the reciprocal "
                        + "quadratic resolvent and then pushes it through the Cayley map."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("white-to-haar-identity"),
                DeclarationHandle.Create(Prefix + "white_to_haar_identity"),
                H("White spectrum becomes Haar spectrum"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "All binders and the positive-scale premise are displayed. The first "
                            + "two clauses give the base and arbitrary-intensity identities.")),
                    Paragraph(Text(
                        "The third clause reflects measure domination in both directions, so "
                            + "the real-line white floor and circle Haar floor are equivalent.")),
                    Paragraph(Text(
                        "At scale one half the coefficient is exactly one, giving the final "
                            + "scale-free correspondence."))),
                DescribeRole.Theorem))));

    private static Formula NormalizedLebesgueFormula()
    {
        Formula real = RealType();
        return Disp(Seq(
            White(), Colon, Sp, Call("Measure", real), Sp, Eq, Sp,
            Call("ofReal", new Formula.Fraction(D(1), Seq(D(2), Sp, Cdot, Sp, Pi))),
            Sp, Cdot, Sp,
            Call("volume", real), Dot));
    }

    private static Formula CayleyCircleFormula()
    {
        Formula a = F.Id("a");
        Formula h = F.Id("h");
        Formula xi = F.Id("xi");
        Formula real = RealType();
        Formula complex = Call("Complex");
        Formula numerator = Seq(
            Open, xi, Colon, Sp, complex, Close, Sp, Minus, Sp,
            F.Id("i"), Sp, Cdot, Sp, a);
        return Disp(Seq(
            Forall, Sp, a, Colon, Sp, real, Comma, Sp,
            h, Colon, Sp, a, Sp, Neq, Sp, D(0), Comma, Sp,
            xi, Colon, Sp, real, Comma, RowBreak, Grp(),
            Call("cayleyCircle", a, h, xi), Sp, Eq, Sp,
            Call("ofConjDivSelf", numerator), Colon, Sp, F.Id("Circle"), Dot));
    }

    private static Formula CompactificationFormula()
    {
        Formula a = F.Id("a");
        Formula h = F.Id("h");
        Formula nu = Nu;
        Formula xi = F.Id("xi");
        Formula real = RealType();
        Formula density = Call("ofReal", new Formula.Fraction(D(1), Seq(
            Call("sq", xi), Sp, Plus, Sp, Call("sq", a))));
        return Disp(Seq(
            Forall, Sp, a, Colon, Sp, real, Comma, Sp,
            h, Colon, Sp, a, Sp, Neq, Sp, D(0), Comma, Sp,
            nu, Colon, Sp, Call("Measure", real), Comma, RowBreak, Grp(),
            CompactificationWithProof(a, h, nu), Sp, Eq, Sp,
            Call("map", Call("cayleyCircle", a, h),
                Call("withDensity", nu,
                    Call("lambda", Seq(xi, Colon, Sp, real), density))), Dot));
    }

    private static Formula TheoremFormula()
    {
        Formula a = F.Id("a");
        Formula lambda = F.Id("lambda");
        Formula nu = Nu;
        Formula real = RealType();
        Formula ennreal = F.Id("ENNReal");
        Formula positive = Seq(D(0), Sp, Lt, Sp, a);
        Formula scale = Call("ofReal",
            new Formula.Fraction(D(1), Seq(D(2), Sp, Cdot, Sp, a)));
        Formula scaledWhite = Seq(lambda, Sp, Cdot, Sp, White());
        Formula scaledHaar = Seq(
            Open, lambda, Sp, Cdot, Sp, scale, Close, Sp, Cdot, Sp, Haar());
        Formula baseIdentity = Seq(
            Compactification(a, White()), Sp, Eq, Sp,
            scale, Sp, Cdot, Sp, Haar());
        Formula scaledIdentity = Seq(
            Compactification(a, scaledWhite), Sp, Eq, Sp, scaledHaar);
        Formula floorEquivalence = Seq(
            Open, scaledWhite, Sp, Leq, Sp, nu, Close, Sp, Leftrightarrow, Sp,
            Open, scaledHaar, Sp, Leq, Sp, Compactification(a, nu), Close);
        Formula half = new Formula.Fraction(D(1), D(2));
        Formula naturalIdentity = Seq(
            Compactification(half, scaledWhite), Sp, Eq, Sp,
            lambda, Sp, Cdot, Sp, Haar());

        return Disp(Seq(
            Forall, Sp, a, Colon, Sp, real, Comma, Sp,
            lambda, Colon, Sp, ennreal, Comma, Sp,
            nu, Colon, Sp, Call("Measure", real), Comma, RowBreak, Grp(),
            positive, Sp, Rightarrow, RowBreak, Grp(),
            Open, baseIdentity, Close, Sp, Land, RowBreak, Grp(),
            Open, scaledIdentity, Close, Sp, Land, RowBreak, Grp(),
            Open, floorEquivalence, Close, Sp, Land, RowBreak, Grp(),
            Open, naturalIdentity, Close, Dot));
    }

    private static Formula Compactification(Formula a, Formula measure) =>
        Call("resolventCompactification", a, measure);

    private static Formula CompactificationWithProof(Formula a, Formula h, Formula measure) =>
        Call("resolventCompactification", a, h, measure);

    private static Formula White() => Seq(F.Id("m"), Underscore, Grp(D(0)));

    private static Formula Haar() =>
        Seq(F.Id("m"), Underscore, Grp(F.Id("T")));

    private static Formula RealType() => Seq(Mathbb, Grp(F.Id("R")));

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        Apply(Seq(Operatorname, Grp(F.Id(name))), arguments);
}
