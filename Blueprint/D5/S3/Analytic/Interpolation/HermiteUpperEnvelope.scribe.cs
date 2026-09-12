using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Interpolation;

internal sealed class HermiteUpperEnvelopeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A positive third derivative makes the Hermite quadratic an upper bound, and matching two moments evaluates its sum.",
        H("Hermite upper envelope"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("hermite-remainder-on-open-domain"),
                DeclarationHandle.Create("D5/S3/Analytic/Interpolation/HermiteUpperEnvelope.hermite_two_point_remainder_on"),
                H("Remainder on an open domain"),
                StatementSource.FromAuthor(BridgeFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Let s be an open subset of the real line containing the closed interval from L to H, and let x lie strictly between L and H. Assume f and p are three times continuously differentiable on s, the third derivative of p is zero on s, p and f agree in value and first derivative at L, and they agree in value at H. If the third derivative of f is positive between the nodes, there is a point z strictly between them with the following remainder and strict sign. A smooth extension near the closed interval permits the usual Hermite remainder formula to apply."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("hermite-upper-envelope"),
                DeclarationHandle.Create("D5/S3/Analytic/Interpolation/HermiteUpperEnvelope.hermite_upper_envelope"),
                H("An upper bound determined by the mean and variance"),
                StatementSource.FromAuthor(EnvelopeFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let k be a natural number at least two and let every coordinate x indexed by Fin k be a positive real number. Let m be the arithmetic mean and V the total squared deviation, without division by k. Define the radius r and nodes L and H as follows.")),
                    Paragraph(Math(Disp(DefinitionsFormula()))),
                    Paragraph(Math(Disp(Seq(F.Id("f"), Open, F.Id("t"), Close, Sp, Eq, Sp,
                        Log, Open, D(1), Minus, Exp, Open, Minus, F.Id("t"), Close, Close)))),
                    Paragraph(Text(
                        "The moment bounds give a positive L and place every coordinate at or below H. If V is zero, all coordinates equal m and both sides coincide. Otherwise L is strictly below H. Take the quadratic p agreeing with f in value and first derivative at L and in value at H.")),
                    Paragraph(Text(
                        "For a coordinate between the nodes the remainder formula gives f less than p. For a positive coordinate to the left of L, suppose f minus p were nonnegative. Two applications of the mean value theorem then give a nonnegative second derivative to the left of L, while two applications of Rolle's theorem give a zero second derivative to its right. This contradicts strict increase of the second derivative. At either node the values agree.")),
                    Paragraph(Text(
                        "Writing the quadratic in powers of t-L reduces its sum to the first and second displacement moments. These equal kr and k squared times r squared, respectively, since V equals k(k-1) times r squared. Thus the quadratic sum equals p(H)+(k-1)p(L), which gives the stated bound after substitution."))),
                DescribeRole.Theorem))));

    private static Formula BridgeFormula()
    {
        Formula x = F.Id("x");
        Formula z = F.Id("z");
        Formula l = F.Id("L");
        Formula h = F.Id("H");
        Formula difference = Seq(Call("f", x), Minus, Call("p", x));
        return Disp(Seq(
            Exists, Sp, z, Sp, InMacro, Sp, Open, l, Comma, h, Close, Colon, Sp,
            difference, Sp, Eq, Sp, Frac,
            Grp(Call("iteratedDeriv", D(3), F.Id("f"), z)), Grp(D(6)),
            Open, x, Minus, l, Close, Caret, Grp(D(2)), Open, x, Minus, h, Close,
            Sp, Land, Sp, difference, Sp, Lt, Sp, D(0)));
    }

    private static Formula DefinitionsFormula()
    {
        Formula i = F.Id("i");
        Formula k = F.Id("k");
        Formula m = F.Id("m");
        Formula v = F.Id("V");
        Formula r = F.Id("r");
        Formula sum = Seq(Sum, Underscore, Grp(i, Sp, InMacro, Sp, Call("Fin", k)), Sp);
        return Seq(
            m, Sp, Eq, Sp, Frac, Grp(sum, Call("x", i)), Grp(k), Comma, Sp,
            v, Sp, Eq, Sp, sum, Open, Call("x", i), Minus, m, Close, Caret, Grp(D(2)), Comma, Sp,
            r, Sp, Eq, Sp, Sqrt, Grp(Frac, Grp(v), Grp(k, Open, k, Minus, D(1), Close)), Comma, Sp,
            F.Id("L"), Sp, Eq, Sp, m, Minus, r, Comma, Sp,
            F.Id("H"), Sp, Eq, Sp, m, Plus, Open, k, Minus, D(1), Close, r);
    }

    private static Formula EnvelopeFormula()
    {
        Formula i = F.Id("i");
        Formula k = F.Id("k");
        return Disp(Seq(
            Forall, Sp, k, Colon, Sp, Call("Nat"), Comma, Sp,
            Forall, Sp, F.Id("x"), Colon, Sp, Call("Fin", k), Sp, To, Sp, Call("Real"), Comma, Sp,
            Open, D(2), Sp, Le, Sp, k, Sp, Land, Sp,
            Open, Forall, Sp, i, Colon, Sp, Call("Fin", k), Comma, Sp,
                D(0), Sp, Lt, Sp, Call("x", i), Close, Close, Sp, Implies, Sp,
            Sum, Underscore, Grp(i, Sp, InMacro, Sp, Call("Fin", k)), Sp, Call("f", Call("x", i)),
            Sp, Le, Sp, Call("f", F.Id("H")), Plus, Open, k, Minus, D(1), Close, Call("f", F.Id("L"))));
    }
}
