using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.QuadraticIdeals;

internal sealed class EisensteinOddQuotientDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Factorization/QuadraticIdeals/EisensteinOddQuotient."
        + "eisenstein_odd_scalar_quotient";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An odd-parameter Eisenstein factor has a scalar contraction equal to its norm ideal "
            + "and a scalar quotient isomorphism.",
        H("Scalar Quotients of Oriented Eisenstein Factors"),
        Blocks(Describe.Lean(
            DescribeId.Create("eisenstein-odd-scalar-contraction-quotient"),
            DeclarationHandle.Create(Declaration),
            H("The oriented factor contracts to its norm ideal"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let E be the quadratic algebra Z[omega] with omega squared plus omega "
                        + "plus one equal to zero. For an odd natural number b, set eta equal "
                        + "to -2 + b omega and B equal to b squared plus 2b plus 4.")),
                Paragraph(Text(
                    "If eta times (u + v omega) is scalar, its omega coefficient gives "
                        + "bu = (b + 2)v. Oddness makes b and b + 2 coprime, so u = (b + 2)t "
                        + "and v = bt. The scalar product is then -Bt. Conversely, an explicit "
                        + "multiple of eta has scalar value B, giving the exact contraction.")),
                Paragraph(Text(
                    "The scalar map to E modulo eta has kernel BZ. Also b and B are coprime: "
                        + "B is congruent to four modulo b and b is odd. In the quotient, "
                        + "b omega = 2 and B = 0. Bezout coefficients therefore express omega "
                        + "as a scalar class. Every quotient class has a representative "
                        + "u + v omega, so the scalar map is surjective and induces the "
                        + "displayed ring equivalence with the stated action on integers."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula b = F.Id("b");
        Formula n = F.Id("n");
        Formula bound = Call("blockNorm", b);
        Formula contraction = Seq(
            Open, Forall, Sp, n, Colon, Sp, F.Id("Z"), Comma, Sp,
            Call("Dvd", Call("orientedFactor", b), Call("C", n)),
            Sp, Iff, Sp, Call("Dvd", bound, n), Close);
        Formula quotient = Call("OrientedQuotient", b);
        Formula equivalence = Seq(
            Open, Exists, Sp, F.Id("e"), Colon, Sp,
            Call("RingEquiv", Call("ZMod", bound), quotient), Comma, Sp,
            Forall, Sp, n, Colon, Sp, F.Id("Z"), Comma, Sp,
            Call("e", Call("IntClass", n)), Sp, Eq, Sp,
            Call("scalarMap", b, n), Close);

        return Disp(Seq(
            Forall, Sp, b, Colon, Sp, F.Id("OddNatural"), Comma, Sp,
            contraction, Sp, Land, RowBreak, Grp(), equivalence, Dot));
    }
}
