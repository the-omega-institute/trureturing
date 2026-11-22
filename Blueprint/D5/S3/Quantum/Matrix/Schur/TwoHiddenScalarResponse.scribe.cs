using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Matrix.Schur;

internal sealed class TwoHiddenScalarResponseDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The four scalar coordinates of a two-hidden-site Schur response have an exact image.",
        H("Two-hidden-site scalar Schur response"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("two-hidden-scalar-response"),
                DeclarationHandle.Create("D5/S3/Quantum/Matrix/Schur/TwoHiddenScalarResponse.response_iff"),
                H("Exact image for an allowed set of mixing parameters"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For nonzero t, set h = e + tf and k = te + f. The four outputs are "
                        + "products along the path k, b, d, h, a, with a nonzero factor on the "
                        + "edge between b and d. A zero product between two nonzero products is "
                        + "impossible, because the neighboring products force both of its factors "
                        + "to be nonzero. These are exactly the two displayed disjunctions. "
                        + "Conversely, when β = γ = 0 one may take d = 0 and b = h = 1. "
                        + "When β = 0 and γ is nonzero one takes b = 0 and h = 1. "
                        + "When β is nonzero one takes d = 1, b = −β/t and h = −γ. "
                        + "In each case the remaining weights realize the outer products. "
                        + "The formulas e = (h − tk)/(1 − t²) and f = k − te recover the two amplitudes.")),
                    Paragraph(Text(
                        "At t = 0 the first coordinate vanishes and the other three are arbitrary. "
                        + "For a fixed t, take the singleton set of mixing parameters. "
                        + "For the real interval (−1, 1), take t = 0 when β = 0 and t = 1/2 "
                        + "when β is nonzero and the second disjunction holds. The exact interval "
                        + "image is γ ≠ 0 or β = 0 or ε = 0."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "Use the real basis (1, z) of the complex plane with z nonreal. Let the boundary "
                + "coupling X have rows (a, bz), (d, 0), (e, f), and let the hidden inverse P have "
                + "unit diagonal and off-diagonal t. In the reduction D − XPX†, the z coefficient "
                + "of AB, the real coefficient of BC, and the real and z coefficients of AC are "
                + "the four displayed outputs when the direct AB bond is real, the direct BC bond "
                + "is on the z line, and the direct AC bond is zero. Choose the two allowed direct "
                + "bond coefficients to compensate the remaining induced coefficients. For a "
                + "reduced target Y, set Dᵢᵢ = Yᵢᵢ + (XPX†)ᵢᵢ to prescribe the real diagonals.")),
            Paragraph(Text(
                "For |t| < 1, P is positive definite. Completing the square in the hidden "
                + "variables makes the full network positive definite exactly when Y is positive "
                + "definite. The decomposition is Mathlib's Matrix.schur_complement_eq₂₂, and "
                + "SchurMinimum.schur_quadratic_is_least gives the attained boundary minimum. "
                + "Any attainable off-diagonal data admit a positive definite completion by "
                + "choosing each reduced diagonal greater than the sum of the moduli of the other "
                + "entries in its row.")),
            Paragraph(Text(
                "For the Chapter 39 wound target with |z| = 1, the off-diagonal entries "
                + "p conjugate(z), qz², rz have coordinates (β, γ, ε, ζ) = (−p, −q, 0, r). "
                + "This follows from conjugate(z) = 2 Re(z) − z and z² = 2 Re(z)z − 1. "
                + "The interval criterion therefore holds for all real p, q, r, including zeros. "
                + "With a positive definite wound target this gives a positive definite lift in "
                + "the prescribed local network. The Lean statement classifies the scalar equations. "
                + "The phase-coordinate and positive definite interpretations use the matrix "
                + "decomposition above.")))));

    private static Formula Statement()
    {
        var field = F.Id("K");
        var set = F.Id("T");
        var t = F.Id("t");
        var a = F.Id("a");
        var b = F.Id("b");
        var d = F.Id("d");
        var e = F.Id("e");
        var f = F.Id("f");
        var zero = D(0);
        var member = Seq(t, Sp, InMacro, Sp, set);
        var h = Paren(Seq(e, Sp, Plus, Sp, t, Sp, f));
        var k = Paren(Seq(t, Sp, e, Sp, Plus, Sp, f));
        var nonsingular = Paren(Seq(Forall, Sp, member, Comma, Sp, t, Sp, t, Sp, Neq, Sp, D(1)));
        var equations = Paren(Seq(
            Exists, Sp, member, Comma, Sp, Exists, Sp,
            a, Comma, Sp, b, Comma, Sp, d, Comma, Sp, e, Comma, Sp, f, Colon, Sp, field, Comma, Sp,
            Beta, Sp, Eq, Sp, Minus, b, Sp, d, Sp, t, Sp, Land, Sp,
            GammaLower, Sp, Eq, Sp, Minus, d, Sp, h, Sp, Land, Sp,
            Varepsilon, Sp, Eq, Sp, Minus, a, Sp, h, Sp, Land, Sp,
            Zeta, Sp, Eq, Sp, Minus, b, Sp, k));
        var zeroMixing = Paren(Seq(zero, Sp, InMacro, Sp, set, Sp, Land, Sp, Beta, Sp, Eq, Sp, zero));
        var nonzeroMixing = Paren(Seq(
            Paren(Seq(Exists, Sp, member, Comma, Sp, t, Sp, Neq, Sp, zero)), Sp, Land, Sp,
            Paren(Seq(Beta, Sp, Neq, Sp, zero, Sp, Lor, Sp,
                GammaLower, Sp, Eq, Sp, zero, Sp, Lor, Sp, Zeta, Sp, Eq, Sp, zero)), Sp, Land, Sp,
            Paren(Seq(GammaLower, Sp, Neq, Sp, zero, Sp, Lor, Sp,
                Beta, Sp, Eq, Sp, zero, Sp, Lor, Sp, Varepsilon, Sp, Eq, Sp, zero))));
        return Disp(Seq(
            Forall, Sp, Paren(Seq(field, Colon, Sp, F.Id("Type"))), Sp,
            OpenBracket, F.Id("Field"), Sp, field, CloseBracket, Sp,
            Paren(Seq(set, Colon, Sp, F.Id("Set"), Sp, field)), Sp,
            Paren(Seq(Beta, Comma, Sp, GammaLower, Comma, Sp,
                Varepsilon, Comma, Sp, Zeta, Sp, Colon, Sp, field)), Comma, Sp,
            nonsingular, Sp, Implies, Sp,
            Paren(Seq(equations, Sp, Iff, Sp, Paren(Seq(zeroMixing, Sp, Lor, Sp, nonzeroMixing))))));
    }

    private static Formula Paren(Formula formula) => Seq(Open, formula, Close);
}
