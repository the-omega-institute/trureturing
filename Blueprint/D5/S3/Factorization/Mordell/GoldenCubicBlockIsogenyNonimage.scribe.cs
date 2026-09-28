using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Mordell;

internal sealed class GoldenCubicBlockIsogenyNonimageDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Factorization/Mordell/GoldenCubicBlockIsogenyNonimage.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The two canonical points of every positive cubic-block layer have no rational preimage under the explicit cubic map.",
        H("Cubic Map Nonimage on Actual Golden Blocks"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("cubic-isogeny-affine-image"),
                DeclarationHandle.Create(Prefix + "CubicIsogenyAffineImage"),
                H("The explicit affine image relation"),
                StatementSource.FromAuthor(ImageFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The source coordinates s,t satisfy t squared equals s cubed minus "
                        + "27b, with s nonzero. The target coordinates are "
                        + "X=(s cubed minus 108b)/(9s squared) and "
                        + "Y=t(s cubed plus 216b)/(27s cubed). This relation is defined "
                        + "only for finite rational source coordinates with s nonzero."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("actual-block-cubic-isogeny-nonimage"),
                DeclarationHandle.Create(Prefix + "actual_block_cubic_isogeny_nonimage"),
                H("Neither canonical point has a rational affine preimage"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every j at least one, d_j is the cubefree factor and c_j is "
                            + "the cube-part root of B_j=L_(3^j)^2+3. The negative-twist "
                            + "point has coordinates (d_j c_j,d_j L_(3^j)); the "
                            + "positive-twist point has coordinates "
                            + "(5d_j c_j,25d_j F_(3^j)). Neither belongs to the "
                            + "rational affine image relation at its displayed curve constant.")),
                    Paragraph(Text(
                        "A prime factor of B_j with cubefree exponent one or two exists "
                            + "because B_j is not a cube. The block congruences exclude "
                            + "the primes two, three and five. At that prime, the target "
                            + "abscissa has valuation e+k and the curve constant has "
                            + "valuation 2e, with e equal to one or two and k nonnegative. "
                            + "The equation s^3=9Xs^2+108b has a unique least valuation "
                            + "among its terms for every integer valuation of s, so it "
                            + "has no nonzero rational solution.")),
                    Paragraph(Text(
                        "The formal image relation uses the stated affine formulas. "
                            + "A group-homomorphism construction and degree calculation "
                            + "for the global isogeny are not part of this statement."))),
                DescribeRole.Theorem))));

    private static Formula Sub(string symbol, string index) =>
        new Formula.Subscript(F.Id(symbol), F.Id(index));

    private static Formula Sub(string symbol, Formula index) =>
        new Formula.Subscript(F.Id(symbol), index);

    private static Formula ImageFormula()
    {
        Formula b = F.Id("b");
        Formula x = F.Id("X");
        Formula y = F.Id("Y");
        Formula s = F.Id("s");
        Formula t = F.Id("t");
        Formula s3 = new Formula.Power(s, D(3));
        Formula s2 = new Formula.Power(s, D(2));
        return Disp(Seq(
            Call("CubicIsogenyAffineImage", b, x, y), Sp, Iff, Sp,
            Exists, Sp, s, Comma, Sp, t, Sp, InMacro, Sp, Mathbb, Grp(F.Id("Q")),
            Comma, Sp, s, Sp, Neq, Sp, D(0), Sp, Land, Sp,
            new Formula.Power(t, D(2)), Sp, Eq, Sp, s3, Sp, Minus, Sp, D(2, 7), b,
            Sp, Land, Sp, x, Sp, Eq, Sp,
            new Formula.Fraction(Seq(s3, Sp, Minus, Sp, D(1, 0, 8), b),
                Seq(D(9), s2)),
            Sp, Land, Sp, y, Sp, Eq, Sp,
            new Formula.Fraction(Seq(t, Grp(Seq(s3, Sp, Plus, Sp, D(2, 1, 6), b))),
                Seq(D(2, 7), s3))));
    }

    private static Formula TheoremFormula()
    {
        Formula j = F.Id("j");
        Formula d = Sub("d", "j");
        Formula c = Sub("c", "j");
        Formula index = new Formula.Power(D(3), j);
        Formula lucas = Sub("L", index);
        Formula fib = Sub("F", index);
        Formula d2 = new Formula.Power(d, D(2));
        return Disp(Seq(
            Forall, Sp, j, Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
            D(1), Sp, Le, Sp, j, Sp, Rightarrow, Sp,
            Neg, Call("CubicIsogenyAffineImage", Seq(Minus, D(3), d2),
                Seq(d, c), Seq(d, lucas)), Sp, Land, Sp,
            Neg, Call("CubicIsogenyAffineImage", Seq(D(1, 2, 5), d2),
                Seq(D(5), d, c), Seq(D(2, 5), d, fib))));
    }
}
