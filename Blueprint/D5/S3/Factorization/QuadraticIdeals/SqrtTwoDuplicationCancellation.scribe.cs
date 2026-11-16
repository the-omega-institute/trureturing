using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.QuadraticIdeals;

internal sealed class SqrtTwoDuplicationCancellationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Local cancellation of primitive homogeneous duplication forms over Z[sqrt(2)].",
        H("Primitive Duplication over the Square-Root-Two Order"),
        Blocks(Describe.Lean(
            DescribeId.Create("sqrt-two-primitive-duplication-local"),
            DeclarationHandle.Create("D5/S3/Factorization/QuadraticIdeals/SqrtTwoDuplicationCancellation.primitive_duplication_local"),
            H("Two exceptional prime ideals and their cancellation bounds"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromLiterature(
                LibraryNoteRef.Create("D5/L/Factorization/anonymous2026quarticvthirteen")),
            Blocks(
                Paragraph(Text(
                    "Let O be the explicit quadratic order Z[sqrt(2)], s = sqrt(2), and delta = 3 - s. "
                    + "For a and b in O define F = (a^2 + delta^2 b^2)^2, "
                    + "G = 4ab(a^2 - delta^2 b^2), and I = (F,G). "
                    + "The hypothesis (a,b) = O is ideal-theoretic primitivity. "
                    + "No nonvanishing hypothesis is imposed on either coordinate or either duplication form.")),
                Paragraph(Text(
                    "The numerator alone is not divisible by s^7 or delta^5. "
                    + "For the dyadic bound, divisibility by s^7 would make the real coordinate of F divisible by sixteen. "
                    + "Twice applying the parity obstruction for X^2 + 2Y^2 modulo four "
                    + "makes both coordinates of a^2 + (delta b)^2 divisible by four. "
                    + "The real and imaginary coordinate congruences then force both a and b to be divisible by s, "
                    + "contrary to primitivity.")),
                Paragraph(Text(
                    "Evaluation at s = 3 modulo seven has kernel (delta). "
                    + "If delta^5 divides F, then delta divides a. Writing a = delta c and cancelling delta^4 "
                    + "forces delta to divide c^2 + b^2. The sum of two squares over F_7 vanishes only when both vanish, "
                    + "so delta divides b as well, again contradicting primitivity.")),
                Paragraph(Text(
                    "A prime ideal containing F and G, but containing neither two nor delta, "
                    + "cannot contain either a or b. It must therefore contain a^2 - delta^2 b^2. "
                    + "Adding this expression to a^2 + delta^2 b^2 forces a into the prime ideal, a contradiction. "
                    + "The kernels of evaluation at s = 0 modulo two and s = 3 modulo seven are maximal; "
                    + "hence every prime ideal containing I is exactly (s) or (delta).")),
                Paragraph(Text(
                    "These local calculations are the arithmetic step in the duplication-height argument of Version 13, "
                    + "Proposition generator. The present result is stated in the explicit order. "
                    + "An identification with the full ring of integers, existence of primitive representatives for all projective points, "
                    + "the ideal norm estimate N(I) <= 2^6 7^4 = 392^2, "
                    + "and the all-point height inequalities remain additional obligations. "
                    + "The intended absolute height is the unnormalized number-field projective logarithmic height divided by the field degree two, "
                    + "with the point at infinity assigned height zero. In that normalization the intended inequalities are "
                    + "4 h_x(T) - log(392) <= h_x(2T) <= 4 h_x(T) + log(676). "
                    + "The real inequalities at the two embeddings are supplied separately by the source's ModelDuplication bounds; "
                    + "no numerical height estimate is asserted by this theorem."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula a = F.Id("a"), b = F.Id("b"), q = F.Id("q");
        Formula order = Call("Zsqrtd", D(2));
        Formula idealType = Call("Ideal", order);
        Formula ideal = Call("commonIdeal", a, b);
        Formula s = F.Id("root"), d = F.Id("delta");
        Formula sIdeal = Call("IdealSpan", s), dIdeal = Call("IdealSpan", d);
        Formula first = Seq(Neg, Sp, Open, ideal, Sp, Le, Sp,
            sIdeal, Caret, Grp(D(7)), Close);
        Formula second = Seq(Neg, Sp, Open, ideal, Sp, Le, Sp,
            dIdeal, Caret, Grp(D(5)), Close);
        Formula third = Seq(Forall, Sp, q, Colon, Sp, idealType, Comma, Sp,
            Call("IsPrime", q), Sp, Implies, Sp, ideal, Sp, Le, Sp, q, Sp, Implies, Sp,
            Open, q, Sp, Eq, Sp, sIdeal, Sp, Lor, Sp, q, Sp, Eq, Sp, dIdeal, Close);
        return Disp(Seq(Forall, Sp, a, Comma, Sp, b, Colon, Sp, order, Comma, Sp,
            Call("IdealSpanPair", a, b), Sp, Eq, Sp, Call("UnitIdeal", order), Sp, Implies, Sp,
            first, Sp, Land, RowBreak, Grp(), second, Sp, Land, RowBreak, Grp(), third, Dot));
    }
}
