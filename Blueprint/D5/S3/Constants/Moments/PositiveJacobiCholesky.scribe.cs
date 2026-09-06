using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Constants.Moments;

internal sealed class PositiveJacobiCholeskyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A symmetric Jacobi matrix with positive characteristic roots has positive recursive "
            + "Cholesky weights and the forbidden-neighbour determinant polynomial.",
        H("Positive Jacobi Cholesky Weights"),
        Blocks(Describe.Lean(
            DescribeId.Create("positive-jacobi-cholesky"),
            DeclarationHandle.Create(
                "D5/S3/Constants/Moments/PositiveJacobiCholesky.positive_jacobi_cholesky"),
            H("Positive roots give the recursive positive chain factor"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let d be positive and let K be a real symmetric d by d matrix. Its "
                        + "diagonal entries are alpha(j), its entries immediately below the "
                        + "diagonal are the positive square roots of beta(j+1), and all lower "
                        + "entries farther from the diagonal vanish. Assume beta(j+1) is "
                        + "strictly positive for j+1<d and every real root of the characteristic "
                        + "polynomial of K is strictly positive. Symmetry supplies the upper "
                        + "entries and the spectral theorem then gives positive definiteness.")),
                Paragraph(Text(
                    "The recursion is an actual definition: p(0)=alpha(0) and "
                        + "p(j+1)=alpha(j+1)-beta(j+1)/p(j). The zero-based weight function has "
                        + "w(2j)=p(j) and w(2j+1)=beta(j+1)/p(j). Hence its indices 0 through "
                        + "2d-2 correspond to the usual weights w_1 through w_(2d-1).")),
                Paragraph(Text(
                    "The proof reuses the pinned LDL decomposition, constructs a lower "
                        + "Cholesky factor, and proves by column induction that it is "
                        + "bidiagonal. A second induction identifies every recursively "
                        + "computed pivot with the square of a nonzero diagonal entry. Thus "
                        + "every divisor and every new difference is strictly positive. "
                        + "Column sign normalization identifies the factor with the existing "
                        + "lowerBidiagonal definition built from positive square roots.")),
                Paragraph(Text(
                    "The polynomial determinant identity uses the existing "
                        + "forbidden_neighbour_determinant theorem and the identity "
                        + "det(I+AB)=det(I+BA). It holds as equality of real polynomials, "
                        + "and therefore at every real or complex evaluation.")),
                Paragraph(Text(
                    "This is the matrix construction layer. Root positivity and the "
                        + "symmetric Jacobi presentation are explicit hypotheses. The theorem "
                        + "does not derive them from coefficient Hankel data, change the "
                        + "previous monic basis into an orthonormal basis, or identify a "
                        + "separately supplied coefficient polynomial P with det(I+vK). "
                        + "It gives P=C_w when P denotes that determinant polynomial. The "
                        + "singular Hankel branch and its multiplicity bookkeeping remain "
                        + "outside this declaration."))),
            DescribeRole.Theorem))));

    private static Formula Apply(Formula f, Formula x) => new Formula.Apply(f, [x]);
    private static Formula Entry(Formula m, Formula i, Formula j) =>
        new Formula.Subscript(m, Seq(i, Comma, j));

    private static Formula TheoremFormula()
    {
        Formula d = F.Id("d");
        Formula k = F.Id("K");
        Formula alpha = F.Id("alpha");
        Formula beta = F.Id("beta");
        Formula w = F.Id("w");
        Formula i = F.Id("i");
        Formula j = F.Id("j");
        Formula r = F.Id("r");
        Formula v = F.Id("v");
        Formula reals = Seq(Mathbb, Grp(F.Id("R")));
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula next = Seq(j, Sp, Plus, Sp, D(1));
        Formula twice = Seq(D(2), j);
        Formula even = Seq(twice, Sp, Plus, Sp, D(1));
        Formula nextOdd = Seq(twice, Sp, Plus, Sp, D(2));
        Formula length = Seq(D(2), d, Sp, Minus, Sp, D(1));
        Formula l = Call("lowerBidiagonal", w);
        Formula transpose = Seq(l, Caret, Grp(F.Id("T")));
        Formula quotient = Seq(Frac, Grp(Apply(beta, next)), Grp(Apply(w, twice)));

        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, d, Sp, InMacro, Sp, naturals, Comma, Sp,
                D(0), Sp, Lt, Sp, d, Comma, Sp,
                alpha, Comma, beta, Colon, Sp, naturals, Sp, To, Sp, reals, Comma),
            Seq(k, Colon, Sp, Call("Matrix", Call("Fin", d), Call("Fin", d), reals), Comma),
            Seq(Call("IsHermitian", k), Sp, Land, Sp, Open,
                Forall, Sp, r, Sp, InMacro, Sp, reals, Comma, Sp,
                Call("IsRoot", Call("charpoly", k), r), Sp, Rightarrow, Sp,
                D(0), Sp, Lt, Sp, r, Close, Sp, Land),
            Seq(Open, Forall, Sp, i, Comma, j, Sp, InMacro, Sp, Call("Fin", d), Comma, Sp,
                next, Sp, Lt, Sp, i, Sp, Rightarrow, Sp,
                Entry(k, i, j), Sp, Eq, Sp, D(0), Close, Sp, Land),
            Seq(Open, Forall, Sp, i, Sp, InMacro, Sp, Call("Fin", d), Comma, Sp,
                Entry(k, i, i), Sp, Eq, Sp, Apply(alpha, i), Close, Sp, Land),
            Seq(Open, Forall, Sp, j, Sp, InMacro, Sp, naturals, Comma, Sp,
                next, Sp, Lt, Sp, d, Sp, Rightarrow, Sp,
                Entry(k, next, j), Sp, Eq, Sp, Sqrt, Grp(Apply(beta, next)), Sp, Land, Sp,
                D(0), Sp, Lt, Sp, Apply(beta, next), Close, Sp, Rightarrow),
            Seq(w, Sp, Eq, Sp, Call("jacobiWeights", alpha, beta), Comma, Sp,
                k, Sp, Gt, Sp, D(0), Sp, Land),
            Seq(Open, Forall, Sp, i, Sp, InMacro, Sp, Call("Fin", length), Comma, Sp,
                D(0), Sp, Lt, Sp, Apply(w, i), Close, Sp, Land, Sp,
                Apply(w, D(0)), Sp, Eq, Sp, Apply(alpha, D(0)), Sp, Land),
            Seq(Open, Forall, Sp, j, Sp, InMacro, Sp, naturals, Comma, Sp,
                next, Sp, Lt, Sp, d, Sp, Rightarrow, Sp,
                Apply(w, even), Sp, Eq, Sp, quotient, Sp, Land, Sp,
                Apply(w, nextOdd), Sp, Eq, Sp, Apply(alpha, next), Sp, Minus, Sp,
                Apply(w, even), Close, Sp, Land),
            Seq(k, Sp, Eq, Sp, l, Sp, transpose, Sp, Land),
            Seq(Call("det", Seq(F.Id("I"), Sp, Plus, Sp, v, k)), Sp, Eq, Sp,
                Call("det", Seq(F.Id("I"), Sp, Plus, Sp, v, transpose, Sp, l)), Sp, Eq, Sp,
                Apply(Call("forbiddenPartition", w), v), Dot)
        ]));
    }
}
