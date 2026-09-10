using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ArithSums;

internal sealed class CenteredEuclideanEndpointDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ArithSums/CenteredEuclideanEndpoint.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Increasing coordinates cannot lower the mean-minus-centered-Euclidean-spread endpoint.",
        H("The centered Euclidean lower endpoint"),
        Blocks(
            Paragraph(Text("Let k be a natural number at least two. Coordinates are arbitrary real "
                + "numbers, indexed by Fin(k), and every norm below is the Euclidean norm. "
                + "Write e_i for the vector with coordinate one at i and zero elsewhere. "
                + "Scalar multiplication and vector addition have their usual real meanings.")),
            Entry("E", "euclidean-space", "The Euclidean carrier",
                Disp(Seq(Quant("k"), Equal(Call("E", K), RealVectors))),
                "The carrier is EuclideanSpace over the reals. Its squared norm is the sum "
                + "of coordinate squares, with no averaging factor.", DescribeRole.Definition),
            Entry("ones", "constant-vector", "The constant unit vector",
                Disp(Seq(Quant("k"), Quant("j"), Equal(Sub(One, J), D(1)))),
                "The symbol one denotes the vector whose every coordinate equals one.",
                DescribeRole.Definition),
            Entry("mean", "coordinate-mean", "The coordinate mean",
                Statement(Equal(M(X), Div(Seq(Sum, Underscore, Grp(J), Sp, Sub(X, J)), K)), "x"),
                "The mean is the finite arithmetic average of all k coordinates.", DescribeRole.Definition),
            Entry("center", "centering", "Centering removes the mean",
                Statement(Equal(C(X), MinusOf(X, TimesOf(M(X), One))), "x"),
                "At coordinate j, C(x)_j=x_j-m(x). Thus C is the action of the matrix "
                + "Id-(1/k) one one-transpose. It is linear and sends every constant vector to zero.",
                DescribeRole.Definition),
            Entry("denom", "normalizing-denominator", "The positive normalizing denominator",
                Statement(Equal(Den, Seq(Sqrt, Grp(TimesOf(K, Paren(MinusOf(K, D(1)))))))),
                "The bound k>=2 gives k>0 and k-1>0, hence d>0. All divisions in the "
                + "norm estimates therefore have positive denominators.", DescribeRole.Definition),
            Entry("lower", "lower-endpoint", "Mean minus centered spread",
                Statement(Equal(L(X), MinusOf(M(X), Div(Norm(C(X)), Den))), "x"),
                "The centered sum of squares is not divided by k inside the norm. "
                + "The functional is defined here only with the stated dimension bound.",
                DescribeRole.Definition),
            Entry("mean_add_single", "mean-increment", "The mean increment",
                Statement(Equal(M(Increment), PlusOf(M(X), Div(U, K))), "x", "i", "u"),
                "This algebraic identity holds for every real increment, including negative increments."),
            Entry("center_add_single", "center-increment", "The centered increment",
                Statement(Equal(C(Increment), CenterIncrement), "x", "i", "u"),
                "Linearity of the finite average gives linearity of centering."),
            Entry("norm_center_single_sq_expanded", "basis-square-expanded", "The coordinate square calculation",
                Statement(Equal(Square(Norm(C(Basis))), PlusOf(
                    Square(Paren(MinusOf(D(1), Div(D(1), K)))),
                    Div(MinusOf(K, D(1)), Square(K)))), "i"),
                "The distinguished coordinate is 1-1/k; each of the other k-1 coordinates is -1/k."),
            Entry("norm_center_single_sq", "basis-square", "The centered basis norm",
                Statement(Equal(Square(Norm(C(Basis))), Div(MinusOf(K, D(1)), K)), "i"),
                "Normalizing the expanded square sum gives a positive value, so C(e_i) is nonzero."),
            Entry("norm_center_single_div", "basis-ratio", "The exact normalized basis length",
                Statement(Equal(Div(Norm(C(Basis)), Den), Div(D(1), K)), "i"),
                "Both sides have the required nonnegative signs. The square identity and d>0 "
                + "give the exact ratio; no sign is lost by squaring."),
            Entry("center_eq_zero_iff_constant", "centering-kernel", "The kernel consists of constant vectors",
                Statement(Equivalent(Equal(C(X), D(0)), Seq(ExistsReal("a"),
                    Equal(X, TimesOf(A, One)))), "x"),
                "If centering vanishes, x=m(x) one. Conversely, a constant vector has its "
                + "constant coordinate as mean and has zero centered norm."),
            Entry("lower_add_single_sub", "endpoint-increment", "The exact endpoint increment",
                Statement(Equal(MinusOf(L(Increment), L(X)), MinusOf(Div(U, K),
                    Div(MinusOf(Norm(CenterIncrement), Norm(C(X))), Den))), "x", "i", "u"),
                "This identity isolates the change in Euclidean norm and holds for every real u."),
            Entry("lower_le_add_single", "coordinate-monotonicity", "A nonnegative coordinate increment cannot lower the endpoint",
                Statement(ImpliesTo(Nonnegative(U), Seq(L(X), Sp, Le, Sp, L(Increment))), "x", "i", "u"),
                "The triangle inequality bounds the norm increment by the norm of u C(e_i). "
                + "For u>=0 this is u times the basis norm, whose ratio to d is 1/k. "
                + "The mean increment therefore compensates for the entire possible norm increase."),
            Entry("lower_add_zero_single", "zero-increment", "Zero increment gives equality for every vector",
                Statement(Equal(L(PlusOf(X, TimesOf(D(0), Basis))), L(X)), "x", "i"),
                "There is no ray condition when u=0."),
            Entry("lower_add_single_eq_iff_centered", "centered-equality", "Positive-increment equality is a nonnegative centered ray",
                Statement(ImpliesTo(Positive(U), Equivalent(Equal(L(Increment), L(X)), CenteredRay)),
                    "x", "i", "u"),
                "For u>0, the vector w=u C(e_i) is nonzero. Equality in the endpoint estimate "
                + "is exactly equality in the triangle inequality for v=C(x) and w. In a real "
                + "inner product space this is equivalent to v being a nonnegative multiple of w. "
                + "The vector v may be zero, and the ray coefficient may be zero."),
            Entry("centered_ray_iff_translated_single", "translated-ray", "Lifting the centered ray to a free translation",
                Statement(Equivalent(CenteredRay, TranslatedRay), "x", "i"),
                "Subtracting t e_i gives a vector in the centering kernel. Thus the same "
                + "nonnegative coefficient t is retained, and x=a one+t e_i with "
                + "a=m(x)-t/k. Conversely, the mean of that translated vector is a+t/k, "
                + "so its centered part is t C(e_i). The offset a is any real number."),
            Entry("lower_add_single_eq_iff_translated", "translated-equality", "The exact translated equality condition",
                Statement(ImpliesTo(Positive(U), Equivalent(Equal(L(Increment), L(X)), TranslatedRay)),
                    "x", "i", "u"),
                "Combining the centered equality criterion with the kernel characterization "
                + "gives this equivalence. Taking t=0 includes every constant vector, "
                + "including constants with negative coordinates."),
            Entry("lower_le_of_pointwise_le", "global-monotonicity", "Coordinate order implies endpoint order",
                Statement(ImpliesTo(Paren(Seq(Quant("j"), Sub(X, J), Sp, Le, Sp, Sub(Y, J))),
                    Seq(L(X), Sp, Le, Sp, L(Y))), "x", "y"),
                "Insert the nonnegative coordinate increments y_j-x_j one at a time. "
                + "The insertion criterion for finite-set monotonicity orders the partial sums, and the sum "
                + "over all coordinates reconstructs y. This can supply lower bounds on "
                + "arithmetic boxes without imposing arithmetic restrictions on this theorem."),
            Paragraph(Text("The geometric ingredients are the real inner-product Cauchy-Schwarz "
                + "bound, the squared norm expansion, the triangle inequality and its equality "
                + "criterion. The equality criterion requires only the second vector to be "
                + "nonzero; it does not exclude zero variance in x. No strict coordinate "
                + "monotonicity is asserted.")))));

    private static DocumentBlock Entry(string name, string id, string title, Formula formula,
        string explanation, DescribeRole role = DescribeRole.Theorem) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(explanation))), role);

    private static Formula K => F.Id("k");
    private static Formula X => F.Id("x");
    private static Formula Y => F.Id("y");
    private static Formula J => F.Id("j");
    private static Formula U => F.Id("u");
    private static Formula A => F.Id("a");
    private static Formula T => F.Id("t");
    private static Formula Den => F.Id("d");
    private static Formula One => Seq(Mathbf, Grp(D(1)));
    private static Formula Reals => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula RealVectors => Seq(Reals, Caret, Grp(K));
    private static Formula Basis => Sub(F.Id("e"), F.Id("i"));
    private static Formula Increment => PlusOf(X, TimesOf(U, Basis));
    private static Formula CenterIncrement => PlusOf(C(X), TimesOf(U, C(Basis)));
    private static Formula CenteredRay => Seq(ExistsReal("t"), Nonnegative(T), Sp, Land, Sp,
        Equal(C(X), TimesOf(T, C(Basis))));
    private static Formula TranslatedRay => Seq(ExistsReal("a"), ExistsReal("t"),
        Nonnegative(T), Sp, Land, Sp, Equal(X, PlusOf(TimesOf(A, One), TimesOf(T, Basis))));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula M(Formula value) => Call("m", value);
    private static Formula C(Formula value) => Call("C", value);
    private static Formula L(Formula value) => new Formula.Apply(Ell, [value]);
    private static Formula Sub(Formula value, Formula index) => Seq(value, Underscore, Grp(index));
    private static Formula Square(Formula value) => Seq(value, Caret, Grp(D(2)));
    private static Formula Norm(Formula value) => Seq(Vert, Sp, value, Sp, Vert);
    private static Formula Div(Formula numerator, Formula denominator) => Seq(Frac, Grp(numerator), Grp(denominator));
    private static Formula PlusOf(Formula left, Formula right) => Seq(left, Sp, Plus, Sp, right);
    private static Formula MinusOf(Formula left, Formula right) => Seq(left, Sp, Minus, Sp, right);
    private static Formula TimesOf(Formula left, Formula right) => Seq(left, Sp, Cdot, Sp, right);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Paren(Formula value) => Seq(Open, value, Close);
    private static Formula Equivalent(Formula left, Formula right) => Seq(Paren(left), Sp, Iff, Sp, Paren(right));
    private static Formula ImpliesTo(Formula left, Formula right) => Seq(left, Sp, Implies, Sp, Paren(right));
    private static Formula Nonnegative(Formula value) => Seq(D(0), Sp, Le, Sp, value);
    private static Formula Positive(Formula value) => Seq(D(0), Sp, Lt, Sp, value);
    private static Formula Domain(string name) => name switch
    {
        "k" => Seq(Mathbb, Grp(F.Id("N"))),
        "x" or "y" => RealVectors,
        "i" or "j" => Call("Fin", K),
        _ => Reals
    };
    private static Formula Quant(string name) => Seq(Forall, Sp, F.Id(name), Sp,
        InMacro, Sp, Domain(name), Comma, Sp);
    private static Formula ExistsReal(string name) => Seq(Exists, Sp, F.Id(name), Sp,
        InMacro, Sp, Reals, Comma, Sp);
    private static Formula Statement(Formula body, params string[] variables) => Disp(Seq(
        Quant("k"), D(2), Sp, Le, Sp, K, Sp, Implies, Sp,
        Seq(variables.Select(Quant).Append(body).ToArray())));
}
