using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Measurement;

internal sealed class OrthocrossInverseFrameDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Measurement/OrthocrossInverseFrame.";
    private static Formula Q => F.Id("q");
    private static Formula L => F.Id("L");
    private static Formula A => F.Id("a");
    private static Formula B => F.Id("b");
    private static Formula Delta => F.Delta;
    private static Formula U => F.Id("u");
    private static Formula T => F.Id("t");
    private static Formula Dim => F.Id("d");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The standard orthocross frame has diagonal d, upper entry a = (1-i)/2 "
            + "and lower entry b = (1+i)/2. A geometric ratio and a nonzero denominator "
            + "specify its proposed inverse entries.",
        H("Geometric parameters for the orthocross inverse"),
        Blocks(
            Def("upperEntry", "Upper frame entry", A, Fraction(Seq(D(1), Minus, F.Id("i")), D(2))),
            Def("lowerEntry", "Lower frame entry", B, Fraction(Seq(D(1), Plus, F.Id("i")), D(2))),
            Def("scale", "Complex scale", L, Seq(Dim, Minus, A), true),
            Def("ratio", "Geometric ratio", Q, Fraction(Seq(Dim, Minus, B), L), true),
            Def("denominator", "Geometric denominator", Delta,
                Seq(B, Minus, A, Pow(Q, Dim)), true),
            Def("upperConstant", "Upper inverse coefficient", U,
                Fraction(Seq(Minus, F.Id("i"), A, Pow(Q, Seq(Dim, Minus, D(2)))),
                    Seq(Pow(L, D(2)), Delta)), true),
            Def("diagonalConstant", "Diagonal inverse coefficient", T,
                Seq(Fraction(D(1), L), Minus,
                    Fraction(Seq(F.Id("i"), A, Pow(Q, Seq(Dim, Minus, D(1)))),
                        Seq(Pow(L, D(2)), Delta))), true),
            Describe.Lean(DescribeId.Create("orthocross-inverse-candidate"),
                DeclarationHandle.Create(Prefix + "candidate"), H("Hermitian triangular candidate"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, Dim, Comma, Sp,
                    Forall, Sp, F.Id("j"), Comma, Sp, F.Id("k"), Comma, Sp,
                    Open, F.Id("j"), Sp, Eq, Sp, F.Id("k"), Sp, Rightarrow, Sp,
                    Sub("M", Seq(F.Id("j"), F.Id("k"))), Sp, Eq, Sp, T, Close, Sp, Land, Sp,
                    Open, F.Id("j"), Sp, Lt, Sp, F.Id("k"), Sp, Rightarrow, Sp,
                    Sub("M", Seq(F.Id("j"), F.Id("k"))), Sp, Eq, Sp,
                    U, Pow(Q, Seq(F.Id("j"), Minus, F.Id("k"), Plus, D(1))), Close, Sp, Land, Sp,
                    Open, F.Id("k"), Sp, Lt, Sp, F.Id("j"), Sp, Rightarrow, Sp,
                    Sub("M", Seq(F.Id("j"), F.Id("k"))), Sp, Eq, Sp,
                    Pow(Seq(Open, U, Pow(Q, Seq(F.Id("k"), Minus, F.Id("j"), Plus, D(1))), Close), Star), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For indices j,k in Fin d, the candidate has diagonal t, "
                    + "entry u q^(j-k+1) above the diagonal, and the conjugate of the corresponding "
                    + "upper entry below the diagonal. Integer exponents are used."))), DescribeRole.Definition),
            Thm("ratio_ne_zero", "The ratio is nonzero",
                Seq(Q, Sp, Neq, Sp, D(0)),
                "The scale has imaginary part one half, so it and its conjugate are nonzero."),
            Thm("ratio_ne_one", "The ratio is distinct from one",
                Seq(Q, Sp, Neq, Sp, D(1)),
                "The difference q-1 equals -i divided by the nonzero scale."),
            Thm("norm_ratio", "Unit modulus", Seq(Norm(Q), Sp, Eq, Sp, D(1)),
                "The numerator is the conjugate of L. Its norm equals the nonzero norm of L."),
            Thm("star_ratio", "Conjugation inverts the ratio",
                Seq(Pow(Q, Star), Sp, Eq, Sp, Pow(Q, Seq(Minus, D(1)))),
                "Conjugating the quotient interchanges its numerator and denominator."),
            Thm("denominator_ne_zero", "Nonzero denominator",
                Seq(Dim, Sp, Gt, Sp, D(0), Sp, Rightarrow, Sp, Delta, Sp, Neq, Sp, D(0)),
                "A zero denominator would imply q^d = i. For d at least two, the telescoping "
                    + "bound |q^d-1| <= d |q-1|, together with |L|^2 = d^2-d+1/2, "
                    + "contradicts |i-1|^2 = 2. Dimension one is evaluated exactly."),
            Thm("upperConstant_ne_zero", "Nonzero upper coefficient",
                Seq(Dim, Sp, Gt, Sp, D(0), Sp, Rightarrow, Sp, U, Sp, Neq, Sp, D(0)),
                "All factors in the numerator and denominator of u are nonzero in positive dimension."),
            Thm("frame_mul_candidate", "The candidate inverts the frame",
                Seq(Dim, Sp, Gt, Sp, D(0), Sp, Rightarrow, Sp,
                    F.Omega, Sp, F.Id("M"), Sp, Eq, Sp, F.Id("I")),
                "Scale the candidate by L^2 delta. The geometric column sum is "
                    + "i L q^(d-k-1), which gives the first product row. Subtracting adjacent "
                    + "frame rows leaves only two entries, and the geometric recurrence gives "
                    + "the difference of the corresponding identity rows. Induction gives every row."),
            Thm("inverse_frame_eq", "Closed inverse form",
                Seq(Dim, Sp, Gt, Sp, D(0), Sp, Rightarrow, Sp,
                    Pow(F.Omega, Seq(Minus, D(1))), Sp, Eq, Sp, F.Id("M")),
                "A right inverse of a square matrix equals its nonsingular inverse. "
                    + "Hermiticity identifies the lower entries with the conjugates of the upper entries."),
            Thm("diagonalConstant_pos", "Positive real diagonal",
                Seq(Dim, Sp, Gt, Sp, D(0), Sp, Rightarrow, Sp, D(0), Sp, Lt, Sp, T),
                "The standard frame is positive definite, and so is its inverse. "
                    + "Every diagonal entry of the inverse is therefore a strictly positive real number."),
            Thm("upperConstant_phase", "Conjugate coefficient phase",
                Seq(Pow(U, Star), Sp, Eq, Sp, U, F.Id("i"), Pow(Q, Seq(D(2), Minus, Dim))),
                "Conjugating delta gives -delta q^(-d), while conjugating L gives qL. "
                    + "The factors in the conjugate of u therefore cancel to a/(L^2 delta)."),
            Thm("diagonal_div_upperConstant", "A short quotient for the diagonal ratio",
                Seq(Dim, Sp, Gt, Sp, D(0), Sp, Rightarrow, Sp,
                    Fraction(T, U), Sp, Eq, Sp,
                    Fraction(Seq(Q, Minus, F.Id("i"), Pow(Q, Seq(D(2), Minus, Dim))), Seq(D(1), Minus, Q))),
                "The identities t = 1/L + qu and qt - conjugate(u) = 1/L give "
                    + "t(1-q) = qu - conjugate(u). Substituting the coefficient phase yields the quotient."),
            Thm("polynomial_at_ratio_ne_zero", "Small Gaussian polynomials do not vanish",
                Seq(Forall, Sp, F.Id("p"), Comma, Sp,
                    F.Id("p"), Sp, Neq, Sp, D(0), Sp, Land, Sp,
                    Open, Forall, Sp, F.Id("n"), Comma, Sp,
                    Pow(Norm(Sub("p", F.Id("n"))), D(2)), Sp, Lt, Sp,
                    D(2), Pow(Dim, D(2)), Minus, D(2), Dim, Plus, D(1), Close, Sp, Rightarrow, Sp,
                    F.Id("p"), Open, Q, Close, Sp, Neq, Sp, D(0)),
                "The polynomial p has Gaussian-integer coefficients. Their Gaussian norm is "
                    + "the squared complex modulus. Write q=A/B with A=(d-1)-di and B=d-(d-1)i. "
                    + "An explicit Bezout identity makes A and B coprime. Scaling polynomial roots "
                    + "by B shows that a root at q would force B to divide the nonzero leading "
                    + "coefficient. Its norm would then be at least norm(B)=2d^2-2d+1, a contradiction.")), []));

    private static DocumentBlock Def(string declaration, string title, Formula lhs, Formula rhs,
        bool dimension = false) => Describe.Lean(
        DescribeId.Create("orthocross-inverse-" + declaration.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + declaration),
        H(title), StatementSource.FromAuthor(Disp(dimension
            ? Seq(Forall, Sp, Dim, Comma, Sp, lhs, Sp, Eq, Sp, rhs)
            : Seq(lhs, Sp, Eq, Sp, rhs))), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text("The " + title.ToLowerInvariant() + " is defined by this equality."))),
        DescribeRole.Definition);

    private static DocumentBlock Thm(string declaration, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create("orthocross-inverse-" + declaration.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(Seq(Forall, Sp, Dim, Comma, Sp, formula))),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static Formula Pow(Formula value, Formula exponent) => Seq(value, Caret, Grp(exponent));
    private static Formula Fraction(Formula numerator, Formula denominator) =>
        new Formula.Fraction(numerator, denominator);
    private static Formula Norm(Formula value) => Seq(Vert, Sp, value, Vert);
    private static Formula Sub(string name, Formula index) => Seq(F.Id(name), Underscore, Grp(index));
}
