using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.Blueprint.D5.S3.Zeros.ActualZeroGeometryDocument;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.TestFunctions;

internal sealed class LiCurvatureFiniteReconstructionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Weil/TestFunctions/LiCurvatureFiniteReconstruction.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Normalized Hermitian second differences reconstruct finite Toeplitz quadratic forms, "
            + "with a smallest-eigenvalue obstruction and a two-point absolute growth bound.",
        H("Finite Li Curvature Reconstruction"), Blocks(
            Paragraph(Text("Throughout, T(c,n) has row and column indices in Fin(n), "
                + "and e(n) is the complex all-ones vector on the same type. "
                + "Both indices are cast to integers before subtraction.")),
            new DocumentBlock.DisplayFormula(Equal(Call("T", Id("c"), Id("n"), Id("j"), Id("k")),
                Call("c", Subtract(Call("Int", Id("j")), Call("Int", Id("k")))))),
            new DocumentBlock.DisplayFormula(Equal(Call("e", Id("n"), Id("j")), Num(1))),
            Paragraph(Text("Ico(1,n) is the natural interval from one inclusive to n exclusive. "
                + "Real and Int in the formulas denote casts; NatSub is truncated natural subtraction. "
                + "For positive n, last(n) is the element of Fin(card(Fin(n))) with value n minus one. "
                + "The eigenvaluesZero enumeration is Mathlib's descending eigenvalues enumeration.")),
            Result("recurrence_eq_weighted_curvature_sum", "Weighted curvature reconstruction",
                Common(All("n", Natural, Equal(U(N), Multiply(Id("L"), Weighted(N))))),
                "The repository's second_difference_recurrence_unique is applied to the displayed "
                    + "candidate sequence. Mathlib's finite interval extension identities verify "
                    + "its initial values and second differences. This is the finite algebraic "
                    + "reconstruction, including zero and one and without division by L."),
            Result("toeplitz_ones_diagonal_count", "Signed finite diagonal count",
                All("c", Function(new Formula.Integers(), Complex), All("n", Natural,
                    Equal(Quadratic(N), Add(Multiply(Call("Complex", N), Call("c", Num(0))),
                        Sum(N, Multiply(Subtract(Call("Complex", N), Call("Complex", K)),
                            Add(C(K), Call("c", Subtract(Num(0), Call("Int", K)))))))))),
                "Mathlib's interval Fubini and reflection identities split the square into "
                    + "its diagonal and two strict triangles. Each signed gap has n minus k "
                    + "entries. The identity requires neither Hermitian symmetry nor normalization, "
                    + "and retains both complex coefficients before taking real parts."),
            Result("recurrence_eq_toeplitz_ones_quadratic", "The actual size-n quadratic form",
                Common(All("n", Natural, Imp(Le(Num(1), N),
                    Equal(U(N), Multiply(Id("L"), Call("re", Quadratic(N))))))),
                "Weighted reconstruction and the signed count give this sequence-to-matrix "
                    + "identity. Conjugation and c(0)=1 give its real part. The existing "
                    + "toeplitzMatrix(c,n-1) is transported through the value-preserving "
                    + "equivalence Fin(n-1+1) to Fin(n); the submatrix and dot-product "
                    + "equivalence theorems also transport the all-ones vector. No measure "
                    + "representation is a premise."),
            Result("recurrence_nonneg_of_toeplitz_posSemidef", "Full Toeplitz positivity",
                Common(Imp(All("N", Natural, Call("PosSemidef", Toeplitz(Id("N")))),
                    All("n", Natural, Le(Num(0), U(N))))),
                "The preceding quadratic identity and Mathlib's PosSemidef.re_dotProduct_nonneg "
                    + "give the nonnegative coefficient for every positive size. The prescribed "
                    + "initial value supplies size zero."),
            Result("negative_recurrence_bounds_smallest_eigenvalue", "A negative spectral obstruction",
                Common(All("n", Natural, Imp(Le(Num(1), N), Imp(Lt(Num(0), Id("L")),
                    Imp(Lt(U(N), Num(0)), Exists("hT", Call("IsHermitian", Matrix(N)),
                        And(Le(Call("eigenvaluesZero", Id("hT"), Call("last", N)), Quotient),
                            Lt(Quotient, Num(0))))))))),
                "The classical finite-dimensional Rayleigh infimum theorem is supplied by "
                    + "Mathlib's hasEigenvalue_iInf_of_finiteDimensional. The public eigenvalue "
                    + "enumeration and its antitonicity put the last eigenvalue below that "
                    + "infimum. Evaluation uses WithLp.toLp(2,e(n)), whose squared Euclidean "
                    + "norm is n and which is nonzero. Conjugate symmetry identifies the real "
                    + "numerator with the preceding quadratic identity. Strict positivity of "
                    + "n times L gives the second inequality."),
            Result("two_point_posSemidef_abs_recurrence_bound", "Two-point absolute bound",
                Common(Imp(Pairs, All("n", Natural,
                    And(Le(Abs(U(N)), Multiply(Id("L"), Total(N))),
                        Equal(Multiply(Id("L"), Total(N)),
                            Multiply(Id("L"), Pow(Call("Real", N), Num(2)))))))),
                "Only injective two-point principal compressions are assumed positive. "
                    + "Selecting indices zero and k in the block of size k+1 gives determinant "
                    + "one minus the squared complex norm of c(k). Mathlib's determinant "
                    + "nonnegativity and two-by-two determinant formula bound that norm by one. "
                    + "The repository's quadratic_of_bounded_second_difference then supplies "
                    + "the absolute growth bound. Mathlib's finite Gauss identity evaluates "
                    + "the displayed sum, also at zero and one. Full-matrix positivity is "
                    + "not needed for this bound."))));

    private static DocumentBlock Result(string name, string title, Formula statement, string derivation) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.FromAuthor(statement), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(derivation))), DescribeRole.Theorem);

    private static Formula N => Id("n");
    private static Formula K => Id("k");
    private static Formula U(Formula n) => Call("u", n);
    private static Formula C(Formula n) => Call("c", Call("Int", n));
    private static Formula Matrix(Formula n) => Call("T", Id("c"), n);
    private static Formula Toeplitz(Formula n) => Call("toeplitzMatrix", Id("c"), n);
    private static Formula Quadratic(Formula n) => Call("dotProduct", Call("star", Call("e", n)),
        Call("mulVec", Matrix(n), Call("e", n)));
    private static Formula Quotient => Div(U(N), Multiply(Call("Real", N), Id("L")));
    private static Formula Sum(Formula n, Formula body) => F.Seq(F.Sum, F.Underscore,
        F.Grp(F.Id("k"), F.InMacro, F.Sp, Call("Ico", Num(1), n)), F.Sp, F.Grp(body));
    private static Formula Total(Formula n) => Add(Call("Real", n), Multiply(Num(2),
        Sum(n, Subtract(Call("Real", n), Call("Real", K)))));
    private static Formula Weighted(Formula n) => Add(Call("Real", n), Multiply(Num(2),
        Sum(n, Multiply(Subtract(Call("Real", n), Call("Real", K)), Call("re", C(K))))));
    private static Formula Pairs => All("N", Natural,
        All("p", Function(Call("Fin", Num(2)), Call("Fin", Add(Id("N"), Num(1)))),
            Imp(Call("Injective", Id("p")),
                Call("PosSemidef", Call("submatrix", Toeplitz(Id("N")), Id("p"), Id("p"))))));
    private static Formula Common(Formula body) =>
        All("u", Function(Natural, Real), All("L", Real,
            All("c", Function(new Formula.Integers(), Complex),
                Imp(Equal(U(Num(0)), Num(0)), Imp(Equal(U(Num(1)), Id("L")),
                    Imp(Le(Num(0), Id("L")), Imp(Equal(Call("c", Num(0)), Num(1)),
                        Imp(All("k", new Formula.Integers(),
                            Equal(Call("c", Subtract(Num(0), K)), Call("star", Call("c", K)))),
                            Imp(All("n", Natural, Imp(Le(Num(1), N),
                                Equal(Add(Subtract(U(Add(N, Num(1))), Multiply(Num(2), U(N))),
                                    U(Call("NatSub", N, Num(1)))),
                                    Multiply(Multiply(Num(2), Id("L")), Call("re", C(N)))))),
                                body)))))))));
}
