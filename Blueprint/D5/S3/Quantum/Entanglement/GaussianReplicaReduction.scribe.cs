using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement;

internal sealed class GaussianReplicaReductionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/GaussianReplicaReduction.";
    private static Formula Identity => Seq(F.Id("I"), Underscore, F.Id("R"));
    private static Formula Transpose(Formula q) => Seq(q, Caret, Grp(F.Id("T")));
    private static Formula Square(Formula x) => Seq(x, Caret, D(2));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula Det(Formula x) => Seq(Operatorname, Grp(F.Id("det")), Open, x, Close);
    private static Formula Reals => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula MatrixType(Formula row, Formula col) =>
        Seq(Reals, Caret, Grp(row, Times, Sp, col));
    private static Formula All(Formula v, Formula domain, Formula body) =>
        Seq(Forall, Sp, v, Sp, InMacro, Sp, domain, Comma, Sp, body);
    private static Formula ScalarParameters(Formula body) =>
        All(F.Id("R"), Seq(Operatorname, Grp(F.Id("FiniteTypes"))),
            All(F.Id("Q"), MatrixType(F.Id("R"), F.Id("R")),
                All(F.Id("a"), Reals, All(F.Id("b"), Reals, body))));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The determinant of a mean of two finite-rank orthogonal projections depends on the overlap of their orthonormal column families.",
        H("Replica determinant reduction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("gaussian-quadratic-integral"),
                DeclarationHandle.Create(Prefix + "integral_exp_neg_quadraticForm_pi"),
                H("Determinant normalization"),
                StatementSource.FromAuthor(Disp(Seq(
                    Int, Underscore, Grp(Mathbb, Grp(F.Id("R")), Caret, F.Id("n")), Sp,
                    Operatorname, Grp(F.Id("exp")), Open, Minus, F.Id("x"), Caret, F.Id("T"),
                    F.Id("M"), F.Id("x"), Close, Sp, F.Id("dx"), Eq,
                    Seq(Frac, Grp(Pi, Caret, Grp(Frac, Grp(F.Id("n")), Grp(D(2)))),
                        Grp(Sqrt, Grp(Operatorname, Grp(F.Id("det")), Open, F.Id("M"), Close)))))),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Analytic/brcic2026gaussianquadratic")),
                Blocks(Paragraph(Text(
                    "For every natural dimension n and positive-definite real n by n matrix M, "
                    + "the Lebesgue integral of exp(-x^T M x) over the plain coordinate space "
                    + "is pi^(n/2) divided by the square root of det M. Factor M as B^T B "
                    + "using its positive matrix square root. The linear substitution y = B x "
                    + "has Jacobian det B = sqrt(det M) and reduces the integral to the "
                    + "isotropic Euclidean Gaussian. The coordinate and Euclidean measures "
                    + "agree under the measure-preserving equivalence between their carriers."))),
                DescribeRole.Theorem),
            Node("block", "A scalar Schur complement", "scalar_block_determinant",
                Disp(ScalarParameters(Seq(F.Id("a"), Neq, Sp, D(0), Implies, Sp,
                    Det(Call("fromBlocks", Seq(F.Id("a"), Identity),
                        Seq(Minus, F.Id("b"), F.Id("Q")),
                        Seq(Minus, F.Id("b"), Transpose(F.Id("Q"))),
                        Seq(F.Id("a"), Identity))), Eq,
                    Det(Seq(Square(F.Id("a")), Identity, Minus,
                        Square(F.Id("b")), Transpose(F.Id("Q")), F.Id("Q")))))),
                "For every finite index type R, every real matrix Q on R, and real a and b with a nonzero, the displayed block determinant equals det(a^2 I_R - b^2 Q^T Q). Factor a from the first block row, then apply the Schur complement with identity in the upper left block. Absorbing a into the remaining determinant cancels the denominator.",
                DescribeRole.Theorem),
            Node("columns", "Two orthonormal column families", "paired_projection_determinant",
                Disp(All(F.Id("J"), Seq(Operatorname, Grp(F.Id("FiniteTypes"))),
                    All(F.Id("R"), Seq(Operatorname, Grp(F.Id("FiniteTypes"))),
                        All(F.Id("U"), MatrixType(F.Id("J"), F.Id("R")),
                            All(F.Id("V"), MatrixType(F.Id("J"), F.Id("R")),
                                All(F.Id("b"), Reals, Seq(
                                    Transpose(F.Id("U")), F.Id("U"), Eq, Identity, Comma, Quad, Sp,
                                    Transpose(F.Id("V")), F.Id("V"), Eq, Identity, Comma, Quad,
                                    D(1), Minus, F.Id("b"), Neq, Sp, D(0), Implies, Sp,
                                    Det(Seq(F.Id("I"), Underscore, F.Id("J"), Minus,
                                        F.Id("b"), Open, F.Id("U"), Transpose(F.Id("U")), Plus,
                                        F.Id("V"), Transpose(F.Id("V")), Close)), Eq,
                                    Det(Seq(Square(Seq(Open, D(1), Minus, F.Id("b"), Close)), Identity,
                                        Minus, Square(F.Id("b")),
                                        Transpose(Seq(Open, Transpose(F.Id("U")), F.Id("V"), Close)),
                                        Open, Transpose(F.Id("U")), F.Id("V"), Close))))))))),
                "Let J and R be finite index types, and let U and V be real J by R matrices satisfying U^T U = V^T V = I_R. For any real b with 1-b nonzero, Sylvester's identity changes the determinant on J into the determinant of the Gram matrix of the concatenated columns. Its diagonal blocks are I_R and its off-diagonal blocks are U^T V and V^T U. The scalar Schur complement yields the displayed determinant on R.",
                DescribeRole.Theorem),
            Node("binary", "The binary determinant identity", "binary_replica_determinant_identity",
                BinaryFormula(),
                "For all real x, y, z, a, b with x+y+z=1, let A have rows (z,x+y) and (x+y,z), B have rows (x,y+z) and (y+z,x), and C have rows (y,z+x) and (z+x,y). Let Q have rows (z,y,x,0), (y,z,0,x), (x,0,z,y), and (0,x,y,z). Define D(a,b,M) = det(a I - b M^T M). Then D(a,b,A) D(a,b,B) D(a,b,C) = (a-b)^2 D(a,b,Q). Expanding the determinants verifies this polynomial identity without any positivity assumption.",
                DescribeRole.Theorem),
            Node("sqrt-limit", "Square roots at large arguments", "sqrt_quadratic_ratio_limit",
                Disp(All(F.Id("b"), Reals, All(F.Id("c"), Reals,
                    Seq(D(0), Leq, Sp, F.Id("b"), Comma, Quad, D(0), Leq, Sp, F.Id("b"), Plus,
                        F.Id("c"), Implies, Sp,
                        Call("lim", Call("div", Call("sqrt", Seq(F.Id("b"), F.Id("a"),
                            Caret, D(2), Plus, F.Id("c"))), F.Id("a"))), Eq,
                        Call("sqrt", F.Id("b")))))),
                "For all real b and c with b nonnegative and b+c nonnegative, sqrt(b a^2+c)/a tends to sqrt(b) as a tends to positive infinity. For a at least one the radicand is nonnegative. Dividing inside the square root gives sqrt(b+c/a^2), and continuity gives the limit.",
                DescribeRole.Theorem),
            Node("scaled-parameter", "The small symmetric parameter", "symmetric_parameter_scaled_limit",
                Disp(All(F.Id("N"), Reals, Seq(D(2), Lt, F.Id("N"), Implies, Sp,
                    Call("lim", Seq(F.Id("a"), Caret, D(2), Varepsilon, Open, F.Id("a"), Close)),
                    Eq, Seq(Frac, Grp(F.Id("N"), Minus, D(1)), Grp(Square(F.Id("N"))))))),
                "For every real N greater than two, let e(a) = ((a^2-1)(N-2)-sqrt(a^2-1) sqrt((a^2-1)N^2+4(N-1)))/(2a(N-1)) and epsilon(a) = (a+(N-1)e(a))/(a-e(a)). Then a^2 epsilon(a) tends to (N-1)/N^2 as a tends to positive infinity. Set s=sqrt(a^2-1) and t=sqrt((a^2-1)N^2+4(N-1)). The identity (a+(N-1)e(a))a(sN+t)=t-(N-2)s removes cancellation in the numerator. The limits s/a=1, t/a=N and (a-e(a))/a=N/(N-1) give the result.",
                DescribeRole.Theorem),
            Node("log-parameter", "The logarithm of a quadratically small parameter", "log_equivalent_of_scaled_limit",
                Disp(All(Varepsilon, Seq(Reals, To, Reals), All(F.Id("C"), Reals,
                    Seq(D(0), Lt, F.Id("C"), Comma, Quad,
                        Call("lim", Seq(F.Id("a"), Caret, D(2), Varepsilon, Open, F.Id("a"), Close)),
                        Eq, F.Id("C"), Implies, Sp,
                        Call("IsEquivalent", Call("atTop"), Call("log", Varepsilon),
                            Seq(Minus, D(2), Call("log"))))))),
                "For any real-valued function epsilon and any positive real C, if a^2 epsilon(a) tends to C at positive infinity, then log(epsilon(a)) is asymptotically equivalent to -2 log(a). The difference is eventually log(a^2 epsilon(a)), which tends to log(C). Every function with a finite limit is negligible compared with log(a).",
                DescribeRole.Theorem),
            Node("stochastic-kernel", "The maximum principle for replica twists", "stochastic_twist_kernel",
                StochasticKernelFormula(),
                "Let R be a nonempty finite type, K any type, g a family of permutations of R, and M a real row-stochastic matrix on R. Assume M(r,g_k(r)) is positive for every k and r, and that every ordered pair of replicas is connected by a finite sequence of twists. Then Mx=x if and only if x is constant. Choose a coordinate where x attains its maximum. The weighted sum of the nonnegative differences from this maximum vanishes, so each positive transition also attains the maximum. Propagation along the twist paths makes every coordinate equal.",
                DescribeRole.Theorem),
            Node("average-kernel", "The kernel of a permutation average", "permutation_average_kernel",
                PermutationKernelFormula(),
                "Let R be a nonempty finite replica type and K a finite type indexing permutations g_k, with an index k_0 for the identity permutation. Assume their directed paths connect every ordered pair in R. Define Q(r,s) as the number of indices k with r=g_k(s), divided by the cardinality of K. Its row and column sums equal one. Thus Q^T Q is row-stochastic. Its entry at (r,g_k(r)) is positive: the summand at g_k(r) contains the k transition and the identity transition. The maximum principle shows that Q^T Q fixes exactly the constant real vectors.",
                DescribeRole.Theorem),
            Node("stochastic-factor", "A simple determinant factor", "stochastic_determinant_factor",
                DeterminantFactorFormula(false),
                "For every real Hermitian row-stochastic matrix G on a nonempty finite type, assume its fixed vectors are exactly the constants. Then there is a continuous real function D with D(0)>0 such that det(((1+e)/2)^2 I-((1-e)/2)^2 G)=e D(e) for every real e. Gershgorin's theorem bounds every eigenvalue by one. The constant vector gives an eigenvalue one, and linear independence of the eigenbasis makes this eigenvalue simple. The remaining eigenvalues are strictly below one. The spectral theorem gives D as the product of the remaining factors, each positive at zero.",
                DescribeRole.Theorem),
            Node("average-factor", "The residual replica determinant", "permutation_average_determinant_factor",
                DeterminantFactorFormula(true),
                "For every finite nonempty replica type and every finite family of permutations containing the identity and connecting every ordered pair by twist paths, let Q be their uniform permutation average. There exists a continuous D with D(0)>0 such that det(((1+e)/2)^2 I-((1-e)/2)^2 Q^T Q)=e D(e) for every real e. The Gram matrix is Hermitian and its fixed vectors are the constants, so its determinant has the simple factor just established.",
                DescribeRole.Theorem),
            Node("cycle-paths", "Paths on a replica cycle", "cyclic_twists_transitive",
                CyclePathsFormula(false),
                "For every natural n and every family of permutations of Fin n containing the cyclic shift finRotate(n), the relation generated by the family connects every ordered pair. Iterating the cyclic shift by the residue s-r sends r to s. The empty cycle is included.",
                DescribeRole.Theorem),
            Node("torus-paths", "Paths on a rectangular replica torus", "torus_twists_transitive",
                CyclePathsFormula(true),
                "For every pair of natural dimensions n and m, a family of permutations of Fin n times Fin m that contains the cyclic shift in each coordinate connects every ordered pair. First move the first coordinate to its target, then move the second coordinate. Empty dimensions are included.",
                DescribeRole.Theorem),
            Node("entropy-limit", "The replica entropy asymptotic", "replica_entropy_asymptotic",
                EntropyLimitFormula(),
                "For every integer n>2, suppose epsilon is a real-valued function with a^2 epsilon(a) tending to a positive C as a tends to positive infinity. Let D_0,D_1,D_2,D_3 be continuous real functions positive at zero. Define Phi_0(a)=sqrt(epsilon(a)^(n^2)/(epsilon(a)D_0(epsilon(a)))) and Phi_i(a)=sqrt(epsilon(a)^n/(epsilon(a)D_i(epsilon(a)))) for i=1,2,3. Then (log(Phi_0)/n-(log(Phi_1)+log(Phi_2)+log(Phi_3))/2)/(1-n) is asymptotically equivalent to ((2-n)/(2n))log(a). The exact logarithmic expression is ((n-2)/(4n))log(epsilon(a)) plus log(D_0(epsilon(a)))/(2n(n-1)) minus the sum of the other three logarithms divided by 4(n-1). The latter terms have finite limits, and log(epsilon(a)) is equivalent to -2log(a).",
                DescribeRole.Theorem))));


    private static Formula StochasticKernelFormula() => Disp(
        All(F.Id("R"), Call("NonemptyFiniteTypes"), All(F.Id("K"), Call("Types"),
            All(F.Id("M"), MatrixType(F.Id("R"), F.Id("R")),
                All(F.Id("g"), Seq(Call("Perm", F.Id("R")), Caret, Grp(F.Id("K"))), Seq(
                    Call("RowStochastic", F.Id("M")), Comma, Quad,
                    Call("PositiveTwistEntries", F.Id("M"), F.Id("g")), Comma, Quad,
                    Call("TransitiveTwistPaths", F.Id("g")), Implies, Sp,
                    Call("Fix", F.Id("M")), Eq, Call("Constants", F.Id("R"))))))));

    private static Formula PermutationKernelFormula() => Disp(
        All(F.Id("R"), Call("NonemptyFiniteTypes"), All(F.Id("K"), Call("FiniteTypes"),
            All(F.Id("g"), Seq(Call("Perm", F.Id("R")), Caret, Grp(F.Id("K"))),
                All(Seq(F.Id("k"), Underscore, D(0)), F.Id("K"),
                    Seq(Call("g", Seq(F.Id("k"), Underscore, D(0))), Eq, F.Id("id"),
                    Comma, Quad, Call("TransitiveTwistPaths", F.Id("g")), Implies, Sp,
                    Call("RowStochastic", Seq(Transpose(F.Id("Q")), F.Id("Q"))), Comma, Quad,
                    Call("Fix", Seq(Transpose(F.Id("Q")), F.Id("Q"))), Eq,
                    Call("Constants", F.Id("R"))))))));

    private static Formula DeterminantFactorFormula(bool permutationAverage)
    {
        Formula assumptions = permutationAverage
            ? Seq(Call("IdentityMember", F.Id("g")), Comma, Quad,
                Call("TransitiveTwistPaths", F.Id("g")))
            : Seq(Call("Hermitian", F.Id("G")), Comma, Quad,
                Call("RowStochastic", F.Id("G")), Comma, Quad,
                Call("Fix", F.Id("G")), Eq, Call("Constants", F.Id("R")));
        Formula matrix = permutationAverage ? Seq(Transpose(F.Id("Q")), F.Id("Q")) : F.Id("G");
        Formula factor = Seq(Exists, Sp, F.Id("D"), Sp, InMacro, Sp, Seq(Reals, To, Reals), Comma, Sp,
            Call("Continuous", F.Id("D")), Comma, Quad, D(0), Lt, Call("D", D(0)), Comma, Quad,
            All(Varepsilon, Reals, Seq(Det(Seq(
                Square(Seq(Frac, Grp(D(1), Plus, Varepsilon), Grp(D(2)))), Identity, Minus,
                Square(Seq(Frac, Grp(D(1), Minus, Varepsilon), Grp(D(2)))), matrix)), Eq,
                Varepsilon, Call("D", Varepsilon))));
        return Disp(All(F.Id("R"), Call("NonemptyFiniteTypes"),
            All(F.Id(permutationAverage ? "g" : "G"),
                permutationAverage ? Call("FinitePermutationFamilies", F.Id("R")) : MatrixType(F.Id("R"), F.Id("R")),
                Seq(assumptions, Implies, Sp, factor))));
    }

    private static Formula CyclePathsFormula(bool torus)
    {
        Formula domain = torus ? Seq(Call("Fin", F.Id("n")), Times, Call("Fin", F.Id("m"))) : Call("Fin", F.Id("n"));
        Formula body = All(F.Id("K"), Call("Types"),
            All(F.Id("g"), Seq(Call("Perm", domain), Caret, Grp(F.Id("K"))),
                Seq(Call(torus ? "ContainsBothCoordinateShifts" : "ContainsCyclicShift", F.Id("g")),
                    Implies, Sp, Call("TransitiveTwistPaths", F.Id("g")))));
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        return Disp(All(F.Id("n"), naturals, torus ? All(F.Id("m"), naturals, body) : body));
    }

    private static Formula EntropyLimitFormula() => Disp(
        All(F.Id("n"), Seq(Mathbb, Grp(F.Id("N"))),
            All(Varepsilon, Seq(Reals, To, Reals), All(F.Id("C"), Reals,
                All(F.Id("D"), Call("FourContinuousRealFunctions"), Seq(
                    D(2), Lt, F.Id("n"), Comma, Quad, D(0), Lt, F.Id("C"), Comma, Quad,
                    Call("lim", Seq(F.Id("a"), Caret, D(2), Varepsilon, Open, F.Id("a"), Close)),
                    Eq, F.Id("C"), Comma, Quad, Call("PositiveAtZero", F.Id("D")), Implies, Sp,
                    Call("IsEquivalent", Call("atTop"), Call("ReplicaEntropy", F.Id("n"), Varepsilon, F.Id("D")),
                        Seq(Frac, Grp(D(2), Minus, F.Id("n")), Grp(D(2), F.Id("n")), Call("log")))))))));

    private static Formula BinaryFormula()
    {
        Formula x = F.Id("x"), y = F.Id("y"), z = F.Id("z"), a = F.Id("a"), b = F.Id("b");
        Formula body = Seq(x, Plus, y, Plus, z, Eq, D(1), Implies, Sp,
            Call("D", a, b, Call("A", x, y, z)),
            Call("D", a, b, Call("B", x, y, z)),
            Call("D", a, b, Call("C", x, y, z)), Eq,
            Square(Seq(Open, a, Minus, b, Close)), Call("D", a, b, Call("Q", x, y, z)));
        return Disp(All(x, Reals, All(y, Reals, All(z, Reals, All(a, Reals, All(b, Reals, body))))));
    }

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("gaussian-reduction-" + id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
