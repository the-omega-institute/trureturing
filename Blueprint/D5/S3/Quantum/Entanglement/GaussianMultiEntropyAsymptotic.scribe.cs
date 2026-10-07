using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement;

internal sealed class GaussianMultiEntropyAsymptoticDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/GaussianMultiEntropyAsymptotic.";
    private static Formula Det(Formula x) => Seq(Operatorname, Grp(F.Id("det")), Open, x, Close);
    private static Formula Hpsilon => Seq(F.Id("H"), Underscore, Grp(Varepsilon));
    private static Formula EPow => Seq(Varepsilon, Caret, Grp(F.Id("m")));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Twisting the replica coordinates of a real Gaussian state produces a positive-definite quadratic form. Its determinant evaluates the literal product integral.",
        H("Gaussian replica determinants"),
        Blocks(
            Node("precision", "The averaged precision", "H",
                Disp(Seq(Hpsilon, Eq, D(1), Minus, Open, D(1), Minus, Varepsilon, Close,
                    Seq(Frac, Grp(F.Id("P"), Underscore, D(0), Plus, F.Id("P"), Underscore, D(1)), Grp(D(2))))),
                "Let N be the positive total number of modes and m the number of replicas. P is the matrix with all entries 1/N, the orthogonal projection onto constant mode coordinates. On replica coordinates, P_0 = I_m tensor P. If U maps x to its primed coordinates under the party permutations, P_1 = U^T P_0 U and T = (P_0 + P_1)/2. The matrix H_epsilon is I - (1-epsilon) T. The reindexing defining P_1 uses the inverse coordinate permutation on both matrix indices.",
                DescribeRole.Definition),
            Node("integral", "The replica projection formula", "replica_integral_projection_formula",
                Disp(Seq(F.Id("Z"), Open, Alpha, Open, D(1), Minus, Open, D(1), Minus,
                    Varepsilon, Close, F.Id("P"), Close, Close, Eq,
                    Sqrt, Grp(Frac, Grp(EPow), Grp(Det(Hpsilon))))),
                "For every finite replica type, every list of party sizes with positive total, and every permutation of the replicas for each party, assume alpha > 0 and 0 < epsilon <= 1. The replica contraction is the Lebesgue integral of the product of the Gaussian density kernels with precision alpha times (I - (1-epsilon) P). It equals sqrt(epsilon^m / det H_epsilon). Empty replica types and zero-sized individual parties are included. Uncurrying the replica variables preserves their product Lebesgue measure. The exponent becomes the quadratic form of alpha H_epsilon. The determinant of the single-copy precision is alpha^N epsilon, and the common alpha and pi factors cancel.",
                DescribeRole.Theorem),
            Node("parameters", "The physical parameter range", "symmetric_parameters",
                Disp(Seq(Alpha, Eq, F.Id("a"), Minus, F.Id("e"), Caret, Grp(Minus), Comma, Quad,
                    Varepsilon, Eq, Frac,
                    Grp(F.Id("a"), Plus, Open, F.Id("N"), Minus, D(1), Close, F.Id("e"), Caret, Grp(Minus)),
                    Grp(Alpha), Comma, Quad, D(0), Lt, Alpha, Comma, Quad,
                    D(0), Lt, Varepsilon, Leq, D(1))),
                "For a >= 1 and N >= 3, the fully symmetric state's off-diagonal entry e^- is nonpositive and a + (N-1)e^- is positive. Thus alpha = a-e^- is positive, and epsilon = (a+(N-1)e^-)/alpha lies in (0,1]. The two square-root comparisons follow from the differences of their squares; the upper comparison is strict even at a = 1.",
                DescribeRole.Theorem),
            Node("state", "The fully symmetric precision", "W_projection_formula",
                Disp(Seq(F.Id("W"), Eq, Alpha, Open, D(1), Minus, Open, D(1), Minus,
                    Varepsilon, Close, F.Id("P"), Close)),
                "For every positive mode count N and every a with a-e^- nonzero, the matrix W with diagonal a and off-diagonal e^- equals alpha times (I-(1-epsilon)P), with alpha and epsilon as above. Transporting this identity to the tagged party coordinates gives the same precision for the replica integral.",
                DescribeRole.Theorem),
            Node("normalization", "One replica is normalized", "replica_integral_singleton",
                Disp(Seq(F.Id("Z"), Underscore, D(1), Eq, D(1))),
                "For any positive-definite real matrix on the party coordinates, a finite singleton replica type has contraction equal to one. Every party twist fixes its single replica. The averaged precision is the original block precision, so the determinant ratio equals one.",
                DescribeRole.Theorem),
            Node("reduction", "Reduction to replica coordinates", "replica_determinant_reduction",
                Disp(All(F.Id("R"), Call("FiniteTypes"),
                    All(F.Id("p"), Call("List", Seq(Mathbb, Grp(F.Id("N")))),
                        All(F.Id("g"), Seq(Call("Perm", F.Id("R")), Caret,
                            Grp(Call("length", F.Id("p")))),
                            All(Varepsilon, Seq(Mathbb, Grp(F.Id("R"))), Seq(
                                D(0), Lt, Call("sum", F.Id("p")), Comma, Quad,
                                D(0), Lt, Varepsilon, Implies, Sp,
                                Det(Call("H", F.Id("p"), F.Id("g"), Varepsilon)), Eq,
                                Det(Seq(Frac, Grp(Open, D(1), Plus, Varepsilon, Close, Caret, D(2)),
                                    Grp(D(4)), F.Id("I"), Underscore, F.Id("R"), Minus,
                                    Frac, Grp(Open, D(1), Minus, Varepsilon, Close, Caret, D(2)),
                                    Grp(D(4)), Call("Q", F.Id("p"), F.Id("g")), Caret, F.Id("T"),
                                    Call("Q", F.Id("p"), F.Id("g")))))))))),
                "For any finite replica type R, any party list p with positive total N, any family g of replica permutations, and epsilon > 0, define Q(r,s) as the sum of 1/N over the modes whose party twist sends s to r. Then det H_epsilon equals the displayed determinant on R. The untwisted normalized indicator columns have entries [i=r]/sqrt(N), and their permuted columns have entries [i=g_k(r)]/sqrt(N). Both column families are orthonormal, their overlap is Q, and their outer products are the two constant-mode projections. The paired-column determinant identity gives the reduction.",
                DescribeRole.Theorem),
            Node("entropy", "The entropy determinant expression", "multi_entropy_determinant_formula",
                Disp(Seq(F.Id("GM"), Underscore, F.Id("n"), Caret, Grp(Open, D(3), Close), Eq,
                    Frac, Grp(D(1)), Grp(D(1), Minus, F.Id("n")),
                    Open, Frac, Grp(D(1)), Grp(F.Id("n")), Log, Phi, Underscore, D(3), Minus,
                    Frac, Grp(D(1)), Grp(D(2)), Open,
                    Log, Phi, Underscore, Grp(F.Id("AB"), F.Colon, F.Id("C")), Plus,
                    Log, Phi, Underscore, Grp(F.Id("BC"), F.Colon, F.Id("A")), Plus,
                    Log, Phi, Underscore, Grp(F.Id("CA"), F.Colon, F.Id("B")), Close, Close)),
                "For every natural replica order n, every positive tripartition, and a >= 1, put N = N_A + N_B + N_C and epsilon = (a+(N-1)e^-)/(a-e^-). Let Phi_3 be sqrt(epsilon^(n^2)/det H_epsilon) for the tripartite torus twists. Each Phi_R is sqrt(epsilon^n/det H_epsilon) for the corresponding bipartition and cyclic twist. Substituting the replica integrals and their one-replica normalizations into the entropy definitions gives the displayed identity. The replica-coordinate reduction applies to each of these four determinants.",
                DescribeRole.Theorem),
            Node("binary-identity", "Binary replicas and bipartitions", "replica_two_determinant_identity",
                BinaryIdentityFormula(),
                "For every natural tripartition A, B, C with positive total and every epsilon > 0, the product of the three bipartite H determinants equals epsilon^2 times the tripartite H determinant at replica order two. Put x=A/N, y=B/N, z=C/N. The binary cyclic twist is a swap. Reindexing the tripartite torus by its four coordinates gives the real matrix with rows (z,y,x,0), (y,z,0,x), (x,0,z,y), and (0,x,y,z). The reduced bipartite matrices and this tripartite matrix satisfy the binary determinant identity with a=((1+epsilon)/2)^2 and b=((1-epsilon)/2)^2. Here a-b=epsilon.",
                DescribeRole.Theorem),
            Node("binary-zero", "Vanishing binary multi-entropy", "determinantGM3_two_eq_zero",
                BinaryZeroFormula(),
                "For all positive integer party sizes A, B, C and all a >= 1, determinantGM3(2,A,B,C,a) is exactly zero. The physical epsilon lies in (0,1], so each H is positive definite and its determinant is positive. Taking the logarithm of the binary determinant identity gives log det H_AB:C + log det H_BC:A + log det H_CA:B = 2 log epsilon + log det H_3. This relation cancels all four terms of the binary entropy expression.",
                DescribeRole.Theorem),
            Node("claim", "The large-squeezing conjecture", "claim",
                Disp(All(F.Id("n"), Seq(Mathbb, Grp(F.Id("N"))),
                    All(F.Id("A"), Seq(Mathbb, Grp(F.Id("N"))),
                        All(F.Id("B"), Seq(Mathbb, Grp(F.Id("N"))),
                            All(F.Id("C"), Seq(Mathbb, Grp(F.Id("N"))), Seq(
                                D(2), Leq, Sp, F.Id("n"), Comma, Quad,
                                D(0), Lt, F.Id("A"), Comma, Quad,
                                D(0), Lt, F.Id("B"), Comma, Quad,
                                D(0), Lt, F.Id("C"), Implies, Sp,
                                Call("IsEquivalent", Call("atTop"),
                                    Call("GM", F.Id("n"), F.Id("A"), F.Id("B"), F.Id("C")),
                                    Call("mul", FracOf(Seq(D(2), Minus, F.Id("n")),
                                        Seq(D(2), F.Id("n"))), Call("log"))))))))),
                "For every integer replica order n >= 2 and every positive integer tripartition A, B, C, the genuine tripartite multi-entropy is asymptotically equivalent to ((2-n)/(2n)) log(a) as the real squeezing parameter a tends to positive infinity. At n = 2 the comparison function is identically zero, so equivalence means eventual exact vanishing.",
                DescribeRole.Definition),
            Node("result", "The large-squeezing asymptotic", "result",
                Disp(F.Id("claim")),
                "The conjecture holds for every replica order n >= 2 and every positive tripartition. At n = 2 the exact binary determinant identity gives zero multi-entropy for all a >= 1. For n > 2 the torus and cyclic twists connect their replicas and contain an identity twist. Their permutation averages have Gram matrices with constant fixed space, so each H determinant is epsilon times a continuous function positive at zero. Since a^2 epsilon(a) tends to (N-1)/N^2, log(epsilon(a)) is asymptotically equivalent to -2log(a). Substitution into the four determinant entropies gives the coefficient (2-n)/(2n); the remaining terms have finite limits.",
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("camargo-nishida-2026-gaussian-multientropy"),
                    ResolutionKind.Proved)))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);
    private static Formula All(Formula v, Formula domain, Formula body) =>
        Seq(Forall, Sp, v, Sp, InMacro, Sp, domain, Comma, Sp, body);
    private static Formula FracOf(Formula a, Formula b) => Seq(Frac, Grp(a), Grp(b));

    private static Formula Tripartition(Formula a, Formula b, Formula c, Formula body) =>
        All(a, Seq(Mathbb, Grp(F.Id("N"))),
            All(b, Seq(Mathbb, Grp(F.Id("N"))), All(c, Seq(Mathbb, Grp(F.Id("N"))), body)));
    private static Formula BinaryIdentityFormula()
    {
        Formula a = F.Id("A"), b = F.Id("B"), c = F.Id("C");
        return Disp(Tripartition(a, b, c, All(Varepsilon, Seq(Mathbb, Grp(F.Id("R"))),
            Seq(D(0), Lt, a, Plus, b, Plus, c, Comma, Quad, D(0), Lt, Varepsilon,
                Implies, Sp, Det(Call("HAB", a, b, c, Varepsilon)),
                Det(Call("HBC", a, b, c, Varepsilon)), Det(Call("HCA", a, b, c, Varepsilon)), Eq,
                Varepsilon, Caret, D(2), Det(Call("Hthree", a, b, c, Varepsilon))))));
    }
    private static Formula BinaryZeroFormula()
    {
        Formula a = F.Id("A"), b = F.Id("B"), c = F.Id("C"), t = F.Id("a");
        return Disp(Tripartition(a, b, c, All(t, Seq(Mathbb, Grp(F.Id("R"))),
            Seq(D(0), Lt, a, Comma, Quad, D(0), Lt, b, Comma, Quad, D(0), Lt, c,
                Comma, Quad, D(1), Leq, Sp, t, Implies, Sp,
                Call("determinantGM", D(2), a, b, c, t), Eq, D(0)))));
    }

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, DescribeRole role,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("gaussian-me-" + id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role, resolution);
}
