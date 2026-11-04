using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.GaussianMultiEntropy;

internal sealed class ResidualLimitDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ResidualLimit.";
    private static Formula Det(Formula x) => Seq(Operatorname, Grp(F.Id("det")), Open, x, Close);
    private static Formula Sub(string name, Formula index) => Seq(F.Id(name), Underscore, Grp(index));
    private static Formula Gram => Seq(Alpha, Sp, F.Id("I"), Minus, Beta, Sp, F.Id("Q"), Caret, Grp(F.Id("T")), F.Id("Q"));
    private static Formula LogP(Formula index) => Seq(Log, Sp, Sub("P", index));
    private static Formula LogH(Formula index) => Seq(Log, Sp, Sub("H", index));
    private static Formula Lam(Formula index) => Seq(LambdaLower, Underscore, Grp(index));
    private static Formula PQ => F.Id("pq");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For the fully symmetric pure Gaussian state with positive party sizes, the discrete Fourier basis of the replica torus and of the replica cycle diagonalizes the four replica Gram determinants. The resulting spectral products give the genuine multi-entropy exactly and identify the constant term of its large-squeezing expansion as a ratio of residual determinants.",
        H("Fourier replica products and the residual-determinant limit"),
        Blocks(
            Node("torus", "The tripartite replica determinant", "tripartite_gram_det",
                Disp(Seq(Det(Gram), Eq, Prod, Underscore, Grp(F.Id("p"), Comma, F.Id("q")),
                    Open, Alpha, Minus, Beta, Lam(PQ), Close)),
                "Let n be positive and let A, B, C be natural numbers with positive sum N. On the replica torus with n^2 points, let Q be the average of the three party twists with weights A/N, B/N and C/N, where A and B shift one torus coordinate each and C acts trivially. For all real alpha and beta, the determinant of alpha I - beta Q^T Q is the product over the n^2 frequency pairs (p, q) of alpha - beta lambda_pq, with lambda_pq = |A omega^p + B omega^q + C|^2 / N^2 and omega = exp(2 pi i / n). The torus characters are common eigenvectors of the twists, Q acts on them by the averaged inverse eigenvalue and Q^T by the averaged eigenvalue, and the dual Fourier matrix inverts the Fourier matrix up to the factor n^2.",
                DescribeRole.Theorem),
            Node("cycle", "The bipartite replica determinant", "cycle_gram_det",
                Disp(Seq(Det(Gram), Eq, Prod, Underscore, Grp(F.Id("k")),
                    Open, Alpha, Minus, Beta, Lam(F.Id("k")), Close)),
                "Let n be positive and let U, V be natural numbers with positive sum. On the replica cycle of length n, let Q average the cyclic shift with weight U/(U+V) and the identity with weight V/(U+V). For all real alpha and beta, the determinant of alpha I - beta Q^T Q is the product over k in Fin n of alpha - beta lambda_k, with lambda_k = |U omega^k + V|^2 / (U+V)^2. The cycle characters diagonalize the twists and the same Fourier argument applies.",
                DescribeRole.Theorem),
            Node("weight", "Eigenvalue defects as sine weights", "one_sub_tripartiteEigenvalue",
                Disp(Seq(D(1), Minus, Lam(PQ), Eq, Frac,
                    Grp(D(4), Sub("w", PQ)), Grp(F.Id("N"), Caret, D(2)))),
                "For real A, B, C with nonzero sum N and natural p, q, the defect 1 - lambda_pq equals 4 w_pq / N^2, where w_pq = AB sin^2(pi (p - q)/n) + AC sin^2(pi p/n) + BC sin^2(pi q/n). The proof writes omega^p and omega^q through cosine and sine of twice the half angles and expands the squared modulus.",
                DescribeRole.Theorem),
            Node("fourier", "The Fourier product formula", "GM3_eq_fourierGM",
                Disp(Seq(F.Id("GM"), Underscore, F.Id("n"), Eq, Frac,
                    Grp(D(2), LogP(D(3)), Minus, F.Id("n"), Open, LogP(F.Id("A")), Plus, LogP(F.Id("B")), Plus,
                        LogP(F.Id("C")), Close),
                    Grp(D(4), F.Id("n"), Open, F.Id("n"), Minus, D(1), Close))),
                "For every replica order n >= 2, all positive integer party sizes A, B, C and every real a >= 1, put N = A + B + C and x = (a^2 - 1)/(N - 1). The genuine multi-entropy of the replica integral definition equals the displayed expression, with P_3 the product over the n^2 torus modes of 1 + x w_pq and P_i the product over k in Fin n of 1 + x u_i sin^2(pi k/n), where u_A = A(B + C), u_B = B(A + C) and u_C = C(A + B). The parameter epsilon of the symmetric state satisfies (1 - epsilon)^2 = epsilon N^2 x, so each replica factor ((1 + epsilon)/2)^2 - ((1 - epsilon)/2)^2 lambda equals epsilon (1 + x w); the powers of epsilon cancel against the one-replica normalizations.",
                DescribeRole.Theorem),
            Node("constant", "The residual-determinant constant", "residualConstant",
                Disp(Seq(Sub("K", F.Id("n")), Eq, Frac,
                    Grp(D(2), LogH(D(3)), Minus, F.Id("n"), Open, LogH(F.Id("A")), Plus, LogH(F.Id("B")), Plus,
                        LogH(F.Id("C")), Close),
                    Grp(D(4), F.Id("n"), Open, F.Id("n"), Minus, D(1), Close))),
                "The tripartite residual product D_3 is the product of 1 - lambda_pq over the n^2 - 1 nonconstant torus modes, and each cut residual product D_i is the product of 1 - lambda_k over the n - 1 nonconstant cycle modes. The leading coefficients are H_3 = D_3 [N^2/(4(N - 1))]^(n^2 - 1) and H_i = D_i [N^2/(4(N - 1))]^(n - 1), and K_n is the displayed combination of their logarithms.",
                DescribeRole.Definition),
            Node("limit", "The residual-determinant limit", "residual_determinant_limit",
                Disp(Seq(Lim, Underscore, Grp(F.Id("a"), To, Infty), Open, F.Id("GM"), Underscore,
                    F.Id("n"), Plus, Frac, Grp(F.Id("n"), Minus, D(2)), Grp(D(2), F.Id("n")), Log, Sp,
                    F.Id("a"), Close, Eq, Sub("K", F.Id("n")))),
                "For every replica order n >= 2 and all positive integer party sizes, the genuine multi-entropy plus ((n - 2)/(2n)) log a tends to the residual-determinant constant K_n as a tends to positive infinity. Every nonconstant Fourier mode has a positive sine weight, so each factor log(1 + x w) - 2 log a tends to log(w/(N - 1)); the products of these limits over the nonconstant modes are log H_3 and log H_i, and the constant modes contribute the coefficient (n - 2)/(2n) of log a.",
                DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("gaussian-residual-" + id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role, null);
}
