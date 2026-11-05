using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.GaussianMultiEntropy;

internal sealed class ReplicaFourDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/GaussianMultiEntropy/ReplicaFour.";
    private static Formula Sub(string name, Formula index) => Seq(F.Id(name), Underscore, Grp(index));
    private static Formula M => F.Id("m");
    private static Formula A2 => Seq(F.Id("a"), Caret, D(2));
    private static Formula GM4 => Sub("GM", D(4));
    private static Formula K4 => Sub("K", D(4));
    private static Formula C4 => Sub("c", D(4));
    private static Formula Law => Seq(Minus, Frac, Grp(Log, Sp, F.Id("a")), Grp(D(4)), Plus, K4, Open, M, Close,
        Plus, Frac, Grp(C4, Open, M, Close), Grp(A2));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "At replica order four the sixteen Fourier modes of the replica torus collapse the tripartite product of the fully symmetric pure Gaussian state into the three cut products and three squared factors. For party sizes (m, 1, 1) this gives an exact closed form of the genuine multi-entropy, its constant, its first correction and a uniform bound for the remainder.",
        H("Replica order four for the (m, 1, 1) Gaussian state"),
        Blocks(
            Node("product", "The order-four product identity", "tripartiteProduct_four",
                Disp(Seq(Sub("P", D(3)), Eq, Sub("P", F.Id("A")), Sub("P", F.Id("B")), Sub("P", F.Id("C")),
                    Prod, Underscore, Grp(F.Id("v")), Open, D(1), Plus, Frac,
                    Grp(F.Id("x"), Open, F.Id("s"), Plus, F.Id("v"), Close), Grp(D(2)), Close, Caret, D(2))),
                "For nonnegative real A, B, C with nonzero sum and every real x, the order-four tripartite product equals the product of the three cut products with coefficients A(B + C), B(A + C), C(A + B) and of the squares of 1 + x(s + v)/2 for v in {AB, AC, BC}, where s = AB + AC + BC. At n = 4 the root of unity is i, and the sixteen sine weights take the values 0, u_i/2, u_i and (s + v)/2.",
                DescribeRole.Theorem),
            Node("closed", "The closed form for (m, 1, 1)", "GM3_four_closed",
                Disp(Seq(GM4, Eq, Frac, Grp(D(1)), Grp(D(2, 4)), Log, Sp, Frac,
                    Grp(Open, Open, D(3), M, Plus, D(1), Close, A2, Minus, M, Plus, D(1), Close, Caret, D(4)),
                    Grp(Open, M, Plus, D(1), Close, Open, M, Sp, A2, Plus, D(1), Close, Caret, D(2),
                        Open, D(2), M, Sp, A2, Minus, M, Plus, D(1), Close, Open, A2, Plus, D(1), Close, Caret, D(4)))),
                "For every integer m >= 1 and every real a >= 1, the genuine multi-entropy at replica order four of the fully symmetric pure Gaussian state with party sizes (m, 1, 1) is one twenty-fourth of the logarithm of the displayed rational function of a^2. With x = (a^2 - 1)/(m + 1), every factor of the order-four product identity is an explicit rational function of a^2, and the Fourier product formula gives the logarithm.",
                DescribeRole.Theorem),
            Node("k4", "The replica-four constant", "K4",
                Disp(Seq(K4, Open, M, Close, Eq, Frac, Grp(D(1)), Grp(D(2, 4)), Log, Sp, Frac,
                    Grp(Open, D(3), M, Plus, D(1), Close, Caret, D(4)),
                    Grp(D(2), M, Caret, D(3), Open, M, Plus, D(1), Close))),
                "The constant term of the large-squeezing expansion at replica order four for party sizes (m, 1, 1).",
                DescribeRole.Definition),
            Node("c4", "The first correction", "c4",
                Disp(Seq(C4, Open, M, Close, Eq, Minus, Frac,
                    Grp(D(2, 9), M, Caret, D(2), Plus, D(1, 4), M, Plus, D(5)),
                    Grp(D(4, 8), M, Open, D(3), M, Plus, D(1), Close))),
                "The coefficient of a^(-2) in the large-squeezing expansion at replica order four for party sizes (m, 1, 1).",
                DescribeRole.Definition),
            Node("remainder", "The expansion with a uniform remainder bound", "GM3_four_remainder",
                Disp(Seq(D(0), Leq, Sp, GM4, Minus, Open, Law, Close, Leq, Frac, Grp(D(1)),
                    Grp(D(8), F.Id("a"), Caret, D(4)))),
                "For every integer m >= 1 and every real a >= 1, the remainder R_4 = GM_4 - (-(log a)/4 + K_4(m) + c_4(m)/a^2) satisfies 0 <= R_4 <= 1/(8a^4). With t = 1/a^2, r = (m - 1)/(3m + 1), b = 1/m and s_0 = (m - 1)/(2m), the closed form gives GM_4 = -(log a)/4 + K_4(m) + h(t)/24 with h(t) = 4 log(1 - rt) - 2 log(1 + bt) - log(1 - s_0 t) - 4 log(1 + t). On [0, 1] the second derivative of h lies between 0 and 6, and two monotonicity arguments for h(t) - h'(0) t and 3t^2 - (h(t) - h'(0) t) give the bounds; h'(0)/24 = c_4(m).",
                DescribeRole.Theorem),
            Node("limit", "The replica-four limit", "GM3_four_tendsto",
                Disp(Seq(Lim, Underscore, Grp(F.Id("a"), To, Infty), Open, GM4, Plus, Frac, Grp(D(1)), Grp(D(4)),
                    Log, Sp, F.Id("a"), Close, Eq, K4, Open, M, Close)),
                "For every integer m >= 1, the genuine multi-entropy at replica order four plus (log a)/4 tends to K_4(m) as a tends to positive infinity. The remainder bound squeezes the difference between K_4(m) + c_4(m)/a^2 and K_4(m) + c_4(m)/a^2 + 1/(8a^4).",
                DescribeRole.Theorem),
            Node("constant", "The residual-determinant constant at order four", "residualConstant_four",
                Disp(Seq(Sub("K", D(4)), Open, M, Comma, D(1), Comma, D(1), Close, Eq, K4, Open, M, Close)),
                "For every integer m >= 1, the residual-determinant constant of replica order four for party sizes (m, 1, 1) equals K_4(m). Both the residual-determinant limit and the replica-four limit describe the limit of the same function, and limits are unique.",
                DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("gaussian-four-" + id),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role, null);
}
