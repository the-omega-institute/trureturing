using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.AbsoluteSeparability;

internal sealed class LowRankRaysAveragesDocument : IScribeDocumentDefinition
{
    private static Formula Call(string n, params Formula[] xs) => new Formula.Apply(F.Id(n), [.. xs]);
    private static Formula Par(Formula x) => F.Seq(F.Open, x, F.Close);
    private static Formula Add(Formula a, Formula b) => F.Seq(a, F.Plus, b);
    private static Formula Mul(Formula a, Formula b) => F.Seq(a, F.Cdot, F.Sp, b);
    private static Formula Kron(Formula a, Formula b) => Call("kronecker", a, b);
    private static Formula Rank(Formula x) => Call("R", x);
    private static Formula Rho(Formula x) => Call("rho", x);
    private static Formula Sep(Formula x) => Call("separableCone", x);
    private static Formula Psd(Formula x) => Call("PosSemidef", x);
    private static Formula Pow(Formula x, byte n) => new Formula.Power(x, F.D(n));
    private static Formula All(string n, Formula t, Formula b) =>
        F.Seq(F.Forall, F.Sp, Par(F.Seq(F.Id(n), F.Colon, t)), F.Comma, F.Sp, b);
    private static Formula And(Formula a, Formula b) => F.Seq(Par(a), F.Land, F.Sp, Par(b));
    private static Formula C => F.Seq(F.Mathbb, F.Grp(F.Id("C")));
    private static Formula Real => F.Seq(F.Mathbb, F.Grp(F.Id("R")));
    private static Formula Nat => F.Seq(F.Mathbb, F.Grp(F.Id("N")));
    private static Formula M => F.Id("m");
    private static Formula N => F.Id("n");
    private static Formula Fin(Formula x) => Call("Fin", x);
    private static Formula Pair => F.Seq(Fin(M), F.Times, F.Sp, Fin(N));
    private static Formula Vec(Formula x) => F.Seq(x, F.To, F.Sp, C);
    private static Formula Mat(Formula x) => Call("Matrix", x, x, C);
    private static Formula Dims(Formula x) => All("m", Nat, All("n", Nat, x));
    private static Formula Dimensional(string v, Formula body) => Dims(All(v, Vec(Par(Pair)), body));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite complex moments produce separable averages containing an arbitrary rank-one matrix.",
        H("Finite product-vector averages"), Blocks(
            Paragraph(Text("For a vector eta on Fin m times Fin n, its reduced matrix rho_eta is the sum of the rank-one matrices of its rows. Write R_x = xx*. The finite list Omega = (0,0,0,0,sqrt(2),-sqrt(2),i sqrt(2),-i sqrt(2)) retains its four zero entries. Uniform averaging over functions g from Fin m to Fin 8 gives zero first and third moments, covariance equal to the identity, zero unconjugated second moments, and the two-pair fourth-moment identity.")),
            Node("reduced", "The reduced matrix", Dimensional("eta",
                F.Seq(Rho(F.Id("eta")), F.Eq, new Formula.Subscript(F.Sum, F.Seq(F.Id("i"), F.InMacro, F.Sp, Fin(M))),
                    F.Sp, Rank(Call("row", F.Id("eta"), F.Id("i"))))),
                "Each row is a vector on Fin n. This is the matrix used in both product-vector averages.", DescribeRole.Definition),
            Node("separable_kronecker", "A positive product belongs to the separable cone",
                Dims(All("A", Mat(Fin(M)), All("B", Mat(Fin(N)),
                    F.Seq(And(Psd(F.Id("A")), Psd(F.Id("B"))), F.Rightarrow, F.Sp,
                        Sep(Kron(F.Id("A"), F.Id("B"))))))),
                "The cone includes every Kronecker product of two positive semidefinite factors. Finite sums and nonnegative real scalings preserve it.", DescribeRole.Lemma),
            Node("separable_rankOne_add_reduced", "The row-contraction average", Dimensional("eta",
                Sep(Add(Rank(F.Id("eta")), Kron(F.Id("I"), Rho(F.Id("eta")))))),
                "Put y_eta(g) = sum_i conjugate(g_i) row_i(eta). The fourth moments give E R_(g tensor y_eta(g)) = R_eta + I tensor rho_eta. Every vector in this finite average is a product vector, so the matrix belongs to the separable cone.", DescribeRole.Theorem),
            Node("separable_projected_rankOne", "An average with a selected product component", ProjectedStatement(),
                "Let P be a Hermitian idempotent fixing every column of chi. For real a and arbitrary local vectors u,v, set psi = a u tensor v + chi. With z(g) = (sqrt(2) a u + Pg) tensor (v/sqrt(2) + y_chi(g)), the finite average E R_z equals R_psi + (P + 2 a squared R_u) tensor rho_chi + one half P tensor R_v. The first and third moments remove the odd terms. The covariance supplies the quadratic terms, and the two fourth-moment pairings supply the rank-one and reduced-matrix terms.", DescribeRole.Theorem))));

    private static Formula ProjectedStatement()
    {
        var p = F.Id("P");
        var chi = F.Id("chi");
        var a = F.Id("a");
        var col = Call("column", chi, F.Id("j"));
        var support = All("j", Fin(N), F.Seq(Call("mulVec", p, col), F.Eq, col));
        var hypotheses = And(Call("IsHermitian", p), And(F.Seq(Pow(p, 2), F.Eq, p), support));
        var psi = Add(Mul(a, Call("product", F.Id("u"), F.Id("v"))), chi);
        var correction = Kron(Add(p, Mul(Mul(F.D(2), Pow(a, 2)), Rank(F.Id("u")))), Rho(chi));
        var half = F.Seq(F.Frac, F.Grp(F.D(1)), F.Grp(F.D(2)));
        var conclusion = Sep(Add(Add(Rank(psi), correction), Mul(half, Kron(p, Rank(F.Id("v"))))));
        var body = All("P", Mat(Fin(M)), F.Seq(hypotheses, F.Rightarrow, F.Sp, conclusion));
        body = All("a", Real, body);
        body = All("v", Vec(Fin(N)), body);
        body = All("u", Vec(Fin(M)), body);
        return Dimensional("chi", body);
    }

    private static DocumentBlock Node(string name, string title, Formula formula, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("low-rank-average-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsoluteSeparability/LowRankRaysAverages." + name),
            H(title), StatementSource.FromAuthor(F.Disp(formula)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);
}
