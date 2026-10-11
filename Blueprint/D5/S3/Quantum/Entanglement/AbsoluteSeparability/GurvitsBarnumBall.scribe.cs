using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.AbsoluteSeparability;

internal sealed class GurvitsBarnumBallDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumBounds/gurvitsbarnum2002largest");
    private static Formula Call(string n, params Formula[] xs) => new Formula.Apply(F.Id(n), [.. xs]);
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula All(string n, Formula t, Formula body) =>
        Seq(Forall, Sp, Par(Seq(F.Id(n), Colon, t)), Comma, Sp, body);
    private static Formula Imp(Formula p, Formula q) => Seq(Par(p), Rightarrow, Sp, q);
    private static Formula And(Formula p, Formula q) => Seq(Par(p), Land, Sp, Par(q));
    private static Formula Eq(Formula p, Formula q) => Seq(p, F.Eq, q);
    private static Formula Le(Formula p, Formula q) => Seq(p, Leq, Sp, q);
    private static Formula Sum(string n, Formula t, Formula body) =>
        Seq(new Formula.Subscript(F.Sum, Seq(F.Id(n), Colon, t)), Sp, body);
    private static Formula Arrow(Formula p, Formula q) => Seq(p, To, Sp, q);
    private static Formula Mul(Formula p, Formula q) => Seq(p, Cdot, Sp, q);
    private static Formula Pow2(Formula x) => new Formula.Power(x, D(2));
    private static Formula Norm(Formula x) => new Formula.Norm(x);
    private static Formula C => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula R => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula N => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Index => Seq(Call("Fin", F.Id("m")), Times, Sp, Call("Fin", F.Id("n")));
    private static Formula Vector => Arrow(Index, C);
    private static Formula Matrix => Arrow(Index, Arrow(Index, C));
    private static Formula Identity => F.Id("I");
    private static Formula Herm(Formula x) => Call("Hermitian", x);
    private static Formula PSD(Formula x) => Call("PSD", x);
    private static Formula BP(Formula x) => Call("BlockPositive", x);
    private static Formula SEP(Formula x) => Call("SeparableCone", x);
    private static Formula Tr(Formula x) => Call("tr", x);
    private static Formula Re(Formula x) => Call("Re", x);
    private static Formula Frob(Formula x) => Sum("u", Index, Sum("v", Index,
        Pow2(Norm(new Formula.Apply(x, [F.Id("u"), F.Id("v")])))));
    private static Formula Dims(Formula body) => All("m", N, All("n", N, body));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Block positivity bounds the Frobenius sum by the real trace and gives a separable ball about a scalar identity.",
        H("The Gurvits--Barnum separable ball"), Blocks(
            Paragraph(Text("All matrices act on the product index set Fin m times Fin n. SeparableCone consists of finite sums of Kronecker products of positive semidefinite factors. BlockPositive means that the real quadratic form is nonnegative on every product vector. The Frobenius sum below is the sum of squared entry norms, independently of any default norm on matrices. Empty index sets and a ball of radius zero are included.")),
            Describe.Lean(DescribeId.Create("gb-block-positive-frobenius"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsoluteSeparability/GurvitsBarnumBall.frobSq_le_trace_sq_of_blockPositive"),
                H("Block-positive Frobenius bound"), StatementSource.FromAuthor(Disp(Bound())),
                AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text("Szarek--Werner--Zyczkowski, J. Math. Phys. 49, 032113 (2008), printed page 18, states Tr(H squared) ≤ (Tr H) squared for block-positive H, as quoted in the Gurvits--Barnum note. For Hermitian H, the entrywise Frobenius sum equals Tr(H squared), so the formal inequality is the same statement, with the nonnegative real trace also made explicit. Compressing H against a vector in either factor gives a positive semidefinite matrix. Its trace square bounds its Frobenius sum. Applying the corrected finite fourth-moment identity in each factor gives two inequalities whose partial-trace terms cancel. Product basis vectors give the nonnegative trace."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gb-separable-frobenius-ball"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsoluteSeparability/GurvitsBarnumBall.separableCone_of_frob_ball"),
                H("Separable ball criterion"), StatementSource.FromAuthor(Disp(Ball())),
                AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text("Gurvits--Barnum Theorem 1, printed page 4, states that I + Delta is separable when Delta is Hermitian and its Frobenius norm is at most one. The formal statement is its scalar form A = c(I + Delta), using the scaling in Corollary 2, printed page 5; c = 0 gives the zero matrix. If the PSD matrix were outside the separable cone, the separation theorem would give a block-positive matrix with negative Hilbert--Schmidt pairing. Its Hermitian part preserves both product quadratic forms and pairing with the given PSD matrix. The Frobenius bound and Cauchy--Schwarz force that pairing to be nonnegative throughout the stated ball, a contradiction."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gb-rank-one-complement"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsoluteSeparability/GurvitsBarnumBall.separableCone_one_sub_rankOne"),
                H("Unit rank-one complement"), StatementSource.FromAuthor(Disp(RankOne())),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("A unit vector gives an orthogonal rank-one projection of trace one and Frobenius sum one. Its complement is PSD and lies in the radius-one ball about the identity. This supplies the codimension-one ray in a spectral decomposition."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gb-projection-ray"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsoluteSeparability/GurvitsBarnumBall.separableCone_scaled_one_sub_two_projection"),
                H("Projection ray"), StatementSource.FromAuthor(Disp(Projection())),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("For a Hermitian idempotent Q of real trace ell at least one, the matrix is PSD: it is the sum of ell minus one times the identity and twice the complement of Q. Its squared distance from ell plus one times the identity is 4 ell, which is at most the square of ell plus one. The real trace parameter includes integer ranks by coercion. This supplies the complementary high-rank rays in a spectral decomposition."))), DescribeRole.Theorem))));

    private static Formula Bound()
    {
        var h = F.Id("H");
        return Dims(All("H", Matrix, Imp(And(Herm(h), BP(h)),
            And(Le(D(0), Re(Tr(h))), Le(Frob(h), Pow2(Par(Re(Tr(h)))))))));
    }

    private static Formula Ball()
    {
        var r = F.Id("A");
        var c = F.Id("c");
        var error = Par(Seq(r, Minus, Mul(c, Identity)));
        return Dims(All("A", Matrix, All("c", R,
            Imp(And(PSD(r), And(Le(D(0), c), Le(Frob(error), Pow2(c)))), SEP(r)))));
    }

    private static Formula RankOne()
    {
        var psi = F.Id("psi");
        var unit = Eq(Sum("u", Index, Pow2(Norm(Call("psi", F.Id("u"))))), D(1));
        var projector = Call("vecMulVec", psi, Call("star", psi));
        return Dims(All("psi", Vector, Imp(unit, SEP(Par(Seq(Identity, Minus, projector))))));
    }

    private static Formula Projection()
    {
        var q = F.Id("Q");
        var ell = F.Id("ell");
        var ray = Par(Seq(Mul(Par(Seq(ell, Plus, D(1))), Identity), Minus, Mul(D(2), q)));
        return Dims(All("Q", Matrix, All("ell", R,
            Imp(And(Herm(q), And(Eq(Mul(q, q), q), And(Eq(Tr(q), ell), Le(D(1), ell)))),
                SEP(ray)))));
    }
}
