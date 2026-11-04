using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum;

internal sealed class CampoamorStursbergZernikeLadderDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/CampoamorStursbergZernikeLadder.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/LieTheory/campoamor2026zernike");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The generalized polynomial quantum Zernike Hamiltonian has ladders with the factorized structure function for every N.",
        H("Zernike ladder factorization for every order"), Blocks(
            Describe.Lean(DescribeId.Create("zernike-ladder-claim"), DeclarationHandle.Create(Prefix + "claim"), H("The factorized ladder assertion"),
                StatementSource.FromAuthor(Disp(E(X("claim"), ClaimBody()))), AssessedProvenance.FromLiterature(Source), Blocks(
                    Paragraph(Text("The set (Ĉ, Î_N, Î'_N) leads to the quantum symmetries K̂₁, K̂₂, K̂₃ in (2.8) and, in consequence, it is possible to define the number and ladder operators K̂, K̂₊, K̂₋ verifying the commutation relations (2.9) with the structure function Φ = Φ₁Φ₂ (2.10), whose factorizing terms are given by Φ₁(Ĥ_N, K̂) = ¼ (Ĥ_N − Σ_{k=1}^N (2i)^k γ_k K̂^k), Φ₂(Ĥ_N, K̂) = Ĥ_N − Σ_{k=1}^N (−2i)^k γ_k (K̂ − Id)^k. (5.1)")),
                    Paragraph(Text("The quotation is Conjecture 1(iii), page 19 of arXiv:2502.02491v2. The displayed proposition uses complex linear endomorphisms of MvPolynomial (Fin 2) Complex, source coordinates 1 and 2 indexed by Fin 2 values 0 and 1, every N at least 1, and every complex coefficient sequence gamma. Only coefficients 1 through N occur. IsSymmetry specifies the positive-degree, grading-zero span in (2.6) and commutation with the Hamiltonian. Membership in Algebra.adjoin expresses construction from the three operators of (2.8). angularMomentum is the source K1. Products are operator composition; a centered dot is scalar multiplication."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("zernike-ladder-result"), DeclarationHandle.Create(Prefix + "result"), H("Ladders with the factorization (5.1)"),
                StatementSource.FromAuthor(Disp(ClaimBody())), AssessedProvenance.FromRepo(Source), Blocks(
                    Paragraph(Text("Put x=p(0)+Complex.I times p(1), y=p(0)-Complex.I times p(1), qp=q(0)+Complex.I times q(1), and qm=q(0)-Complex.I times q(1). The raising operator is half the sum of x squared and x qp times divided(N,gamma,dot,Complex.I times (angularMomentum+2)); the lowering operator is half the sum of y squared and y qm times divided(N,gamma,dot,Complex.I times (2-angularMomentum)). Weyl shift relations and the geometric-sum identity give both ordered products and commutation with the Hamiltonian directly in the endomorphism ring.")),
                    Paragraph(Text("The two symmetries are half the Hamiltonian minus or plus half the sum of the ladders. Normal ordering bounds each correction by total degree 2N with grading zero and positive degree. Their k2 is half the sum of the ladders, and k3 is their difference, so the ladders and half the angular momentum belong to the required generated algebra. The two ordered products are phi at half the angular momentum and at its shift by 1.")),
                    Paragraph(Text("The conclusion holds for all complex coefficients, including zero coefficients. It gives the degree and momentum-order upper bound in (2.6). Exact order at degenerate coefficients, algebraic independence in Conjecture 1(ii), and analytic Hilbert-space or spectrum conclusions in Conjecture 2 are outside this proposition."))), DescribeRole.Theorem, openProblemResolutionClaim: new OpenProblemResolutionClaim(ProblemSlugRef.Create("campoamor-stursberg-et-al-2025-zernike-ladder-factorization"), ResolutionKind.Proved)))));
    private static Formula ExistsOp(Formula name, Formula body) => Seq(Exists, Sp, Parenthesized(Seq(name, Colon, Sp, Operators)), Comma, Sp, body);
    private static Formula ClaimBody()
    {
        Formula i = X("I"), j = Seq(X("I"), Apos), k = X("K"), kp = X("Kp"), km = X("Km");
        Formula h = Call("hamiltonian", X("N"), X("gamma"));
        Formula generators = Seq(OpenBrace, X("k1"), Comma, Sp, Call("k2", i, j), Comma, Sp, Call("k3", i, j), CloseBrace);
        Formula algebra = Apply(Q("Algebra", "adjoin"), Cplx, generators);
        Formula phi = Call("phi", X("N"), X("gamma"), h, k);
        Formula body = And(E(Sub(M(k, kp), M(kp, k)), kp), E(Sub(M(k, km), M(km, k)), MinusOf(km)), E(M(kp, km), phi), E(Sub(M(km, kp), M(kp, km)), Sub(Call("phi", X("N"), X("gamma"), h, A(k, D(1))), phi)));
        body = ExistsOp(km, And(Mem(km, algebra), body));
        body = ExistsOp(kp, And(Mem(kp, algebra), body));
        body = ExistsOp(k, And(Mem(k, algebra), body));
        body = And(Call("IsSymmetry", X("N"), X("gamma"), P(Pop(1), D(2)), i), Call("IsSymmetry", X("N"), X("gamma"), P(Pop(0), D(2)), j), body);
        return All("N", Nat, Imp(LeqOf(D(1), X("N")), All("gamma", Coefficients, ExistsOp(i, ExistsOp(j, body)))));
    }

    private static Formula X(string name) => F.Id(name);
    private static Formula Q(string owner, string name) => Seq(Operatorname, Grp(X(owner)), Dot, Operatorname, Grp(X(name)));
    private static Formula Apply(Formula function, params Formula[] args) => Seq(function, Parenthesized(Seq(args.SelectMany((a, i) => i == 0 ? new[] { a } : new[] { Comma, Sp, a }).ToArray())));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Nat => Seq(Mathbb, Grp(X("N")));
    private static Formula Cplx => Seq(Mathbb, Grp(X("C")));
    private static Formula Operators => Apply(Q("Module", "End"), Cplx, Call("MvPolynomial", Call("Fin", D(2)), Cplx));
    private static Formula Arrow(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp, Parenthesized(Seq(X(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula Imp(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Implies, Sp, Parenthesized(b));
    private static Formula And(params Formula[] items) => Seq(items.SelectMany((a, i) => i == 0 ? new[] { Parenthesized(a) } : new[] { Sp, Land, Sp, Parenthesized(a) }).ToArray());
    private static Formula E(Formula a, Formula b) => Equal(a, b);
    private static Formula M(Formula a, Formula b) => Seq(Parenthesized(a), Sp, Star, Sp, Parenthesized(b));
    private static Formula P(Formula a, Formula n) => new Formula.Power(Parenthesized(a), n);
    private static Formula A(Formula a, Formula b) => Add(a, b);
    private static Formula Sub(Formula a, Formula b) => Subtract(a, b);
    private static Formula MinusOf(Formula a) => Seq(Minus, Parenthesized(a));
    private static Formula LeqOf(Formula a, Formula b) => Seq(a, Sp, Leq, Sp, b);
    private static Formula Mem(Formula a, Formula b) => Seq(a, Sp, InMacro, Sp, b);
    private static Formula Pop(byte i) => Call("p", D(i));
    private static Formula Coefficients => Arrow(Nat, Cplx);
}
