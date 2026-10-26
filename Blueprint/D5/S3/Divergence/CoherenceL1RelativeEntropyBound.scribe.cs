using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Divergence;

internal sealed class CoherenceL1RelativeEntropyBoundDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Divergence/CoherenceL1RelativeEntropyBound.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Divergence/rana2016coherence");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The l1 norm of coherence bounds relative entropy coherence in every finite dimension.",
        H("Relative entropy coherence is at most l1 coherence"),
        Blocks(
            Entry("IsState", "Density matrices", State(),
                "A complex matrix is a quantum state exactly when it is positive semidefinite and has trace one.", true),
            Entry("vonNeumann2", "Base-2 von Neumann entropy", EntropyDefinition(),
                "Entropy is the negative real trace of x log base two x applied by continuous functional calculus; the scalar function is zero at zero.", true),
            Entry("l1Coherence", "The l1 norm of coherence", L1(),
                "Section II, Eq. (3b), p. 2 gives Cl1(X) as the sum of |Xij| over i different from j. The complex norm is that absolute value; both indices run through Fin n.", true),
            Entry("coherenceRel", "Relative entropy coherence", Relative(),
                "Section III, after Eq. (13), p. 4: “The minimization could be solved analytically [2], leading to Cr(ρ) = S(ρdiag)−S(ρ), where S(ρ) = − Tr(ρ log₂ ρ) is the von Neuman entropy.” The scalar functional calculus uses base-two logarithms.", true),
            Entry("reflection", "Reflection associated with a matrix", Reflection(),
                "The reflection associated with P is twice P minus the identity matrix.", false),
            Entry("reflection_hermitian", "Hermitian reflections", ReflectionHermitian(),
                "The reflection associated with a Hermitian matrix is Hermitian.", false),
            Entry("reflection_unitary", "Unitary reflections", ReflectionUnitary(),
                "The reflection associated with a Hermitian idempotent matrix is unitary.", false),
            Entry("claim", "Conjecture 7", Claim(),
                "Section III.2, printed p. 5, verbatim: “Conjecture 7. For all states ρ, C_{l1}(ρ) ≥ C_r(ρ).” Here n ranges over every natural number and rho over every complex n by n matrix. The state predicate imposes positive semidefiniteness and unit trace, including singular states.", true),
            Entry("result", "The coherence inequality", Disp(ClaimBody()),
                "A binary pinching is the average of a state and its conjugate by the unitary reflection 2P minus the identity. The binary Holevo inequality bounds its entropy increase by twice the trace norm of the off-diagonal block. Sequential coordinate pinchings preserve positivity and trace and end at the diagonal matrix. Each block has one nonzero row, so its trace norm is the square root of the sum of squared absolute values in that row above the diagonal. Summing the entropy increments gives Cᵣ(rho) ≤ 2 sum over k of the upper-row l2 norms. Each row l2 norm is at most its l1 norm, and Hermitian symmetry makes twice the upper-triangular sum equal l1Coherence.", false))));
    private static DocumentBlock Entry(string name, string title, Formula formula, string prose, bool literature) => Describe.Lean(
        DescribeId.Create("rpl-" + name.ToLowerInvariant().Replace('_', '-')), DeclarationHandle.Create(name == "l1Coherence"
            ? "D5/S3/Quantum/Information/CorrelatedCoherenceMonogamyRefutation.l1Coherence" : Prefix + name), H(title),
        StatementSource.FromAuthor(formula), literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
        Blocks(Paragraph(Text(prose))), name is "result" or "reflection_hermitian" or "reflection_unitary" ? DescribeRole.Theorem : DescribeRole.Definition,
        name == "result" ? new OpenProblemResolutionClaim(
            ProblemSlugRef.Create("rana-parashar-lewenstein-2016-l1-relative-entropy-coherence"),
            ResolutionKind.Proved) : null);
    private static Formula V(string n) => F.Id(n);
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula Call(string n, params Formula[] a) => new Formula.FunctionCall(FormulaIdentifier.Create(n), [.. a]);
    private static Formula Q(string a, string b) => Seq(Operatorname, Grp(V(a)), Dot, Operatorname, Grp(V(b)));
    private static Formula App(Formula f, params Formula[] a) => Seq(f, Sp, Parenthesized(Seq(a.SelectMany((x, i) => i == 0 ? new[] { x } : new[] { Seq(Comma, Sp), x }).ToArray())));
    private static Formula All(string n, Formula t, Formula b) => Seq(Forall, Sp, Parenthesized(Seq(V(n), Colon, Sp, t)), Comma, Sp, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Lam(string n, Formula t, Formula b) => Parenthesized(Seq(Parenthesized(Seq(V(n), Colon, Sp, t)), Sp, Mapsto, Sp, b));
    private static Formula Sum(string n, Formula t, Formula b) => Seq(new Formula.Subscript(F.Sum, Seq(V(n), Colon, Sp, t)), Sp, Parenthesized(b));
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
    private static Formula Real => Seq(Mathbb, Grp(V("R")));
    private static Formula Complex => Seq(Mathbb, Grp(V("C")));
    private static Formula Fin => Call("Fin", V("n"));
    private static Formula Mat => Call("Matrix", Fin, Fin, Complex);
    private static Formula Entropy(Formula a) => Seq(Minus, Sp, Call("re", Call("trace", Call("cfc",
        Lam("x", Real, Mul(V("x"), App(Q("Real", "logb"), D(2), V("x")))), a))));

    // Lean constant: D5.S3.Quantum.Information.CorrelatedCoherenceMonogamyRefutation.l1Coherence.
    private static Formula L1Owner => Seq(Q("D5", "S3"), Dot, Q("Quantum", "Information"), Dot,
        Q("CorrelatedCoherenceMonogamyRefutation", "l1Coherence"));

    private static Formula Rho => V("rho");
    private static Formula State() => Disp(All("n", Nat, All("rho", Mat,
        new Formula.Logic(Call("IsState", Rho), FormulaLogicOperator.Iff,
            And(Call("PosSemidef", Rho), Eq(Call("trace", Rho), D(1)))))));
    private static Formula EntropyDefinition() => Disp(All("n", Nat, All("rho", Mat,
        Eq(Call("vonNeumann2", Rho), Entropy(Rho)))));
    private static Formula L1()
    {
        var term = Seq(Operatorname, Grp(V("if")), Sp,
            new Formula.Relation(V("i"), FormulaRelationOperator.NotEqual, V("j")), Sp,
            Operatorname, Grp(V("then")), Sp, Vert, Sp, App(Rho, V("i"), V("j")), Vert, Sp,
            Operatorname, Grp(V("else")), Sp, D(0));
        var body = Eq(App(L1Owner, Rho), Sum("i", Fin, Sum("j", Fin, term)));
        return Disp(All("n", Nat, All("rho", Mat, body)));
    }
    private static Formula Reflection() => Disp(All("n", Nat, All("P", Mat,
        Eq(Call("reflection", V("P")), Sub(Seq(D(2), Sp, F.Cdot, Sp, V("P")), D(1))))));
    private static Formula ReflectionHermitian() => Disp(All("n", Nat, All("P", Mat,
        Imp(Call("IsHermitian", V("P")), Call("IsHermitian", Call("reflection", V("P")))))));
    private static Formula ReflectionUnitary() => Disp(All("n", Nat, All("P", Mat,
        Imp(Call("IsHermitian", V("P")), Imp(Eq(Mul(V("P"), V("P")), V("P")),
            new Formula.Relation(Call("reflection", V("P")), FormulaRelationOperator.MemberOf,
                Call("unitaryGroup", Fin, Complex)))))));
    private static Formula Relative() => Disp(All("n", Nat, All("rho", Mat,
        Eq(Call("coherenceRel", Rho), Sub(Call("vonNeumann2", App(Q("Matrix", "diagonal"),
            Lam("i", Fin, App(Rho, V("i"), V("i"))))), Call("vonNeumann2", Rho))))));
    private static Formula ClaimBody() => All("n", Nat, All("rho", Mat, Imp(Call("IsState", Rho),
        Le(Call("coherenceRel", Rho), App(L1Owner, Rho)))));
    private static Formula Claim() => Disp(new Formula.Logic(V("claim"), FormulaLogicOperator.Iff, ClaimBody()));
}
