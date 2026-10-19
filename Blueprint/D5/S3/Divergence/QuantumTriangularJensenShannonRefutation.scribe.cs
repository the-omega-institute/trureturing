using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Divergence;

internal sealed class QuantumTriangularJensenShannonRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Divergence/QuantumTriangularJensenShannonRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumBounds/liu2025quantumtriangular");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A full-rank commuting qubit pair has quantum triangular discrimination squared greater than base-2 quantum Jensen–Shannon divergence.",
        H("QTD squared can exceed QJS2"),
        Blocks(
            SourceQuotation(),
            Entry("jensen-shannon", "QJS2", "Quantum Jensen–Shannon divergence", JensenShannon(),
                "Definition 2.10 with base-2 logarithms is the entropy of the average state minus the average entropy.",
                DescribeRole.Definition, true),
            Entry("triangular", "QTD", "Quantum triangular discrimination", Triangular(),
                "Definition 3.1 uses the inverse square root of the sum between two copies of the difference. "
                + "The function x↦x^(−1/2) has value zero at zero in the real-power convention, "
                + "so the inverse acts on the support of the sum.",
                DescribeRole.Definition, true),
            Entry("lower-bound", "claim", "The proposed lower inequality", Claim(),
                "For every finite dimension and every pair of quantum states, the assertion requires QTD²≤QJS₂. "
                + "This is the lower conjunct of the proposed two-sided bound.",
                DescribeRole.Definition, true),
            Entry("refutation", "result", "A commuting qubit counterexample", Disp(Seq(Neg, Sp, Parenthesized(ClaimBody()))),
                "Take ρ=diag(255/256,1/256) and σ=diag(1/256,255/256). Both states have strictly positive "
                + "diagonal entries and unit trace. Their sum is the identity, so its inverse square root is the identity. "
                + "The difference has diagonal entries 127/128 and −127/128, giving QTD=(127/128)². "
                + "The average is the maximally mixed qubit state with entropy one. Both input entropies equal "
                + "h(1/256), where h(a)=−a log₂ a−(1−a) log₂(1−a). Since log₂(1/256)=−8 "
                + "and log₂(255/256)<0, h(1/256)≥1/32. Thus QJS₂≤31/32<(127/128)⁴=QTD², "
                + "and QTD²−QJS₂≥97793/268435456. The matrices commute, so the failure already occurs "
                + "for classical probability distributions. The general family diag(1−a,a), diag(a,1−a) "
                + "has Q=(1−2a)² and J=1−h(a). Mathematical reasoning, not additional formal theorems here, "
                + "gives (1−J)/(1−Q)=h(a)/(4a(1−a))→∞ as a→0⁺. Consequently no fixed p>0 "
                + "makes Q^p≤J universal, and no function F with F(1)=1 that is locally Lipschitz at one "
                + "makes F(Q)≤J universal. The logarithmic entropy deficit near orthogonal supports causes "
                + "this obstruction. The upper inequality QJS₂≤QTD and the metric assertion for √QTD "
                + "are not addressed.",
                DescribeRole.Theorem, false))));

    private static DocumentBlock SourceQuotation() => Paragraph(Text(
        "Yupan Liu, Quantum state testing beyond the polarizing regime and quantum triangular discrimination, "
        + "arXiv:2303.01952v5; Computational Complexity 34 (2025), article 11. "
        + "§1.3, Improved inequalities on the quantum triangular discrimination, printed p. 7, verbatim: "
        + "“We observe that Theorem 1.4(ii) is not tight. Numerical simulations indicate that the tight bound is "
        + "QTD²(ρ₀, ρ₁) ≤ QJS₂(ρ₀, ρ₁) ≤ QTD(ρ₀, ρ₁) for any states ρ₀ and ρ₁.” "
        + "After Theorem 3.4, verbatim: “Numerical simulations suggest that the tight bound is "
        + "QTD²(ρ₀, ρ₁) ≤ QJS₂(ρ₀, ρ₁) ≤ QTD(ρ₀, ρ₁), while we only managed to prove a slightly weaker bound "
        + "½QTD²(ρ₀, ρ₁) ≤ QJS₂(ρ₀, ρ₁) ≤ QTD(ρ₀, ρ₁) in Theorem 3.4.”"));

    private static DocumentBlock Entry(string id, string name, string title, Formula formula,
        string prose, DescribeRole role, bool literature) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(formula),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role,
            name == "result" ? new OpenProblemResolutionClaim(
                ProblemSlugRef.Create("liu-2025-qtd-qjs-lower-bound-refutation"),
                ResolutionKind.Refuted) : null);

    private static Formula V(string name) => F.Id(name);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Half(Formula a) => new Formula.Fraction(a, D(2));
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
    private static Formula Complex => Seq(Mathbb, Grp(V("C")));
    private static Formula Mat => Call("Matrix", Call("Fin", V("n")), Call("Fin", V("n")), Complex);
    private static Formula Rho => V("rho");
    private static Formula Sigma => V("sigma");
    private static Formula Pair(Formula body) => All("n", Nat, All("rho", Mat, All("sigma", Mat, body)));
    private static Formula Scale(Formula a, Formula b) =>
        Seq(Parenthesized(a), Sp, Cdot, Sp, Parenthesized(b));

    private static Formula JensenShannon() => Disp(Pair(Eq(Call("QJS2", Rho, Sigma),
        Sub(Call("vonNeumann2", Scale(Half(D(1)), Add(Rho, Sigma))),
            Half(Add(Call("vonNeumann2", Rho), Call("vonNeumann2", Sigma)))))));
    private static Formula Triangular()
    {
        Formula difference = Sub(Rho, Sigma);
        Formula inverseRoot = Call("cfc", Parenthesized(Seq(V("x"), Sp, Mapsto, Sp, new Formula.Power(V("x"), Half(Seq(Minus, Sp, D(1)))))), Add(Rho, Sigma));
        return Disp(Pair(Eq(Call("QTD", Rho, Sigma), Half(Call("re", Call("trace",
            Mul(Mul(Mul(difference, inverseRoot), difference), inverseRoot)))))));
    }
    private static Formula ClaimBody() => Pair(Imp(Call("IsState", Rho), Imp(Call("IsState", Sigma),
        Le(new Formula.Power(Call("QTD", Rho, Sigma), D(2)), Call("QJS2", Rho, Sigma)))));
    private static Formula Claim() => Disp(new Formula.Logic(V("claim"), FormulaLogicOperator.Iff, ClaimBody()));
}
