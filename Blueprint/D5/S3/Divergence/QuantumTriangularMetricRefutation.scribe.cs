using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Divergence;

internal sealed class QuantumTriangularMetricRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Divergence/QuantumTriangularMetricRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumBounds/liu2025quantumtriangular");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The square root of quantum triangular discrimination fails every uniform quasi-triangle inequality.",
        H("The square root of QTD is not a metric"),
        Blocks(
            SourceQuotation(),
            Entry("triangle-inequality", "claim", "The proposed triangle inequality", Claim(),
                "Open Problem 8.16 asks whether the square root of Definition 3.1 satisfies the "
                + "triangle inequality for every triple of quantum states in every finite dimension. "
                + "IsState means positive semidefinite with trace one. QTD is the original matrix "
                + "functional-calculus expression, with the inverse square root taken on the support. "
                + "The quantifier over dimensions also includes zero.",
                DescribeRole.Definition, true),
            Entry("unbounded-triangle-ratio", "no_quasi_triangle", "No uniform quasi-triangle constant",
                NoQuasiTriangle(),
                "For 0<t≤1/4, let ρ±=(1+t⁶)⁻¹[[1,±t³],[±t³,t⁶]] and "
                + "τ=diag(1−t⁴,t⁴). The endpoint matrices are positive semidefinite of rank one "
                + "and trace one, while τ is positive definite of trace one. Equivalently, the "
                + "endpoint parameter is r=t³ and the diagonal parameter is b=t⁴. "
                + "The sum ρ++ρ− is diagonal, and QTD(ρ+,ρ−)=2t³/(1+t⁶). "
                + "To calculate a short edge, put a=t⁶/(1+t⁶), b=t⁴, "
                + "d=√(b(2−b)+(1−2b)a), u=b²+(1−2b)a and v=b(1−b). "
                + "A positive definite two-by-two matrix S of trace two has inverse square root "
                + "((2+d)I−S)/(d√(2+2d)), where d²=det S. The existing "
                + "CommutingMidpoint identities sqrt_trace_square_two and "
                + "sqrt_times_trace_two give sqrt(S)=(S+dI)/√(2+2d). "
                + "The displayed inverse is checked by multiplication, then identified "
                + "with the negative half power using half_inverse. The trace identity "
                + "Tr(M²)=(Tr M)²−2det M, applied to M=(ρ+−τ)(ρ++τ)⁻¹ᐟ², gives "
                + "QTD(ρ+,τ)=u/d+v²/(d²(1+d)). Changing the sign of the coherence gives "
                + "QTD(τ,ρ−)=QTD(ρ+,τ). The scalar bounds d²≥3t⁴/2, d≥t², "
                + "u≤17t⁶/16 and v²≤t⁸ imply QTD(ρ+,τ)≤83t⁴/48<7t⁴/4. "
                + "For an arbitrary real K, choose m≥max(1,K) and t=1/(8m²). Then "
                + "4m²QTD(ρ+,τ)<QTD(ρ+,ρ−). Taking nonnegative square roots gives the "
                + "strict comparison in the displayed statement. Thus a fixed multiplicative "
                + "constant cannot restore the triangle inequality even on qubit states.",
                DescribeRole.Theorem, false),
            Entry("refutation", "result", "The triangle inequality fails",
                Disp(Seq(Neg, Sp, Parenthesized(ClaimBody()))),
                "Apply the preceding theorem at K=1. Its three qubit states satisfy the strict "
                + "reverse of the proposed triangle inequality, contradicting its dimension-two "
                + "instance. Hence the square root of QTD is not a distance metric. The contrast "
                + "with classical triangular discrimination concerns this particular quantum "
                + "extension and does not identify a different quantum divergence with QTD.",
                DescribeRole.Theorem, false))));

    private static DocumentBlock SourceQuotation() => Paragraph(Text(
        "Yupan Liu, Complexity-theoretic perspectives on quantum state testing, PhD thesis, "
        + "Nagoya University, Open Problem 8.16, printed p. 180, asks: "
        + "“Is it possible to prove that the square root of quantum triangular discrimination, "
        + "denoted as √QTD, is a distance metric? Specifically, for any quantum states ρ0, ρ1, "
        + "and ρ2, can it be shown that the following inequality holds: "
        + "√QTD(ρ0, ρ1) + √QTD(ρ1, ρ2) ≥ √QTD(ρ0, ρ2)?” "
        + "The same proposed triangle inequality appears in §1.3 of Quantum state testing "
        + "beyond the polarizing regime and quantum triangular discrimination, "
        + "arXiv:2303.01952v5; Computational Complexity 34 (2025), article 11."));

    private static DocumentBlock Entry(string id, string name, string title, Formula formula,
        string prose, DescribeRole role, bool literature) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(formula),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role,
            name == "result" ? new OpenProblemResolutionClaim(
                ProblemSlugRef.Create("liu-2025-qtd-triangle-inequality-refutation"),
                ResolutionKind.Refuted) : null);

    private static Formula V(string name) => F.Id(name);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, V(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Add, Parenthesized(b));
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(Parenthesized(a), FormulaBinaryOperator.Multiply, Parenthesized(b));
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
    private static Formula Real => Seq(Mathbb, Grp(V("R")));
    private static Formula Complex => Seq(Mathbb, Grp(V("C")));
    private static Formula Mat(Formula n) => Call("Matrix", Call("Fin", n), Call("Fin", n), Complex);
    private static Formula Rho0 => V("rho0");
    private static Formula Rho1 => V("rho1");
    private static Formula Rho2 => V("rho2");
    private static Formula State(Formula rho) => Call("IsState", rho);
    private static Formula Distance(Formula rho, Formula sigma) =>
        Seq(Sqrt, Grp(Call("QTD", rho, sigma)));
    private static Formula ShortSum => Add(Distance(Rho0, Rho1), Distance(Rho1, Rho2));
    private static Formula ClaimBody() => All("n", Nat,
        All("rho0", Mat(V("n")), All("rho1", Mat(V("n")), All("rho2", Mat(V("n")),
            Imp(State(Rho0), Imp(State(Rho1), Imp(State(Rho2),
                Le(Distance(Rho0, Rho2), ShortSum))))))));
    private static Formula Claim() => Disp(
        new Formula.Logic(V("claim"), FormulaLogicOperator.Iff, Parenthesized(ClaimBody())));
    private static Formula NoQuasiTriangle() => Disp(All("K", Real,
        Ex("rho0", Mat(D(2)), Ex("rho1", Mat(D(2)), Ex("rho2", Mat(D(2)),
            And(State(Rho0), And(State(Rho1), And(State(Rho2),
                Lt(Mul(V("K"), ShortSum), Distance(Rho0, Rho2))))))))));
}
