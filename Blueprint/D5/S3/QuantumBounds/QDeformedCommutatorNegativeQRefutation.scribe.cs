using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumBounds;

internal sealed class QDeformedCommutatorNegativeQRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuantumBounds/QDeformedCommutatorNegativeQRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumBounds/chruscinski2022qdeformed");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A traceless complex matrix of size three and a rank-one projector violate the proposed q-deformed commutator inequality at q = −1.",
        H("A counterexample to the negative-q commutator bound"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("qcomm-negative-q-g"),
                DeclarationHandle.Create(Prefix + "g"),
                H("The dimension-dependent coefficient"),
                StatementSource.FromAuthor(GFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Equation (24) defines the real coefficient g(n) = (n² − 3n + 3)/(n(n − 1)). The natural number n is embedded in the real numbers in every arithmetic operation. For n at least two, the denominator is positive. As a total real-valued function, g uses the real division convention also at n = 0 and n = 1; the inequality below only concerns n at least two."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("qcomm-negative-q-claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("The inequality in Conjecture 2"),
                StatementSource.FromAuthor(ClaimFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Chruściński, Kimura, Ohno and Singal define [A,B]q = AB − qBA. Conjecture 2 in Section 3 states that, for any q ≤ 0, if A or B is traceless, the sharp bound has coefficient max[g(n)(1 − q)², 1 + q²]. Here mass M = ∑ᵢ ∑ⱼ |M i j|² is the squared Frobenius norm. Fin n indexes rows and columns by 0,…,n−1. The real scalar q is embedded in the complex numbers for scalar multiplication of matrices. The displayed claim is the inequality clause for all dimensions n at least two, all nonpositive real q and all complex matrix pairs satisfying the disjunction of trace conditions. A violation of the inequality also refutes the assertion that it holds and is sharp."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("qcomm-negative-q-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("A three-dimensional counterexample"),
                StatementSource.FromAuthor(Disp(new Formula.Not(F.Id("claim")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Take n = 3, q = −1, A = diag(2,−1,−1) and B = diag(1,0,0). The trace of A is 2 − 1 − 1 = 0, while the trace of B is 1. Their squared Frobenius norms are mass A = 6 and mass B = 1. The products satisfy AB = BA = diag(2,0,0), so AB − qBA = diag(4,0,0) and its squared Frobenius norm is 16. Equation (24) gives g(3) = 1/2, hence max[g(3)(1 − (−1))², 1 + (−1)²] = 2. The proposed bound becomes 16 ≤ 2 · 6 · 1 = 12, a contradiction. The disjunction of trace conditions admits this pair because A is traceless; the pair does not satisfy the stronger condition that both matrices are traceless."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("chruscinski-2022-qdeformed-commutator-negative-q-refutation"),
                    ResolutionKind.Refuted))),
        []));

    private static Formula Parenthesized(Formula x) => Seq(Open, x, Close);
    private static Formula Blackboard(string name) => Seq(Mathbb, Grp(F.Id(name)));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, F.Id(name), Sp, Colon, Sp, type, Comma, Sp, body);
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula GFormula()
    {
        Formula n = F.Id("n");
        Formula realN = Parenthesized(Seq(n, Sp, Colon, Sp, Blackboard("R")));
        Formula numerator = Seq(new Formula.Power(realN, D(2)), Sp, Minus, Sp,
            D(3), Sp, Cdot, Sp, realN, Sp, Plus, Sp, D(3));
        Formula denominator = Seq(realN, Sp, Cdot, Sp,
            Parenthesized(Seq(realN, Sp, Minus, Sp, D(1))));
        return Disp(All("n", Blackboard("N"), Seq(
            Call("g", n), Sp, Eq, Sp, new Formula.Fraction(numerator, denominator))));
    }

    private static Formula ClaimFormula()
    {
        Formula n = F.Id("n"), q = F.Id("q"), a = F.Id("A"), b = F.Id("B");
        Formula index = Parenthesized(Seq(F.Id("Fin"), Sp, n));
        Formula matrix = Seq(F.Id("Matrix"), Sp, index, Sp, index, Sp, Blackboard("C"));
        Formula traceless = Parenthesized(Seq(
            Call("trace", a), Sp, Eq, Sp, D(0), Sp, Lor, Sp,
            Call("trace", b), Sp, Eq, Sp, D(0)));
        Formula complexQ = Parenthesized(Seq(q, Sp, Colon, Sp, Blackboard("C")));
        Formula commutator = Seq(a, Sp, Cdot, Sp, b, Sp, Minus, Sp,
            complexQ, Sp, Cdot, Sp, Parenthesized(Seq(b, Sp, Cdot, Sp, a)));
        Formula coefficient = Call("max",
            Seq(Call("g", n), Sp, Cdot, Sp,
                new Formula.Power(Parenthesized(Seq(D(1), Sp, Minus, Sp, q)), D(2))),
            Seq(D(1), Sp, Plus, Sp, new Formula.Power(q, D(2))));
        Formula inequality = Seq(Call("mass", commutator), Sp, Leq, Sp,
            coefficient, Sp, Cdot, Sp, Call("mass", a), Sp, Cdot, Sp, Call("mass", b));
        Formula matrices = Seq(Forall, Sp, a, Sp, b, Sp, Colon, Sp, matrix, Comma, Sp,
            traceless, Sp, To, Sp, inequality);
        Formula quantified = All("n", Blackboard("N"), Seq(
            D(2), Sp, Leq, Sp, n, Sp, To, Sp,
            All("q", Blackboard("R"), Seq(q, Sp, Leq, Sp, D(0), Sp, To, Sp, matrices))));
        return Disp(Seq(F.Id("claim"), Sp, Iff, Sp, quantified));
    }
}
