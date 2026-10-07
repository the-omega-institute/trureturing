using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumBounds;

internal sealed class QDeformedCommutatorTracelessRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuantumBounds/QDeformedCommutatorTracelessRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumBounds/chruscinski2022qdeformed");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two traceless complex matrices of size five violate the proposed q-deformed commutator inequality at q = 2.",
        H("A traceless counterexample to the q-deformed commutator bound"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("qcomm-traceless-claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("The inequality in Conjecture 1"),
                StatementSource.FromAuthor(ClaimFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Chruściński, Kimura, Ohno and Singal define the q-deformed commutator by [A,B]q = AB − qBA. Conjecture 1 in Section 3 states: “For any q > 0, if A or B is traceless, the inequality (7) holds and is sharp.” Here mass M = ∑ᵢ ∑ⱼ |M i j|² is the squared Frobenius norm, using the existing definition from the Moreau–Yosida module. Fin n indexes the rows and columns by 0,…,n−1. The real scalar q is embedded in C for scalar multiplication of matrices. The displayed claim is the inequality clause for every dimension n, every positive real q and every pair of complex matrices satisfying the disjunction of trace conditions. A violation of this clause also refutes the conjunction that the inequality holds and is sharp."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("qcomm-traceless-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("A five-dimensional counterexample"),
                StatementSource.FromAuthor(Disp(new Formula.Not(F.Id("claim")))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Take q = 2 and n = 5. Let A = [6,42; 0,−3] ⊕ (−I₃) and B = [6,0; −42,−3] ⊕ (−I₃), where the bracketed arrays are two-by-two matrices and I₃ is the three-by-three identity. Both traces are 6 − 3 − 1 − 1 − 1 = 0. Their squared Frobenius norms are mass A = mass B = 1812. Direct multiplication gives AB − 2BA = [−1800,−630; 630,3519] ⊕ (−I₃), with mass (AB − 2BA) = 16417164. The proposed upper bound is (1 + 2²) · mass A · mass B = 5 · 1812² = 16416720. Thus 16417164 > 16416720, exceeding the bound by 444 and contradicting claim."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("chruscinski-2022-qdeformed-commutator-traceless-refutation"),
                    ResolutionKind.Refuted))),
        []));

    private static Formula Parenthesized(Formula x) => Seq(Open, x, Close);
    private static Formula Blackboard(string name) => Seq(Mathbb, Grp(F.Id(name)));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, F.Id(name), Sp, Colon, Sp, type, Comma, Sp, body);
    private static Formula Call(string name, Formula argument) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [argument]);

    private static Formula ClaimFormula()
    {
        Formula n = F.Id("n"), q = F.Id("q"), a = F.Id("A"), b = F.Id("B");
        Formula index = Parenthesized(Seq(F.Id("Fin"), Sp, n));
        Formula matrix = Seq(F.Id("Matrix"), Sp, index, Sp, index, Sp, Blackboard("C"));
        Formula traceless = Parenthesized(Seq(
            Call("trace", a), Sp, Eq, Sp, D(0), Sp, Lor, Sp,
            Call("trace", b), Sp, Eq, Sp, D(0)));
        Formula commutator = Seq(a, Sp, b, Sp, Minus, Sp, q, Sp, Cdot, Sp,
            Parenthesized(Seq(b, Sp, a)));
        Formula coefficient = Parenthesized(Seq(D(1), Sp, Plus, Sp, new Formula.Power(q, D(2))));
        Formula inequality = Seq(Call("mass", commutator), Sp, Leq, Sp,
            coefficient, Sp, Cdot, Sp, Call("mass", a), Sp, Cdot, Sp, Call("mass", b));
        Formula matrices = Seq(Forall, Sp, a, Sp, b, Sp, Colon, Sp, matrix, Comma, Sp,
            traceless, Sp, To, Sp, inequality);
        Formula quantified = All("n", Blackboard("N"), All("q", Blackboard("R"),
            Seq(D(0), Sp, Lt, Sp, q, Sp, To, Sp, matrices)));
        return Disp(Seq(F.Id("claim"), Sp, Iff, Sp, quantified));
    }
}
