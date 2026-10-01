using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.SpinChains;

internal sealed class WStateTIMPSBondDimensionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/SpinChains/WStateTIMPSBondDimension.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/QuantumStates/klimov2023wstate");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two 3 x 3 matrices give a translation-invariant matrix product state representation with periodic boundary conditions of the normalized W-state of order 7. Its bond dimension 3 is smaller than floor(7/2) + 1 = 4. This refutes the conjecture of P. Klimov, R. Sengupta and J. Biamonte (arXiv:2306.16456) that no such representation of the W-state of order n has bond dimension smaller than floor(n/2) + 1, and shows that d(7) is at most 3, not 4 as in the paper's table.",
        H("A bond-dimension-3 translation-invariant MPS of the seven-qubit W-state"),
        Blocks(
            Node("rep", "Translation-invariant representations of the W-state", RepFormula(),
                "A pair A(0), A(1) of complex d x d matrices represents the normalized W-state of order n, as a translation-invariant matrix product state with periodic boundary conditions, when for every word w in {0, 1}^n the trace of the ordered product A(w_0) A(w_1) ... A(w_(n-1)) equals the amplitude of the basis vector |w> in the W-state: 1/sqrt(n) when w has exactly one letter 1, and 0 otherwise. In Lean the words are maps Fin n -> Fin 2 and the product is the product of a list in index order.",
                "IsWStateTIMPS", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The conjecture", ClaimFormula(),
                "For every n >= 2, every d and all complex d x d matrices A(0), A(1) representing the W-state of order n, the bond dimension d is at least floor(n/2) + 1. The paper conjectures that no representation has bond dimension smaller than floor(n/2) + 1; the hypothesis n >= 2 only weakens the claim, and the paper's table of d(n) starts at n = 2. Here floor(n/2) is the natural-number division n / 2.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Bond dimension 3 for n = 7", Disp(new Formula.Not(F.Id("claim"))),
                "Take A(0) = E_12 + E_21 + E_23 and A(1) = E_31 / sqrt(7), 3 x 3 matrices with E_ij the matrix units. Then A(0)^3 = A(0), and the (1, 3) entry of A(0)^r is 1 for even r >= 2 and 0 otherwise. The trace of a word with k >= 1 letters 1 is 7^(-k/2) times the product of the (1, 3) entries of A(0)^r over the k cyclic gaps r between consecutive letters 1, which add up to 7 - k. For k = 1 the gap is 6 and the trace is 1/sqrt(7). For k >= 2 the gaps cannot all be even and at least 2: that needs 3k <= 7, so k = 2, and then the two gaps add up to 5, which is odd. For k = 0 the trace of A(0)^7 = A(0) is 0. So the pair represents the W-state of order 7 with bond dimension 3 < 4. In Lean the 128 word traces of the integer matrices are computed by the kernel, and the factor 1/sqrt(7) is pulled out of each word.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("klimov-2023-w-state-ti-mps-bond-dimension"),
                    ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create("wstatemps-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Named(Formula name) => Seq(Operatorname, Grp(name));
    private static Formula Call(Formula name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Rel(Formula left, FormulaRelationOperator op, Formula right) =>
        new Formula.Relation(left, op, right);
    private static Formula Equal(Formula left, Formula right) =>
        Rel(left, FormulaRelationOperator.Equal, right);
    private static Formula Le(Formula left, Formula right) =>
        Rel(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, right);
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula Plus(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Ite(Formula condition, Formula then, Formula otherwise) =>
        Call(F.Id("ite"), condition, then, otherwise);
    private static Formula Sub(Formula value, Formula index) => new Formula.Subscript(value, index);

    private static Formula RepFormula()
    {
        Formula n = F.Id("n"), d = F.Id("d"), a = F.Id("A"), w = F.Id("w"), i = F.Id("i");
        Formula words = new Formula.Power(Seq(OpenBrace, D(0), Comma, Sp, D(1), CloseBrace), n);
        Formula product = Seq(F.Prod, Underscore, Grp(i, Eq, D(0)), Caret, Grp(n, F.Minus, D(1)), Sp,
            Sub(a, Sub(w, i)));
        Formula weight = Seq(F.Sum, Underscore, Grp(i), Sp, Sub(w, i));
        Formula amplitude = Ite(Equal(weight, D(1)),
            new Formula.Fraction(D(1), Seq(Sqrt, Grp(n))), D(0));
        Formula body = Seq(Forall, Sp, w, Sp, InMacro, Sp, words, Comma, Sp,
            Equal(Call(F.Id("tr"), product), amplitude));
        return Disp(Iff(Call(F.Id("IsWStateTIMPS"), n, d, a), body));
    }

    private static Formula ClaimFormula()
    {
        Formula n = F.Id("n"), d = F.Id("d"), a = F.Id("A");
        Formula hypotheses = And(Le(D(2), n), Call(F.Id("IsWStateTIMPS"), n, d, a));
        Formula bound = Le(Plus(new Formula.Floor(new Formula.Fraction(n, D(2))), D(1)), d);
        Formula body = Seq(Forall, Sp, n, Comma, Sp, d, Comma, Sp, a, Comma, Sp,
            Implies(hypotheses, bound));
        return Disp(Iff(F.Id("claim"), body));
    }
}
