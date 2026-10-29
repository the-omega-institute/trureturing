using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Algebraic;

internal sealed class KurkovA107667WeightedBallotDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Algebraic/KurkovA107667WeightedBallot.";
    private const string TriangleQuote =
        "Triangular matrix T, read by rows, that satisfies: T = D + SHIFT_LEFT(T^2) "
        + "where SHIFT_LEFT shifts each row 1 place to the left and D is the diagonal "
        + "matrix {1, 2, 3, ...}.";
    private const string FormulaQuote =
        "Conjecture: T(n+m, m) = (n+m+1) * P(n+1, n+1, m) where P(n, k, m) = "
        + "P(n-1, k, m) + (n+m) * P(n, k-1, m) for 1 < k < n with P(n, 1, m) = 1, "
        + "P(n, n, m) = (n+m) * P(n, n-1, m). - _Mikhail Kurkov_, Jun 02 2026";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceComposition/kurkov2026a107667");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Kurkov's weighted-ballot formula for the A107667 triangle.",
        H("Kurkov's Weighted-Ballot Formula for A107667"),
        Blocks(
            Paragraph(Text(
                "All indices and table entries are natural numbers. T is zero-indexed. "
                + "P has three arguments and is constrained only on r >= k >= 1; it is "
                + "different from the two-argument conjugating matrix also called P in "
                + "the OEIS entry. Natural subtraction is truncated at zero. "
                + "OEIS A107667 revision 25 has no page numbers; the locators below "
                + "are its NAME and FORMULA fields.")),
            Node("IsSourceTriangle", "The source triangle", TriangleFormula(),
                "NAME, verbatim: " + TriangleQuote
                + " The function T has type N -> N -> N. Lower triangularity and "
                + "ordinary matrix multiplication give the finite interval sum. "
                + "The diagonal entry in row a is a+1, as in the displayed row zero 1.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("IsPTable", "Kurkov's three-argument table", PTableFormula(),
                "FORMULA, verbatim: " + FormulaQuote
                + " The source's row variable n is called r in IsPTable. The base "
                + "rule applies for r >= 1; the diagonal rule applies for r >= 2. "
                + "Thus P(1,1,m)=1 comes from the base rule. Values outside "
                + "r >= k >= 1 are unrestricted and do not occur in the conclusion.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The two-parameter conjecture",
                Disp(Seq(Named("claim"), Sp, Iff, Sp, ClaimBody())),
                "FORMULA, verbatim: " + FormulaQuote
                + " The claim quantifies over every natural-valued T and P satisfying "
                + "the displayed source rules, and over every n,m in N, including zero.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The weighted-ballot identity", Disp(ClaimBody()),
                "The identity holds for every pair of source tables. A zero extension "
                + "of P satisfies a first-return convolution with parameter shifts "
                + "m+1 and m+i+1. Induction proves that convolution directly from "
                + "the three recurrence rules; strong induction on the row-column "
                + "difference then identifies the diagonal values with T. The proof "
                + "does not construct a separate bijection between path sets.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("kur107667-ballot"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(
        string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
            DescribeId.Create("a107667-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, openProblemResolutionClaim: resolution);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Named(name), [.. args]);
    private static Formula Value(string name, params Formula[] args) =>
        new Formula.Apply(F.Id(name), [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id(name), Colon, Sp, type)), Comma, Sp, body);
    private static Formula AllNat(string name, Formula body) => All(name, Naturals(), body);
    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);
    private static Formula Add(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Lt(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula ImpliesFormula(Formula a, Formula b) =>
        Seq(Parenthesized(a), Sp, Implies, Sp, b);
    private static Formula Conjunction(Formula a, Formula b, Formula c) =>
        Seq(Parenthesized(a), Sp, Land, Sp, Parenthesized(b), Sp, Land, Sp, Parenthesized(c));

    private static Formula TriangleFormula()
    {
        Formula t = F.Id("T"), a = F.Id("a"), b = F.Id("b"), j = F.Id("j");
        Formula b1 = Add(b, D(1));
        Formula interval = new Formula.Apply(
            Seq(Named("Finset"), Dot, Named("Icc")), [b1, a]);
        Formula sum = Seq(new Formula.Subscript(F.Sum,
            Seq(j, Sp, InMacro, Sp, interval)), Sp,
            Parenthesized(Mul(Value("T", a, j), Value("T", j, b1))));
        Formula body = Conjunction(
            AllNat("a", AllNat("b", ImpliesFormula(Lt(a, b), Eq(Value("T", a, b), D(0))))),
            AllNat("a", Eq(Value("T", a, a), Add(a, D(1)))),
            AllNat("a", AllNat("b", ImpliesFormula(Lt(b, a), Eq(Value("T", a, b), sum)))));
        return Disp(All("T", Arrow(Naturals(), Arrow(Naturals(), Naturals())),
            Seq(Call("IsSourceTriangle", t), Sp, Iff, Sp, body)));
    }

    private static Formula PTableFormula()
    {
        Formula p = F.Id("P"), r = F.Id("r"), k = F.Id("k"), m = F.Id("m");
        Formula rm = Add(r, m);
        Formula body = Conjunction(
            AllNat("r", AllNat("m", ImpliesFormula(Le(D(1), r), Eq(Value("P", r, D(1), m), D(1))))),
            AllNat("r", AllNat("k", AllNat("m", ImpliesFormula(Lt(D(1), k),
                ImpliesFormula(Lt(k, r), Eq(Value("P", r, k, m),
                    Add(Value("P", Sub(r, D(1)), k, m),
                        Mul(Parenthesized(rm), Value("P", r, Sub(k, D(1)), m))))))))),
            AllNat("r", AllNat("m", ImpliesFormula(Le(D(2), r),
                Eq(Value("P", r, r, m), Mul(Parenthesized(rm), Value("P", r, Sub(r, D(1)), m)))))));
        return Disp(All("P", Arrow(Naturals(), Arrow(Naturals(), Arrow(Naturals(), Naturals()))),
            Seq(Call("IsPTable", p), Sp, Iff, Sp, body)));
    }

    private static Formula ClaimBody()
    {
        Formula t = F.Id("T"), p = F.Id("P"), n = F.Id("n"), m = F.Id("m");
        Formula identity = Eq(Value("T", Add(n, m), m),
            Mul(Parenthesized(Add(Add(n, m), D(1))), Value("P", Add(n, D(1)), Add(n, D(1)), m)));
        return All("T", Arrow(Naturals(), Arrow(Naturals(), Naturals())),
            All("P", Arrow(Naturals(), Arrow(Naturals(), Arrow(Naturals(), Naturals()))),
                ImpliesFormula(Call("IsSourceTriangle", t),
                    ImpliesFormula(Call("IsPTable", p), AllNat("n", AllNat("m", identity))))));
    }
}
