using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Beatty;

internal sealed class IteratedBeattyRangeRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Beatty/IteratedBeattyRangeRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Arith/khani2026iteratedbeatty");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The positive fixed point two at modulus sqrt two defeats the full proposed extension.",
        H("Iterated Beatty Range: the Universal Extension Fails"),
        Blocks(
            Node("nativeBeatty", "The source's natural floor map", StepFormula(),
                "nativeBeatty(alpha,k) is Mathlib's natural floor of the real product alpha k. "
                + "For alpha>1 all products at natural inputs are nonnegative, so natural floor "
                + "has exactly the integer value of the source's floor.", DescribeRole.Definition),
            Node("nativeRange", "The native iterated range", RangeFormula(),
                "The superscript [n] denotes Function.iterate, the actual n-fold "
                + "composition, including each intermediate floor. It is not floor(alpha^n k). "
                + "The preimage k is a positive natural. For alpha>1 and k>=1, k<=alpha k, hence "
                + "k<=floor(alpha k). Induction keeps every intermediate value positive, so this "
                + "is exactly the source's natural floor-map composition on positive naturals.",
                DescribeRole.Definition),
            new DocumentBlock.DisplayFormula(Disp(Equal(Call("frac", F.Id("t")),
                Sub(F.Id("t"), new Formula.Floor(F.Id("t")))))),
            Node("fractionalTest", "Every strict source condition", TestFormula(),
                "The function frac is Int.fract: t minus its integer floor. Every division is real "
                + "division. Exponents and i-1 are natural-number operations; i>=2 prevents truncated "
                + "subtraction from changing the source index. Both bounds are strict. The first "
                + "condition and every i from 2 through n are retained, including both endpoints "
                + "of that integer index range.", DescribeRole.Definition),
            Node("claim", "The full positive-natural extension", Disp(Iff(F.Id("claim"), ClaimBody())),
                "Question 1 on printed page 8 asks whether the page-one characterization extends "
                + "below c=(3+sqrt(5))/2. The claim quantifies over every irrational real alpha in "
                + "the full interval (1,c), every natural n>=1, and every positive natural x. "
                + "It asserts the complete equivalence between native iterate-range membership "
                + "and all fractional conditions. The internal split rho, the greatest real root "
                + "of t^4-2t^3-t+1, is included even though the displayed union of open branches omits it. "
                + "The bounded source reading does not decide whether its naturals include zero; "
                + "positivity here is the registered interpretation, not a claimed source convention.",
                DescribeRole.Definition),
            Node("result", "Literal negation of the extension", Disp(new Formula.Not(F.Id("claim"))),
                "Take alpha=sqrt(2), n=3, x=2 and the positive preimage k=2. Existing Mathlib "
                + "theorems supply irrationality, 1<sqrt(2)<3/2<c and its exact square. "
                + "The strict bounds 2<2sqrt(2)<3 give nativeBeatty(sqrt(2),2)=2. "
                + "Function.iterate_fixed therefore gives actual third-iterate membership. "
                + "The fractional parts at indices two and three are 0 and 1/sqrt(2). "
                + "At i=3 the tested expression is 1/sqrt(2), strictly greater than "
                + "1-1/sqrt(2), because 2/sqrt(2)=sqrt(2)>1. Thus the required upper bound fails. "
                + "The result has the literal Lean type Not claim and has no assumed test failure. "
                + "Both the input and iterate witness are 2, so the same counterexample applies "
                + "if the source's naturals also include zero. The polynomial defining rho has "
                + "value -1 at 2 and 25 at 3; continuity gives a root in (2,3), so its greatest "
                + "root exceeds 2. Consequently this witness is in the lower printed branch as well. "
                + "The theorem originally restricted to alpha>c is not refuted. "
                + "The proof shape is bind-only; admission is the named external open-problem "
                + "resolution exception preregistered in issue #29668. Only the designated refutation "
                + "result is a public theorem, so the section 3.9 refutation audit exemption applies.",
                DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role) => Describe.Lean(
            DescribeId.Create("iterated-beatty-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            role == DescribeRole.Theorem ? AssessedProvenance.FromRepo(Source)
                : AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(prose))), role);

    private static Formula A => F.Id("alpha");
    private static Formula N => F.Id("n");
    private static Formula X => F.Id("x");
    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Real() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Frac(Formula f) => Call("frac", f);
    private static Formula Equal(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula LtN(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula LeN(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.And, Par(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Implies, Par(b));
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Iff, Par(b));
    private static Formula For(string name, Formula domain, Formula body) => new Formula.BindMany(
        FormulaQuantifier.ForAll, [new(FormulaIdentifier.Create(name), domain)], body);
    private static Formula Ex(string name, Formula domain, Formula body) => new Formula.BindMany(
        FormulaQuantifier.Exists, [new(FormulaIdentifier.Create(name), domain)], body);

    private static Formula StepFormula() => Disp(For("alpha", Real(), For("k", Nat(),
        Equal(Call("nativeBeatty", A, F.Id("k")), new Formula.Floor(Mul(A, F.Id("k")))))));

    private static Formula RangeFormula()
    {
        var k = F.Id("k");
        var iterate = new Formula.Apply(Pow(Par(Call("nativeBeatty", A)), Seq(OpenBracket, N, CloseBracket)), [k]);
        return Disp(For("alpha", Real(), For("n", Nat(), For("x", Nat(),
            Iff(Call("nativeRange", A, N, X), Ex("k", Nat(), And(LeN(D(1), k), Equal(iterate, X))))))));
    }

    private static Formula TestBody()
    {
        var i = F.Id("i");
        var middle = Sub(Frac(Div(X, Pow(A, i))), Div(Frac(Div(X, Pow(A, Sub(i, D(1))))), A));
        return And(And(LtN(Sub(D(1), Div(D(1), A)), Frac(Div(X, A))), LtN(Frac(Div(X, A)), D(1))),
            For("i", Nat(), Imp(LeN(D(2), i), Imp(LeN(i, N),
                And(LtN(Sub(D(1), Div(D(2), A)), middle), LtN(middle, Sub(D(1), Div(D(1), A))))))));
    }

    private static Formula TestFormula() => Disp(For("alpha", Real(), For("n", Nat(), For("x", Nat(),
        Iff(Call("fractionalTest", A, N, X), TestBody())))));

    private static Formula ClaimBody() => For("alpha", Real(),
        Imp(Call("Irrational", A), Imp(LtN(D(1), A),
            Imp(LtN(A, Div(Add(D(3), Seq(Sqrt, Grp(D(5)))), D(2))),
                For("n", Nat(), Imp(LeN(D(1), N), For("x", Nat(), Imp(LeN(D(1), X),
                    Iff(Call("nativeRange", A, N, X), Call("fractionalTest", A, N, X)))))))));
}
