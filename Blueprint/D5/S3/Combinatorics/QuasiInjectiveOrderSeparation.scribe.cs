using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics;

internal sealed class QuasiInjectiveOrderSeparationDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/QuasiInjectiveOrderSeparation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/pongsriiam2021quasi");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every order has a function that is quasi-injective just below it and fails at it.",
        H("Separating the Orders of Quasi-Injectivity"),
        Blocks(
            Node("quasi-injective-definition", "Quasi-injectivity of a given order",
                "QuasiInjectiveOfOrder",
                QuasiInjectiveFormula(),
                "Definition 1 of the source reads verbatim: \"We call a function f : N to C a "
                    + "quasi-injective function if for all a, b in N, the condition "
                    + "f(an) = f(bn) for all n in N implies a = b. In addition, if f : N to N "
                    + "and l in N, then we say that f is quasi-injective of order l if f, "
                    + "f(2), f(3), ..., f(l) are quasi-injective, that is, for any a, b, k in "
                    + "N with 1 <= k <= l, if f(k)(an) = f(k)(bn) for all n in N, then "
                    + "a = b.\" Here the superscript denotes the k-fold composite. The source "
                    + "works with the positive integers, so the quantifiers over a, b and n "
                    + "carry positivity. Being quasi-injective of order l implies the same of "
                    + "every smaller order, so the orders form a decreasing chain of "
                    + "conditions.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("separating-family-definition", "The separating family", "g",
                SeparatingFamilyFormula(),
                "For an order m at least two, an odd number 2t+1 with t at least one is given "
                    + "the level t modulo m-1. The function raises the level by one, sends the "
                    + "top level to one, fixes one, and sends an even number 2t to the first "
                    + "level at 2(m-1)t+1. Division and remainder are the natural-number ones. "
                    + "Entering the ladder only through the even numbers is what makes the "
                    + "construction work: multiplying any a by two returns it to the entrance, "
                    + "so no property carried by a alone can trigger the collapse early. A "
                    + "level read from the exponent of two in n instead fails at once, since "
                    + "the pair a = 2 to the m-1 and b = 2 to the m already collapses under a "
                    + "single application.",
                DescribeRole.Definition, AssessedProvenance.FromRepo()),
            Node("question-statement", "The question asked of the orders", "claim",
                ClaimFormula(),
                "Question 17 of the source reads verbatim: \"For each m >= 2, is there a "
                    + "function f : N to N such that f is quasi-injective of order m - 1 but "
                    + "not of order m?\" The statement displayed here is the affirmative "
                    + "reading, quantified over every order m at least two. The source proves "
                    + "that the divisor-counting function and the Jordan totient functions are "
                    + "quasi-injective of every order, and that the divisor-power sums are "
                    + "quasi-injective of order two, so no function it studies separates two "
                    + "consecutive orders.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("orders-separated", "Consecutive orders are separated", "result",
                ResultFormula(),
                "The answer is yes, witnessed by the family above. Two facts drive it. First, "
                    + "for every k between one and m-1 and every t at least one, the k-fold "
                    + "composite sends 2t to 2((m-1)t + k - 1) + 1: the first step lands in "
                    + "level zero of the ladder and each later step raises the level by one, "
                    + "and level k-1 is below the top level whenever k is at most m-1, so the "
                    + "collapse is never reached. That value is strictly increasing in t, so "
                    + "taking n equal to two separates any two distinct a and b, which is "
                    + "quasi-injectivity of order m-1. Second, the m-fold composite is "
                    + "constantly one: an even number needs one step to enter the ladder, "
                    + "m-2 steps to climb it and one more to collapse, an odd number at level "
                    + "j needs m-j steps, and one is fixed. Hence the m-fold composite agrees "
                    + "on the multiples of one and of two while one and two differ, so "
                    + "quasi-injectivity of order m fails.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("quasi-injective-order-separation"),
                    ResolutionKind.Proved))),
        []));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.FromAuthor(formula),
            provenance,
            Blocks(Paragraph(Text(prose))),
            role,
            resolution);

    private static Formula QuasiInjectiveFormula()
    {
        Formula f = F.Id("f"), l = F.Id("l"), k = F.Id("k");
        Formula a = F.Id("a"), b = F.Id("b"), n = F.Id("n");
        Formula agree = Universal("n", Naturals(),
            Implies(LessEqual(D(1), n),
                Equal(Iterate(f, k, Multiply(a, n)), Iterate(f, k, Multiply(b, n)))));
        Formula body = Universal("k", Naturals(),
            Implies(LessEqual(D(1), k),
                Implies(LessEqual(k, l),
                    Universal("a", Naturals(),
                        Universal("b", Naturals(),
                            Implies(LessEqual(D(1), a),
                                Implies(LessEqual(D(1), b),
                                    Implies(agree, Equal(a, b)))))))));
        return Disp(Universal("f", Functions(),
            Universal("l", Naturals(),
                Iff(Call("QuasiInjectiveOfOrder", f, l), body))));
    }

    private static Formula SeparatingFamilyFormula()
    {
        Formula m = F.Id("m"), n = F.Id("n");
        Formula value = Call("g", m, n);
        Formula half = Call("div", n, D(2));
        Formula level = Call("mod", Call("div", Subtract(n, D(1)), D(2)), Subtract(m, D(1)));
        Formula top = Call("mod", Subtract(m, D(2)), Subtract(m, D(1)));
        Formula caseOne = Implies(Equal(n, D(1)), Equal(value, D(1)));
        Formula caseEven = Implies(
            And(NotEqual(n, D(1)), Equal(Call("mod", n, D(2)), D(0))),
            Equal(value, Add(Multiply(Multiply(D(2), Subtract(m, D(1))), half), D(1))));
        Formula caseTop = Implies(
            And(NotEqual(n, D(1)),
                And(Equal(Call("mod", n, D(2)), D(1)), Equal(level, top))),
            Equal(value, D(1)));
        Formula caseClimb = Implies(
            And(NotEqual(n, D(1)),
                And(Equal(Call("mod", n, D(2)), D(1)), NotEqual(level, top))),
            Equal(value, Add(n, D(2))));
        return Disp(Universal("m", Naturals(),
            Universal("n", Naturals(),
                Seq(caseOne, Sp, Sp, Sp, caseEven, Nl,
                    caseTop, Sp, Sp, Sp, caseClimb))));
    }

    private static Formula ClaimFormula()
    {
        Formula m = F.Id("m"), f = F.Id("f"), n = F.Id("n");
        Formula positive = Universal("n", Naturals(),
            Implies(LessEqual(D(1), n), LessEqual(D(1), Call("f", n))));
        Formula holds = Call("QuasiInjectiveOfOrder", f, Subtract(m, D(1)));
        Formula fails = Negated(Call("QuasiInjectiveOfOrder", f, m));
        Formula body = Universal("m", Naturals(),
            Implies(LessEqual(D(2), m),
                Exists("f", Functions(), And(positive, And(holds, fails)))));
        return Disp(Iff(F.Id("claim"), body));
    }

    private static Formula ResultFormula() => Disp(F.Id("claim"));

    private static Formula Iterate(Formula f, Formula k, Formula x) =>
        Seq(f, Caret, Grp(Open, k, Close), Open, x, Close);

    private static Formula Naturals() =>
        new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));

    private static Formula Functions() =>
        Seq(Naturals(), Sp, To, Sp, Naturals());

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Negated(Formula value) =>
        new Formula.Not(Parenthesized(value));

    private static Formula Universal(string name, Formula domain, Formula body) =>
        new Formula.Bind(
            FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);

    private static Formula Exists(string name, Formula domain, Formula body) =>
        new Formula.Bind(
            FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula LessEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(
            Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
}
