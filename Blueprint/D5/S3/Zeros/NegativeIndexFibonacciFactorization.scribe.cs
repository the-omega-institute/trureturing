using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros;

internal sealed class NegativeIndexFibonacciFactorizationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Zeros/NegativeIndexFibonacciFactorization.";
    private static LibraryNoteRef Mane => LibraryNoteRef.Create("D5/L/Zeros/mane2026vanishing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Mane's negative-index factorization holds for all k >= 2 and 2 <= s <= k+1.",
        H("Negative-index generalized Fibonacci factorization"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("claim"), DeclarationHandle.Create(Prefix + "claim"),
                H("Conjecture 6.4"), StatementSource.FromAuthor(ClaimFormula()),
                AssessedProvenance.FromLiterature(Mane),
                Blocks(Paragraph(Text(
                    "Mane, p. 19, Section 6: “Conjecture 6.4. Numerical calculations and "
                    + "symbolic manipulations yield the following. For k ≥ 2 and n = −sk, "
                    + "where s ∈ [2, k + 1] (the pattern fails for s ≥ k + 2), "
                    + "𝓕_{−sk,k}(x) = −x(x^k + 1)^{s−2}(x^k + s). (6.4) "
                    + "Hence 𝓕_{−sk,k}(x) has roots x^k = −s. The case s = 2 was derived "
                    + "in the enumerated list following eq. (3.2).” "
                    + "Here k and s are natural numbers; the negative index is the integer "
                    + "negative of their natural product. F is the polynomial in ℤ[X] defined "
                    + "in NegativeIndexTribonacciAttainmentRefutation, with F k n = "
                    + "a k (1−n).toNat and a k m = 𝓕_{1−m,k}. The initial values and "
                    + "backward recurrence are those of (1.2)–(1.3). X is the polynomial "
                    + "indeterminate, C is Polynomial.C, and the coefficient s is cast to ℤ. "
                    + "The exponent s−2 uses natural truncated subtraction; 2 ≤ s makes it "
                    + "the ordinary nonnegative difference. The formula encodes the identity "
                    + "throughout the stated range; the neighbouring root and failure "
                    + "sentences describe its consequences and boundary."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("result"), DeclarationHandle.Create(Prefix + "result"),
                H("The factorization holds throughout the conjectured range"),
                StatementSource.FromAuthor(Disp(F.Id("claim"))),
                AssessedProvenance.FromRepo(Mane),
                Blocks(Paragraph(Text(
                    "For the backward sequence, the generating function is "
                    + "(1−X^k z^k)/(1−(1+X^k)z^k+Xz^{k+1}). A finite geometric sum "
                    + "computes its coefficient at z^{sk+1}, because the omitted tail starts "
                    + "in degree k(s+1). The r-th summand has degrees between kr and "
                    + "(k+1)r. With s ≤ k+1, only r=s contributes to degree sk+1, and "
                    + "only r=s−1 contributes to degree (s−1)k+1. Subtracting X^k times "
                    + "the second coefficient from the first gives the displayed "
                    + "factorization for every permitted k and s."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("mane-2026-negative-index-fibonacci-factorization"),
                    ResolutionKind.Proved)))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(F.Id(owner)), Dot, Operatorname, Grp(F.Id(name)));
    private static Formula QCall(string owner, string name, params Formula[] args) =>
        new Formula.Apply(Qualified(owner, name), [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) =>
        Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create(name), type)], body);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula AtMost(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Power(Formula value, Formula exponent) => new Formula.Power(value, exponent);
    private static Formula Implication(Formula premise, Formula conclusion) =>
        new Formula.Logic(Parenthesized(premise), FormulaLogicOperator.Implies,
            Parenthesized(conclusion));

    private static Formula ClaimFormula()
    {
        Formula k = F.Id("k"), s = F.Id("s"), x = F.Id("X");
        Formula integerS = Typed(QCall("Nat", "cast", s), new Formula.Integers());
        Formula index = new Formula.Negate(Typed(
            QCall("Nat", "cast", Typed(Multiply(s, k), Named("Nat"))), new Formula.Integers()));
        Formula rhs = Multiply(Multiply(new Formula.Negate(x),
            Power(Parenthesized(Add(Power(x, k), D(1))), Subtract(s, D(2)))),
            Parenthesized(Add(Power(x, k), Call("C", integerS))));
        Formula clause = All("k", Named("Nat"), Implication(AtMost(D(2), k),
            All("s", Named("Nat"), Implication(AtMost(D(2), s),
                Implication(AtMost(s, Add(k, D(1))), Equal(Call("F", k, index), rhs))))));
        return Disp(new Formula.Logic(F.Id("claim"), FormulaLogicOperator.Iff,
            Parenthesized(clause)));
    }
}
