using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros;

internal sealed class NegativeIndexTribonacciAttainmentRefutationDocument
    : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Zeros/NegativeIndexTribonacciAttainmentRefutation.";
    private static LibraryNoteRef Mane => LibraryNoteRef.Create("D5/L/Zeros/mane2026vanishing");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Mane's negative-index root-amplitude attainment fails at k = 3 and n = -15.",
        H("Negative-index tribonacci root-amplitude attainment"),
        Blocks(
            Node("a", "Backward polynomial recurrence", BackwardFormula(),
                "Mane, p. 2, (1.2)–(1.3): “By convention, the initial values are "
                + "𝓕_{n,k}(x) = 1 for n = 1 and 𝓕_{n,k}(x) = 0 for n ∈ [−(k−2), 0].” "
                + "The recurrence is 𝓕_{n,k}(x) = x^{k−1}𝓕_{n−1,k}(x) + "
                + "x^{k−2}𝓕_{n−2,k}(x) + ⋯ + 𝓕_{n−k,k}(x). Here a k m is "
                + "𝓕_{1−m,k}, with integer polynomial coefficients. The index j : Fin(k−1) "
                + "enumerates the source indices j.val+1. Every subtraction between natural "
                + "numbers is truncated subtraction. For k = 0 and m > 0 the value is "
                + "totalized to zero, outside the source's k ≥ 2 range."),
            Node("F", "Source index convention", IndexFormula(),
                "Mane, p. 2, (1.3), iterates the recurrence downwards to negative indices. "
                + "The displayed construction uses a k m = 𝓕_{1−m,k}; thus F k n agrees "
                + "with the source polynomial for n ≤ 1. Int.toNat is the nonnegative "
                + "integer-to-natural conversion. Its totalization beyond n = 1 is unused."),
            Node("zeta", "Maximum nonzero-root amplitude", AmplitudeFormula(),
                "Mane, p. 19: “For k ≥ 2 and n ∈ ℤ, let ζ_{n,k} denote the maximum "
                + "amplitude of |x_root|^k, where P_{n,k}(x_root^k) = 0. Set ζ_{n,k} = 0 "
                + "if 𝓕_{n,k}(x) has no nonzero roots, including vanishing polynomials.” "
                + "The polynomial is mapped from ℤ to ℂ before evaluation; ‖z‖ is the "
                + "complex norm. For a nonzero polynomial the root set is finite, so its "
                + "nonempty amplitude set has a maximum. Real sSup of the empty set is zero. "
                + "For the zero polynomial and k ≥ 2 the amplitude set is unbounded, and "
                + "Real sSup is also zero, matching the vanishing-polynomial convention."),
            Node("claim", "The attainment clause of Conjecture 6.6", ClaimFormula(),
                "Mane, p. 20, Conjecture 6.6: “For fixed k ≥ 3 and n < 0, the upper "
                + "bound is ζ_{n,k} ≤ ⌊|n|/k⌋. The bound is attained whenever r_{n,k} = 1 "
                + "(equivalently n = −sk, where s ≥ 1), i.e. it is a tight bound.” "
                + "The proposition encodes the attainment sentence for every natural k ≥ 3 "
                + "and s ≥ 1, at the integer index −(s*k). The right-hand s is cast to ℝ. "
                + "The universal upper-bound inequality is a separate clause."),
            Describe.Lean(
                DescribeId.Create("result"), DeclarationHandle.Create(Prefix + "result"),
                H("Attainment fails at the nondegenerate tribonacci instance"),
                StatementSource.FromAuthor(Disp(new Formula.Not(F.Id("claim")))),
                AssessedProvenance.FromRepo(Mane),
                Blocks(Paragraph(Text(
                    "At k = 3 and n = −15 the recurrence gives "
                    + "𝓕_{−15,3}(x) = −x(x¹² + 8x⁹ + 18x⁶ + 15x³ + 5). "
                    + "Writing t = x³ gives the quartic t⁴ + 8t³ + 18t² + 15t + 5. "
                    + "The intermediate value theorem supplies a real root −A with 4 < A < 5. "
                    + "Factoring out t+A leaves a monic cubic with positive coefficients "
                    + "b < 4, c < 3 and d < 5/4. The polynomial Cauchy bound puts all its "
                    + "roots strictly inside radius 5. Thus every nonzero root x of the "
                    + "tribonacci polynomial satisfies ‖x‖³ < 5. Its amplitude set is finite "
                    + "and nonempty, so ζ is strictly less than 5. The proposed equality "
                    + "at s = 5 therefore fails. The upper-bound inequality holds at this "
                    + "instance; its general validity is not asserted."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("mane-2026-negative-index-fibonacci-root-amplitude"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create(name is "F" ? "source-index" : name),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromLiterature(Mane),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

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
    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula AtLeast(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.GreaterThanOrEqual, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Power(Formula value, Formula exponent) => new Formula.Power(value, exponent);
    private static Formula Implication(Formula premise, Formula conclusion) =>
        new Formula.Logic(Parenthesized(premise), FormulaLogicOperator.Implies, Parenthesized(conclusion));
    private static Formula IfThenElse(Formula condition, Formula yes, Formula no) => Seq(
        Operatorname, Grp(F.Id("if")), Sp, Parenthesized(condition), Sp,
        Operatorname, Grp(F.Id("then")), Sp, yes, Sp,
        Operatorname, Grp(F.Id("else")), Sp, no);

    private static Formula BackwardFormula()
    {
        Formula k = F.Id("k"), m = F.Id("m"), j = F.Id("j");
        Formula jNext = Add(Call("val", j), D(1));
        Formula sum = Seq(new Formula.Subscript(Sum,
            Seq(j, Colon, Sp, Call("Fin", Subtract(k, D(1))))), Sp,
            Parenthesized(Multiply(Power(F.Id("X"), Subtract(k, jNext)),
                Call("a", k, Add(Subtract(m, k), jNext)))));
        Formula early = new Formula.Logic(Equal(k, D(0)), FormulaLogicOperator.Or, Less(m, k));
        return Disp(All("k", Named("Nat"), All("m", Named("Nat"), Equal(
            Typed(Call("a", k, m), Call("Polynomial", new Formula.Integers())),
            IfThenElse(Equal(m, D(0)), D(1), Parenthesized(IfThenElse(early, D(0),
                Subtract(Call("a", k, Subtract(m, k)), sum))))))));
    }

    private static Formula IndexFormula()
    {
        Formula k = F.Id("k"), n = F.Id("n");
        return Disp(All("k", Named("Nat"), All("n", new Formula.Integers(),
            Equal(Call("F", k, n), Call("a", k, QCall("Int", "toNat", Subtract(D(1), n)))))));
    }

    private static Formula AmplitudeFormula()
    {
        Formula k = F.Id("k"), p = F.Id("p"), z = F.Id("z");
        Formula complex = Named("Complex");
        Formula nonzero = new Formula.Relation(z, FormulaRelationOperator.NotEqual, D(0));
        Formula eval = QCall("Polynomial", "eval", z,
            QCall("Polynomial", "map", QCall("Int", "castRingHom", complex), p));
        Formula roots = Seq(OpenBrace, Sp, z, Colon, Sp, complex, Sp, Mid, Sp,
            Parenthesized(new Formula.Logic(nonzero, FormulaLogicOperator.And, Equal(eval, D(0)))),
            Sp, CloseBrace);
        Formula lambda = Parenthesized(Seq(Operatorname, Grp(F.Id("fun")), Sp,
            Typed(z, complex), Sp, Mapsto, Sp, Power(new Formula.Norm(z), k)));
        return Disp(All("k", Named("Nat"), All("p", Call("Polynomial", new Formula.Integers()),
            Equal(Typed(Call("zeta", k, p), Named("Real")),
                Call("sSup", QCall("Set", "image", lambda, roots))))));
    }

    private static Formula ClaimFormula()
    {
        Formula k = F.Id("k"), s = F.Id("s");
        Formula index = new Formula.Negate(Typed(
            QCall("Nat", "cast", Typed(Multiply(s, k), Named("Nat"))), new Formula.Integers()));
        Formula clause = All("k", Named("Nat"), Implication(AtLeast(k, D(3)),
            All("s", Named("Nat"), Implication(AtLeast(s, D(1)),
                Equal(Call("zeta", k, Call("F", k, index)),
                    Typed(QCall("Nat", "cast", s), Named("Real")))))));
        return Disp(new Formula.Logic(F.Id("claim"), FormulaLogicOperator.Iff, Parenthesized(clause)));
    }
}
