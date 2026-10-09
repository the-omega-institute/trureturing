using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class KimberlingArrayFirstOccurrenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/KimberlingArrayFirstOccurrence.";

    public DocumentDefinition Create()
    {
        var n = F.Id("n"); var m = F.Id("m"); var i = F.Id("i");
        var j = F.Id("j"); var N = F.Id("N"); var v = F.Id("v");
        var phi = T("goldenRatio"); var psi = T("goldenConj");
        return DocumentDefinition.Create(ScribeNode.Create(
            "The first natural with v occurrences in the golden power array is the Lucas number of index four v minus five.",
            H("First occurrences in Kimberling's array"),
            Blocks(
            Node("a", "Occurrence count", "a",
                Disp(All("N", T("Nat"), Eq(C("a", N), C("card", new Formula.SetBuilder(i, i, Seq(T("Nat"), Comma, Sp, And(And(Le(D(1), i), Le(i, N)), Mem(N, C("row", i))))))))),
                "Count the rows with indices between one and N that contain N. Membership implies that the row index is at most N.", DescribeRole.Definition),
            Node("claim", "First occurrence assertion", "claim",
                Disp(Iff(T("claim"), ClaimFormula())),
                "For every v at least two, the target Lucas number has v occurrences and no smaller positive natural has exactly v occurrences.", DescribeRole.Definition),
            Node("lucas-zero", "Initial Lucas value", "lucas_zero",
                Disp(Eq(C("lucas", D(0)), D(2))),
                "The zeroth Lucas number is two.", DescribeRole.Theorem),
            Node("lucas-succ", "Fibonacci bridge", "lucas_succ",
                Disp(All("n", T("Nat"), Eq(C("lucas", Add(n, D(1))), Add(C("fib", n), C("fib", Add(n, D(2))))))),
                "The integral trace expresses each positive Lucas number as the sum of two Fibonacci numbers.", DescribeRole.Theorem),
            Node("lucas-real", "Real Lucas identity", "lucas_real",
                Disp(All("n", T("Nat"), Eq(C("lucas", n), Add(Pow(phi, n), Pow(psi, n))))),
                "The two conjugate golden powers sum to the Lucas number.", DescribeRole.Theorem),
            Node("lucas-pos", "Positive Lucas numbers", "lucas_pos",
                Disp(All("n", T("Nat"), Lt(D(0), C("lucas", n)))),
                "Every Lucas number is positive.", DescribeRole.Theorem),
            Node("lucas-recur", "Lucas recurrence", "lucas_recur",
                Disp(All("n", T("Nat"), Eq(C("lucas", Add(n, D(2))), Add(C("lucas", Add(n, D(1))), C("lucas", n))))),
                "Lucas numbers satisfy the Fibonacci recurrence.", DescribeRole.Theorem),
            Node("lucas-strict", "Strict increase", "lucas_strict",
                Disp(All("n", T("Nat"), Imp(Le(D(1), n), Lt(C("lucas", n), C("lucas", Add(n, D(1))))))),
                "Lucas numbers strictly increase from index one onward.", DescribeRole.Theorem),
            Node("lucas-mono", "Lucas monotonicity", "lucas_mono",
                Disp(All("n", T("Nat"), All("m", T("Nat"), Imp(Le(D(1), n), Imp(Le(n, m), Le(C("lucas", n), C("lucas", m))))))),
                "Comparison of indices at least one gives comparison of Lucas numbers.", DescribeRole.Theorem),
            Node("lucas-odd-real", "Odd Lucas identity", "lucas_odd_real",
                Disp(All("n", T("Nat"), Imp(C("Odd", n), Eq(C("lucas", n), Sub(Pow(phi, n), Inv(Pow(phi, n))))))),
                "For odd indices the conjugate term is the negative inverse power.", DescribeRole.Theorem),
            Node("lucas-even-real", "Even Lucas identity", "lucas_even_real",
                Disp(All("n", T("Nat"), Imp(C("Even", n), Eq(C("lucas", n), Add(Pow(phi, n), Inv(Pow(phi, n))))))),
                "For even indices the conjugate term is the positive inverse power.", DescribeRole.Theorem),
            Node("inv-one-add-inv-cube-lt-one", "Inverse-power bound", "inv_one_add_inv_cube_lt_one",
                Disp(Lt(Add(Inv(phi), Inv(Pow(phi, D(3)))), D(1))),
                "The inverse first and third golden powers sum to less than one.", DescribeRole.Theorem),
            Node("lucas-mem-own-row", "Own-row membership", "lucas_mem_own_row",
                Disp(All("m", T("Nat"), Imp(C("Odd", m), Imp(Le(D(1), m), Mem(C("lucas", m), C("row", m)))))),
                "At an odd positive index, the first entry of the corresponding row is the Lucas number.", DescribeRole.Theorem),
            Node("lucas-mem-lower-odd-row", "Lower odd rows", "lucas_mem_lower_odd_row",
                Disp(All("m", T("Nat"), All("i", T("Nat"), Imp(C("Odd", m), Imp(Le(D(3), m), Imp(C("Odd", i), Imp(Le(D(1), i), Imp(Lt(Mul(D(2), i), m), Mem(C("lucas", m), C("row", i)))))))))),
                "An odd Lucas number belongs to every positive odd row whose doubled index is smaller than the Lucas index. The multiplier is the Lucas number at the difference of the indices.", DescribeRole.Theorem),
            Node("pair-lower-bound", "Pair lower bound", "pair_lower_bound",
                Disp(All("i", T("Nat"), All("j", T("Nat"), All("N", T("Nat"), Imp(Le(D(1), i), Imp(Lt(i, j), Imp(Mem(N, C("row", i)), Imp(Mem(N, C("row", j)), Le(C("lucas", Add(Mul(D(2), i), D(1))), N))))))))),
                "A common value in two rows is at least the odd Lucas threshold of the lower row. Below that threshold the golden difference has absolute norm one. Even gaps contradict the power threshold; odd gaps place the two multiples on opposite sides of an integer.", DescribeRole.Theorem),
            Node("occurrence-lower-bound", "Threshold for at least v rows", "occurrence_lower_bound",
                Disp(All("N", T("Nat"), All("v", T("Nat"), Imp(Le(D(2), v), Imp(Le(v, C("a", N)), Le(C("lucas", Index(v)), N)))))),
                "Ordered containing rows have gaps at least two. The penultimate one among v rows has index at least twice v minus three, so the pair bound gives the asserted Lucas threshold.", DescribeRole.Theorem),
            Node("lucas-attainment", "Threshold attainment", "lucas_attainment",
                Disp(All("v", T("Nat"), Imp(Le(D(2), v), Eq(C("a", C("lucas", Index(v))), v)))),
                "The rows one, three, through twice v minus three, together with row four v minus five, provide v occurrences. Any additional occurrence would violate the next Lucas threshold.", DescribeRole.Theorem),
            Node("result", "First occurrences", "result",
                Disp(T("claim")),
                "Threshold attainment and the lower bound prove the first-occurrence assertion for every v at least two.", DescribeRole.Theorem, new OpenProblemResolutionClaim(ProblemSlugRef.Create("kimberling-array-first-occurrence-l4v5"), ResolutionKind.Proved))),
            []));
    }

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula formula, string prose, DescribeRole role,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula C(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula T(string name) => new Formula.NamedConstant(FormulaIdentifier.Create(name));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Le(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Lt(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.LessThan, y);
    private static Formula Mem(Formula x, Formula y) => new Formula.Relation(x, FormulaRelationOperator.MemberOf, y);
    private static Formula And(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.And, y);
    private static Formula Imp(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula Iff(Formula x, Formula y) => new Formula.Logic(x, FormulaLogicOperator.Iff, y);
    private static Formula Add(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Add, y);
    private static Formula Sub(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Subtract, y);
    private static Formula Mul(Formula x, Formula y) => new Formula.Binary(x, FormulaBinaryOperator.Multiply, y);
    private static Formula Pow(Formula x, Formula y) => new Formula.Power(x, y);
    private static Formula Inv(Formula x) => C("inv", x);
    private static Formula Index(Formula v) => Sub(Mul(D(4), v), D(5));

    private static Formula ClaimFormula()
    {
        var v = F.Id("v"); var N = F.Id("N");
        var target = C("lucas", Index(v));
        return All("v", T("Nat"), Imp(Le(D(2), v),
            And(Eq(C("a", target), v), All("N", T("Nat"),
                Imp(Le(D(1), N), Imp(Lt(N, target),
                    new Formula.Relation(C("a", N), FormulaRelationOperator.NotEqual, v)))))));
    }
}
