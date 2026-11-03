using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Congruence;

internal sealed class ZhangLComplexityEventualStabilityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Congruence/ZhangLComplexityEventualStability.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithUnits/zhang2024lcomplexity");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every positive-multiple orbit reaches permanent linear l-complexity growth.",
        H("Eventual stability of l-complexity"),
        Blocks(
            Paragraph(Text(
                "Expressions have one leaf value l and internal operations addition and multiplication. "
                + "For l > 1, an expression with s leaves has value at most l raised to s. "
                + "Multiplying an expression by one additional leaf increases its size by one. "
                + "Consequently the l-complexity of l^m * n minus m is a nonincreasing positive integer "
                + "sequence. The antitone chain condition makes this sequence eventually constant. "
                + "The lower bound permits cancellation of natural subtraction and gives permanent "
                + "linear growth from a suitable point in every orbit. This is the discrete-defect "
                + "stabilization method used by Altman and Zelinsky for ordinary integer complexity; "
                + "the expression bound here applies to every natural l > 1.")),
            Node("value", "Natural expression value", ValueFormula(),
                "An expression is evaluated in Nat by assigning l to each leaf and using addition "
                + "and multiplication at the corresponding internal nodes. Expr denotes "
                + "KumarPengTranModularComplexity.Expr.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("complexity", "Natural l-complexity", ComplexityFormula(),
                "Page 2: “Given a positive integer n ∈ lZ⁺, define the l-complexity of n, denoted "
                + "as ‖n‖_l, as the minimal number of l’s that are needed to express n in terms of l "
                + "using only addition and multiplication (and parentheses).” Complexity is the "
                + "natural sInf of attainable leaf counts. Expr.leaves counts the leaves; value l e "
                + "evaluates e in Nat. For a positive multiple of l, the set of leaf counts is nonempty.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("A", "Numbers with permanent linear growth", AFormula(),
                "Question 3, page 10: “Let l > 1 and define A_l := {n ∈ lZ⁺ : ‖l^m · n‖_l = "
                + "m + ‖n‖_l for all m ≥ 0}.” In Nat, membership in lZ⁺ means 0 < n and l ∣ n. "
                + "The variable m ranges over all natural numbers, including zero. "
                + "Page 2: “Given a positive integer n ∈ lZ⁺, define the l-complexity of n, denoted "
                + "as ‖n‖_l, as the minimal number of l’s that are needed to express n in terms of l "
                + "using only addition and multiplication (and parentheses).” The value function "
                + "is structural recursion on Expr, with leaf l and operations Nat.add and Nat.mul. "
                + "The complexity function is the natural sInf of the attainable leaf counts. "
                + "Expr denotes KumarPengTranModularComplexity.Expr; Expr.leaves counts the leaves.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Every orbit reaches A", Disp(
                    Logic(Named("claim"), FormulaLogicOperator.Iff, ClaimBody())),
                "Question 3, page 10: “Can one say anything about the set A_l? For example, is it "
                + "true that for every n ∈ lZ⁺, there exists m₀ ≥ 0 such that l^{m₀} · n ∈ A_l?” "
                + "Together with the preceding sentence “Let l > 1 and define A_l := {n ∈ lZ⁺ : "
                + "‖l^m · n‖_l = m + ‖n‖_l for all m ≥ 0}.” The variables l, n and m0 are "
                + "natural numbers; m0 denotes the source's m₀. Positivity and divisibility express "
                + "n ∈ lZ⁺. This proposition is the every-orbit assertion in Question 3.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Eventual stability on every positive-multiple orbit", Disp(ClaimBody()),
                "Every positive multiple n of every natural l > 1 has a translate l^m0 * n in A l. "
                + "The exponential bound on expression values gives l-complexity of l^m * n at least m + 1. "
                + "The one-leaf extension makes the corresponding natural defect nonincreasing. "
                + "After the defect becomes constant, cancellation yields the equality required by A. "
                + "No bound on the first such m0 or complete description of A l is asserted.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("zhang-2024-l-complexity-question-3"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolutionClaim = null) => Describe.Lean(
        DescribeId.Create("zhang-l-complexity-" + (name == "A" ? "a" : name)), DeclarationHandle.Create(Prefix + name),
        H(title), StatementSource.FromAuthor(formula), provenance,
        Blocks(Paragraph(Text(prose))), role, resolutionClaim);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Q(string owner, string name) => Seq(Named(owner), Dot, Named(name));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula App(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Call(string name, params Formula[] arguments) => App(Named(name), arguments);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Lt(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Logic(Formula left, FormulaLogicOperator op, Formula right) =>
        new Formula.Logic(Parenthesized(left), op, Parenthesized(right));

    private static Formula ValueFormula()
    {
        var l = F.Id("l");
        var e = F.Id("e");
        var f = F.Id("f");
        var expr = Named("Expr");
        var addition = All("e", expr, All("f", expr,
            Eq(Call("value", l, App(Q("Expr", "add"), e, f)),
                Seq(Call("value", l, e), Plus, Call("value", l, f)))));
        var multiplication = All("e", expr, All("f", expr,
            Eq(Call("value", l, App(Q("Expr", "mul"), e, f)),
                Seq(Call("value", l, e), Cdot, Sp, Call("value", l, f)))));
        return Disp(All("l", Named("Nat"), Logic(Eq(Call("value", l, Q("Expr", "x")), l),
            FormulaLogicOperator.And,
            Logic(addition, FormulaLogicOperator.And, multiplication))));
    }

    private static Formula ComplexityFormula()
    {
        var l = F.Id("l");
        var n = F.Id("n");
        var k = F.Id("k");
        var e = F.Id("e");
        var expr = Named("Expr");
        var nat = Named("Nat");
        var sizes = Seq(OpenBrace, k, Colon, nat, Mid, Sp,
            Ex("e", expr, Logic(Eq(App(Q("Expr", "leaves"), e), k),
                FormulaLogicOperator.And, Eq(Call("value", l, e), n))), CloseBrace);
        return Disp(All("l", nat, All("n", nat,
            Eq(Call("complexity", l, n), Call("sInf", sizes)))));
    }

    private static Formula AFormula()
    {
        var l = F.Id("l");
        var n = F.Id("n");
        var m = F.Id("m");
        var nat = Named("Nat");
        var growth = All("m", nat, Eq(
            Call("complexity", l, Seq(new Formula.Power(l, m), Cdot, Sp, n)),
            Seq(m, Plus, Call("complexity", l, n))));
        var members = Seq(OpenBrace, n, Colon, nat, Mid, Sp,
            Logic(Lt(D(0), n), FormulaLogicOperator.And,
                Logic(new Formula.Relation(l, FormulaRelationOperator.Divides, n),
                    FormulaLogicOperator.And, growth)), CloseBrace);
        return Disp(All("l", nat, Eq(Call("A", l), members)));
    }

    private static Formula ClaimBody()
    {
        var l = F.Id("l");
        var n = F.Id("n");
        var m0 = F.Id("m0");
        var conclusion = Ex("m0", Named("Nat"),
            Seq(new Formula.Power(l, m0), Cdot, Sp, n, InMacro, Sp, Call("A", l)));
        return All("l", Named("Nat"), Logic(Lt(D(1), l), FormulaLogicOperator.Implies,
            All("n", Named("Nat"), Logic(Lt(D(0), n), FormulaLogicOperator.Implies,
                Logic(new Formula.Relation(l, FormulaRelationOperator.Divides, n),
                    FormulaLogicOperator.Implies, conclusion)))));
    }
}
