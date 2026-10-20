using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Congruence;

internal sealed class KumarPengTranModularComplexityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Congruence/KumarPengTranModularComplexity.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/ArithUnits/kumarpengtran2022complexity");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Three unit bases modulo seventeen have greater inefficiency than base two.",
        H("A cardinal-ranking counterexample for modular integer complexity"),
        Blocks(
            Paragraph(Text(
                "Expressions are arbitrary binary trees with one kind of leaf and two operations, "
                + "addition and multiplication. A recursion over all splits of a leaf budget "
                + "enumerates exactly their possible values. At modulus 17, six leaves suffice "
                + "for every residue in base 2, while bases 1, 3 and 16 each miss a residue at "
                + "that budget. These three distinct unit bases contradict the bound of two "
                + "in the displayed proposition. The comparison counts individual bases; bases "
                + "3 and 16 tie, so the conclusion does not address dense ranking by distinct "
                + "inefficiency values. Exact inefficiencies and minimality are not separate "
                + "theorems of this module.")),
            Node("Expr", "Addition and multiplication expressions", ExprFormula(),
                "Page 1: “An expression refers to a sequence of x’s, which are joined together "
                + "by +, ·, and () in the usual sense.” Expr has one leaf constructor x and "
                + "the two binary constructors add and mul; parentheses specify the tree.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("leaves", "Number of occurrences of x", LeavesFormula(),
                "Page 1 defines complexity as “the smallest number of 1’s needed to write n "
                + "as an equation using addition and multiplication.” Page 28 states “In this "
                + "section, we shall denote the base as s.” Expr.leaves counts one occurrence "
                + "at x and adds the counts at either binary operation.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("eval", "Evaluation at a residue-ring base", EvalFormula(),
                "Page 28: “In this section, we shall denote the base as s.” The leaf x evaluates "
                + "to s in ZMod m; the two binary operations evaluate by ring addition and "
                + "multiplication, with no subtraction or extra constants.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("complexity", "Least expression size", ComplexityFormula(),
                "Page 1: “The complexity of a number n, denoted as ||n|| is equal to the "
                + "smallest number of 1’s needed to write n as an equation using addition and "
                + "multiplication.” Page 28 replaces the base by s. The set contains precisely "
                + "the natural leaf counts of expressions evaluating to r. Its natural sInf "
                + "is the minimum when r is reachable; the proof uses reachability explicitly "
                + "when relating this infimum to a leaf budget.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("inefficiency", "Maximum residue complexity", InefficiencyFormula(),
                "Page 28: “The inefficiency E of an element, which will be used as a base, "
                + "s ∈ ℤ/mℤ is defined as E(m, s) = max(‖0‖, ‖1‖, ‖2‖, …, ‖m − 1‖). "
                + "In other words, the maximum complexity of an element of ℤ/mℤ with x = s.” "
                + "Finset.univ ranges over all residues and Finset.sup takes their maximum.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Conjecture 4.4 with cardinal ranking", ClaimFormula(),
                "Conjecture 4.4, page 29: “E(m, 2) is the third most inefficient for odd m.” "
                + "The proposition quantifies over odd natural m ≥ 3 with NeZero m, and "
                + "counts units s for which inefficiency m 2 < inefficiency m s. It requires "
                + "that count to be at most two. This is the individual-base cardinal "
                + "interpretation of third place. The paper does not specify a tie rule; "
                + "dense ranking by distinct values is outside this proposition. Page 28 "
                + "restricts bases that span the ring by the observation “The representations "
                + "with base s span every element of ℤ/mℤ if and only if s ∈ Uₘ.”",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "Refutation by three strictly larger inefficiencies",
                Disp(Seq(Neg, Sp, Parenthesized(ClaimBody()))),
                "At m = 17, inefficiency 17 2 ≤ 6, whereas inefficiency 17 1, "
                + "inefficiency 17 3 and inefficiency 17 16 are greater than 6. The units "
                + "represented by 1, 3 and 16 form a three-element subset of the filtered "
                + "set. Monotonicity of finite cardinality contradicts its proposed bound.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("kumar-peng-tran-2022-modular-integer-complexity-conjecture-4-4"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Node(string name, string title, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
        DescribeId.Create("kpt44-" + (name == "Expr" ? "expr" : name)), DeclarationHandle.Create(Prefix + name),
        H(title), StatementSource.FromAuthor(formula), provenance,
        Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Q(string owner, string name) => Seq(Named(owner), Dot, Named(name));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula App(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Call(string name, params Formula[] arguments) => App(Named(name), arguments);
    private static Formula Cast(Formula value, Formula type) => Parenthesized(Seq(value, Colon, type));
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Lt(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Logic(Formula left, FormulaLogicOperator op, Formula right) =>
        new Formula.Logic(Parenthesized(left), op, Parenthesized(right));

    private static Formula ExprFormula()
    {
        var e = Named("Expr");
        var binary = new Formula.TypeArrow(e, new Formula.TypeArrow(e, e));
        return Disp(Seq(e, Colon, Named("Type"), Semi, Sp,
            Q("Expr", "x"), Colon, e, Semi, Sp,
            Q("Expr", "add"), Colon, binary, Semi, Sp,
            Q("Expr", "mul"), Colon, binary));
    }

    private static Formula LeavesFormula()
    {
        var e = F.Id("e");
        var f = F.Id("f");
        var leaves = Q("Expr", "leaves");
        var total = Seq(App(leaves, e), Plus, App(leaves, f));
        return Disp(All("e", Named("Expr"), All("f", Named("Expr"),
            Logic(Eq(App(leaves, Q("Expr", "x")), D(1)), FormulaLogicOperator.And,
                Logic(Eq(App(leaves, App(Q("Expr", "add"), e, f)), total),
                    FormulaLogicOperator.And,
                    Eq(App(leaves, App(Q("Expr", "mul"), e, f)), total))))));
    }

    private static Formula EvalFormula()
    {
        var m = F.Id("m");
        var s = F.Id("s");
        var e = F.Id("e");
        var f = F.Id("f");
        var eval = Q("Expr", "eval");
        var leaf = Eq(App(eval, s, Q("Expr", "x")), s);
        var sum = Eq(App(eval, s, App(Q("Expr", "add"), e, f)),
            Seq(App(eval, s, e), Plus, App(eval, s, f)));
        var product = Eq(App(eval, s, App(Q("Expr", "mul"), e, f)),
            Seq(App(eval, s, e), Cdot, App(eval, s, f)));
        return Disp(All("m", Named("Nat"), All("s", Call("ZMod", m),
            All("e", Named("Expr"), All("f", Named("Expr"),
                Logic(leaf, FormulaLogicOperator.And,
                    Logic(sum, FormulaLogicOperator.And, product)))))));
    }

    private static Formula ComplexityFormula()
    {
        var m = F.Id("m");
        var s = F.Id("s");
        var r = F.Id("r");
        var n = F.Id("n");
        var e = F.Id("e");
        var values = Seq(OpenBrace, n, Colon, Named("Nat"), Sp, Mid, Sp,
            Parenthesized(Ex("e", Named("Expr"),
                Logic(Eq(App(Q("Expr", "leaves"), e), n), FormulaLogicOperator.And,
                    Eq(App(Q("Expr", "eval"), s, e), r)))), CloseBrace);
        return Disp(All("m", Named("Nat"), All("s", Call("ZMod", m),
            All("r", Call("ZMod", m), Eq(Call("complexity", s, r), Call("sInf", values))))));
    }

    private static Formula InefficiencyFormula()
    {
        var m = F.Id("m");
        var s = F.Id("s");
        var r = F.Id("r");
        var function = Parenthesized(Seq(Named("fun"), Sp, r, Colon, Call("ZMod", m),
            Sp, Mapsto, Sp, Call("complexity", s, r)));
        var universe = Cast(Q("Finset", "univ"), Call("Finset", Call("ZMod", m)));
        return Disp(All("m", Named("Nat"), Seq(OpenBracket, Call("NeZero", m), CloseBracket,
            Sp, All("s", Call("ZMod", m),
                Eq(Call("inefficiency", m, s), App(Q("Finset", "sup"), universe, function))))));
    }

    private static Formula ClaimBody()
    {
        var m = F.Id("m");
        var s = F.Id("s");
        var units = Call("Units", Call("ZMod", m));
        var comparison = Lt(Call("inefficiency", m, Cast(D(2), Call("ZMod", m))),
            Call("inefficiency", m, Cast(s, Call("ZMod", m))));
        var predicate = Parenthesized(Seq(Named("fun"), Sp, s, Colon, units,
            Sp, Mapsto, Sp, comparison));
        var filtered = App(Q("Finset", "filter"), predicate,
            Cast(Q("Finset", "univ"), Call("Finset", units)));
        return All("m", Named("Nat"), Seq(OpenBracket, Call("NeZero", m), CloseBracket,
            Sp, Logic(Le(D(3), m), FormulaLogicOperator.Implies,
                Logic(Call("Odd", m), FormulaLogicOperator.Implies,
                    Le(App(Q("Finset", "card"), filtered), D(2))))));
    }

    private static Formula ClaimFormula() => Disp(Logic(Named("claim"), FormulaLogicOperator.Iff, ClaimBody()));
}
