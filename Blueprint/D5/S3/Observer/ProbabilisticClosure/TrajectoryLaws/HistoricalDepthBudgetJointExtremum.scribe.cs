using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws;

internal sealed class HistoricalDepthBudgetJointExtremumDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One iid law and one infinite greedy code attain the full-history depth-budget joint extremum.",
        H("Historical Processes and Depth-Budget Joint Extrema"),
        Blocks(
            Paragraph(Text(
                "Let A be the actual finite alphabet, with at least two letters and the full discrete "
                + "measurable structure. The real parameter delta is positive and at most the reciprocal "
                + "of the number of letters. Every row q(v,a), including the empty-history row, is "
                + "normalized and bounded below by delta. Histories are complete finite words. No "
                + "stationarity, finite memory, computability, rationality or summable-tail assumption "
                + "is imposed. The function b gives arbitrary natural budgets at every depth.")),
            Paragraph(Text(
                "NormalizedRows(q) means that all row entries are nonnegative and each row sums to one. "
                + "For a proof h of this property, mu(q,h) denotes trajectoryLaw(q,h): its initial law "
                + "is the row at the empty history; after coordinates zero through n, its successor "
                + "kernel is the row at precisely that observed prefix of length n plus one. "
                + "The cylinder C(w) fixes coordinates zero through length(w) minus one, so C of the "
                + "empty word is the whole trajectory space. U(F) denotes deletedSet(F), the union "
                + "of these cylinders. trunc(F,N) is the set of words in F of length at most N.")),
            Paragraph(Text(
                "Legal(b,F) requires prefix freedom, excludes the empty word and bounds the number "
                + "of distinct words of each length n by b(n). Fix any distinguished actual letter a "
                + "with subscript zero. extremalVector(delta,a) assigns delta to every other letter "
                + "and one minus the number of other letters times delta to that letter. In the "
                + "formula, p is this vector and G is the one infinite greedyCode with mass priority "
                + "and the prescribed tie order at each depth. truncatedMass is the finite word-mass "
                + "sum through the given horizon, and codeMass is the total word-mass sum in the "
                + "extended nonnegative reals. Lambda notation denotes a function, and const(B,z) "
                + "is the standard constant function on B with value z.")),
            Paragraph(Text(
                "historicalGap(delta,b) is one minus the supremum of the real deletion masses over "
                + "all such rows and all legal codes. IsGreatest asserts both membership and an "
                + "upper bound for every member of the displayed set. Both greatest-value clauses "
                + "use actual measures; the real clause also supplies the probability-bounded "
                + "conversion needed for the gap identity.")),
            Describe.Lean(
                DescribeId.Create("historical-depth-budget-joint-extremum"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/HistoricalDepthBudgetJointExtremum.historical_depth_budget_joint_extremum"),
                H("One law and one code attain all horizons and the joint supremum"),
                StatementSource.FromAuthor(MainFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a fixed finite code, backward induction assigns payoff one to a selected "
                        + "node before testing the terminal depth, and zero to an unselected terminal "
                        + "node. A row with entries at least delta is bounded by putting its entire "
                        + "surplus on one child of maximal continuation value. These choices define "
                        + "one total heavy-child function on histories and lawful rows everywhere.")),
                    Paragraph(Text(
                        "At each original node, swap its heavy child with the distinguished letter. "
                        + "Recursive transport is a bijection at every depth and preserves prefixes "
                        + "in both directions. Its inverse first recovers the original prefix and then "
                        + "uses that original node's inverse swap. Consequently every depth budget "
                        + "is preserved and every live path product becomes exactly the iid product "
                        + "of its transported word. Finite iid optimality bounds the transported code.")),
                    Paragraph(Text(
                        "The full-history trajectory calculation includes the empty cylinder and "
                        + "the initial letter without a dummy coordinate. Prefix-free cylinders are "
                        + "measurable and pairwise disjoint. Nonnegative finite sums and increasing "
                        + "unions connect finite comparison to the actual infinite deletion event. "
                        + "Finite optimizing rows and swaps may depend on the code and the horizon; "
                        + "no coherent limit of these choices is needed. Infinite attainment uses "
                        + "the fixed iid row and the same G for every horizon and for total mass.")),
                    Paragraph(Text(
                        "Zero budgets, skipped depths, exhaustion, empty codes and horizon zero are "
                        + "included. At the uniform endpoint the surplus is zero, with no division "
                        + "by surplus and no unique-heavy-child requirement. Label-dependent code "
                        + "restrictions would require a separate invariance condition. This joint "
                        + "optimization does not assert greedy optimality for a fixed historical law."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(
            GidRef.Create("D5/S0/Computability/Coding/DepthBudgetIidGreedyOptimality"))]));

    private static Formula MainFormula()
    {
        Formula aType = F.Id("A"), a = Seq(F.Id("a"), Underscore, D(0));
        Formula delta = DeltaLower, b = F.Id("b"), tie = F.Id("tie");
        Formula p = F.Id("p"), g = F.Id("G"), q = F.Id("q"), h = F.Id("h");
        Formula code = F.Id("F"), n = F.Id("N"), w = F.Id("w"), i = F.Id("i");
        Formula nat = Call("Nat"), real = Call("Real"), enn = Call("ENNReal");
        Formula list = Call("List", aType), codes = Call("Set", list);
        Formula rows = Seq(list, Sp, To, Sp, aType, Sp, To, Sp, real);
        Formula law = Call("trajectoryLaw", q, h);
        Formula wordProduct = Seq(Prod, Underscore, Grp(i, Colon, Call("Fin", Call("length", w))), Sp,
            Call("apply", q, Call("take", w, Call("val", i)), Call("get", w, i)));
        Formula cylinderLaw = All(w, list,
            Equal(Call("apply", law, Call("wordCylinder", w)), Call("ofReal", wordProduct)));
        Formula allLaws = All(q, rows, All(h, Call("NormalizedRows", q),
            And(Call("IsProbabilityMeasure", law), cylinderLaw)));
        Formula finite = All(q, rows, All(h, Call("NormalizedRows", q),
            Imply(Lower(q, delta, aType), All(code, codes,
                Imply(Call("Legal", b, code), All(n, nat,
                    Seq(Call("apply", law, Call("deletedSet", Truncate(code, n, list))), Sp, Leq, Sp,
                        Call("ofReal", Call("truncatedMass", p, g, n)))))))));
        Formula iid = Call("const", list, p);
        Formula iidLaw = Call("trajectoryLaw", iid, h);
        Formula finiteAttainment = All(n, nat, Equal(
            Call("apply", iidLaw, Call("deletedSet", Truncate(g, n, list))),
            Call("ofReal", Call("truncatedMass", p, g, n))));
        Formula totalAttainment = Equal(Call("apply", iidLaw, Call("deletedSet", g)), Call("codeMass", p, g));
        Formula joint = Call("IsGreatest", JointSet(aType, rows, codes, delta, b, enn, false),
            Call("codeMass", p, g));
        Formula realJoint = Call("IsGreatest", JointSet(aType, rows, codes, delta, b, real, true),
            Call("toReal", Call("codeMass", p, g)));
        Formula gap = Equal(Call("historicalGap", delta, b),
            Seq(D(1), Sp, Minus, Sp, Call("toReal", Call("codeMass", p, g))));
        Formula attained = Some(h, Call("NormalizedRows", iid), And(
            Lower(iid, delta, aType), finiteAttainment, totalAttainment, joint, realJoint, gap));
        Formula clauses = And(Call("Legal", b, g), allLaws, finite, attained);
        Formula order = Seq(LambdaLower, Sp, F.Id("n"), Colon, nat, Sp, Mapsto, Sp,
            Call("priority", p, Call("tie", F.Id("n"))));
        Formula withDefinitions = Let(p, Call("extremalVector", delta, a),
            Let(g, Call("greedyCode", order, b), clauses));
        Formula assumptions = And(Seq(D(0), Sp, Lt, Sp, delta),
            Seq(D(2), Sp, Leq, Sp, Call("card", aType)),
            Seq(delta, Sp, Leq, Sp, Frac, Grp(D(1)), Grp(Call("card", aType))));
        Formula body = All(a, aType, All(delta, real, All(b, Seq(nat, Sp, To, Sp, nat),
            All(tie, Seq(nat, Sp, To, Sp, Call("LinearOrder", list)),
                Imply(assumptions, withDefinitions)))));
        return Disp(All(aType, Call("Type"), Seq(
            OpenBracket, Call("Fintype", aType), CloseBracket, Sp,
            OpenBracket, Call("DecidableEq", aType), CloseBracket, Sp,
            OpenBracket, Call("MeasurableSpace", aType), CloseBracket, Sp,
            OpenBracket, Call("MeasurableSingletonClass", aType), CloseBracket, Sp, body)));
    }

    private static Formula JointSet(Formula aType, Formula rows, Formula codes,
        Formula delta, Formula b, Formula type, bool realMass)
    {
        Formula q = F.Id("q"), h = F.Id("h"), code = F.Id("F"), x = F.Id("x");
        Formula mass = Call("apply", Call("trajectoryLaw", q, h), Call("deletedSet", code));
        if (realMass) mass = Call("toReal", mass);
        return Seq(OpenBrace, x, Colon, type, Sp, Mid, Sp,
            Some(q, rows, Some(h, Call("NormalizedRows", q), And(Lower(q, delta, aType),
                Some(code, codes, And(Call("Legal", b, code), Equal(x, mass)))))), CloseBrace);
    }

    private static Formula Lower(Formula q, Formula delta, Formula aType) =>
        All(F.Id("v"), Call("List", aType), All(F.Id("z"), aType,
            Seq(delta, Sp, Leq, Sp, Call("apply", q, F.Id("v"), F.Id("z")))));
    private static Formula Truncate(Formula code, Formula n, Formula list)
    {
        Formula w = F.Id("w");
        return Seq(OpenBrace, w, Colon, list, Sp, Mid, Sp,
            And(Seq(w, Sp, InMacro, Sp, code), Seq(Call("length", w), Sp, Leq, Sp, n)), CloseBrace);
    }
    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, Open, variable, Colon, type, Close, Comma, Sp, body);
    private static Formula Some(Formula variable, Formula type, Formula body) =>
        Seq(Exists, Sp, Open, variable, Colon, type, Close, Comma, Sp, body);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Imply(Formula left, Formula right) =>
        Seq(Open, left, Close, Sp, Rightarrow, Sp, Open, right, Close);
    private static Formula Let(Formula variable, Formula value, Formula body) =>
        Seq(Operatorname, Grp(F.Id("let")), Sp, variable, Colon, Eq, Sp, value, Comma, Sp, body);
    private static Formula And(params Formula[] items)
    {
        var joined = new List<Formula>();
        for (int index = 0; index < items.Length; index++)
        {
            if (index > 0) joined.AddRange([Sp, Land, Sp]);
            joined.AddRange([Open, items[index], Close]);
        }
        return Seq([.. joined]);
    }
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}
