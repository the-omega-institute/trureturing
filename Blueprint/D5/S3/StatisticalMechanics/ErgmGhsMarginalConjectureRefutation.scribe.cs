using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics;

internal sealed class ErgmGhsMarginalConjectureRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/ErgmGhsMarginalConjectureRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/StatisticalMechanics/bianchicolletmagnanini2022ghs");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An edge-triangle Gibbs law has every edge marginal above one half and a positive third Ursell function.",
        H("The marginal criterion does not imply GHS for general exponential random graphs"),
        Blocks(
            Node("hom-density", "homDensity", "Homomorphism density", HomDensityFormula(),
                "For simple graphs h and g on m and n labeled vertices, respectively, homDensity is the number "
                    + "of adjacency-preserving vertex maps from h to g divided by n to the power m. "
                    + "The natural homomorphism count and n are cast to real numbers before division. "
                    + "This is the density in Section 2.1, TeX lines 292–296. The definition also includes n = 0, "
                    + "using total real division, so a zero denominator gives zero.",
                AssessedProvenance.FromLiterature(Source)),
            Node("hamiltonian", "hamiltonian", "The homomorphism-density Hamiltonian", HamiltonianFormula(),
                "A finite family h assigns to each index j a vertex count and a simple graph on that many vertices. "
                    + "The Hamiltonian multiplies the scalar product of the real coefficients β and the corresponding "
                    + "homomorphism densities by the square of the real cast of n. This is Section 2.1, "
                    + "TeX lines 298–308. The definition allows an empty family and coefficients of either sign.",
                AssessedProvenance.FromLiterature(Source)),
            Node("gibbs-weight", "gibbsWeight", "The Gibbs probability of a graph", GibbsWeightFormula(),
                "The probability of a labeled simple graph g is the exponential of its Hamiltonian divided by "
                    + "the sum of these exponentials over all simple graphs on the same vertex set. "
                    + "This is the Gibbs density and partition sum of Section 2.1, TeX lines 300–312.",
                AssessedProvenance.FromLiterature(Source)),
            Node("expectation", "expectation", "Expectation of a graph observable", ExpectationFormula(),
                "For a real observable f on labeled simple graphs, expectation is the scalar product of "
                    + "the Gibbs probabilities and f, hence their finite weighted sum. Section 4, "
                    + "TeX line 1248, uses expectation with respect to this general Gibbs law.",
                AssessedProvenance.FromLiterature(Source)),
            Node("edge-indicator", "edgeIndicator", "The indicator of a possible edge", EdgeIndicatorFormula(),
                "An edge e of the complete graph is an unordered pair of distinct labeled vertices. "
                    + "Its indicator at g is one if that pair belongs to the edge set of g and zero otherwise. "
                    + "The constant function on unordered pairs is written as Function.const, and Subtype.val "
                    + "extracts the unordered pair underlying e. These are the edge coordinates described in "
                    + "Section 2.1, TeX lines 322–333.",
                AssessedProvenance.FromLiterature(Source)),
            Node("u3", "u3", "The third Ursell function", U3Formula(),
                "The third Ursell function is the third joint cumulant of the three edge indicators: "
                    + "the triple moment minus the three products of a marginal and the complementary pair moment, "
                    + "plus twice the product of the marginals. The edges e, f and g may coincide. "
                    + "The formula is given in Section 3, TeX lines 577–589; Definition 3.4, "
                    + "TeX lines 617–636, requires it to be nonpositive for every triple.",
                AssessedProvenance.FromLiterature(Source)),
            Node("claim", "claim", "The universal marginal criterion", ClaimFormula(),
                "For every natural n and every nonempty finite family indexed by Fin (k + 1), "
                    + "the first graph is the complete graph on two vertices. Its coefficient is unrestricted; "
                    + "every coefficient at a nonzero index is nonnegative. Under these hypotheses the proposition "
                    + "asserts that all edge marginals are at least one half if and only if all third Ursell "
                    + "functions are nonpositive, including triples with repeated edges. This states the "
                    + "conjectured equivalence at TeX line 1322 with the general setting of Section 4, "
                    + "TeX lines 1248–1264, made explicit. The quantification includes n = 0 and n = 1, "
                    + "whose complete graphs have no edges.",
                AssessedProvenance.FromRepo(Source)),
            Describe.Lean(
                DescribeId.Create("result"), DeclarationHandle.Create(Prefix + "result"),
                H("Three vertices refute the sufficiency direction"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(Local("claim"))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Take n = 3, k = 1, h(0) = K₂ and h(1) = K₃, with β(0) = 0 and β(1) = log(2)/2. "
                            + "A homomorphism from K₃ to a simple graph on three vertices is injective, "
                            + "because distinct vertices of K₃ are adjacent and a simple graph has no loops. "
                            + "It is therefore surjective. Its image contains every possible edge, so the target "
                            + "must be K₃. The six permutations of its vertices give all such maps to K₃, "
                            + "and there are none to any other target. "
                            + "Substitution into the Hamiltonian gives 3²(log(2)/2)(6/3³) = log(2) "
                            + "at K₃ and zero at each other graph.")),
                    Paragraph(Text(
                        "Encode each graph by the three Boolean choices for the unordered pairs {0,1}, {0,2} "
                            + "and {1,2}. Reading these three adjacencies recovers the choices, and choosing the "
                            + "three adjacencies of an arbitrary graph reconstructs that graph. Thus this is "
                            + "a bijection with the eight Boolean triples; K₃ corresponds exactly to the triple "
                            + "with all entries true. Reindexing the graph sums by this bijection, the "
                            + "exponential weight is two at K₃ and one at the other seven graphs. The partition "
                            + "sum is nine, so their probabilities are 2/9 and 1/9, respectively.")),
                    Paragraph(Text(
                        "Each edge belongs to four graphs, one of which is K₃, so its marginal is "
                            + "(1 + 1 + 1 + 2)/9 = 5/9. Each pair of distinct edges belongs to two graphs, "
                            + "including K₃, so its joint moment is (1 + 2)/9 = 1/3. All three edges occur "
                            + "together only in K₃, giving triple moment 2/9. "
                            + "For the triple consisting of {0,1}, {0,2} and {1,2}, substitution into the "
                            + "third Ursell formula gives 2/9 − 3(5/9)(1/3) + 2(5/9)³ = 7/729.")),
                    Paragraph(Text(
                        "Suppose the universal equivalence holds. The only nonzero index is one, "
                            + "and its coefficient log(2)/2 is nonnegative since log(2) is nonnegative. "
                            + "Every edge marginal is 5/9 ≥ 1/2. Applying the forward implication at "
                            + "n = 3 and k = 1 therefore makes the third Ursell function nonpositive at "
                            + "the three distinct edges. This contradicts 7/729 > 0. Hence the marginal "
                            + "lower bounds do not suffice for GHS in this general family."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("bianchi-collet-magnanini-2022-ergm-ghs-marginal"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Node(string id, string declaration, string title, Formula formula,
        string prose, AssessedProvenance provenance) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance, Blocks(Paragraph(Text(prose))),
            DescribeRole.Definition);

    private static Formula HomDensityFormula() =>
        All("m", Naturals(), All("n", Naturals(), All("h", GraphType(V("m")),
            All("g", GraphType(V("n")), Equal(Typed(Call("homDensity", V("h"), V("g")), Reals()),
                new Formula.Fraction(
                    CastReal(At(Qualified("D5", "S3", "Combinatorics", "ExtremalDensity",
                        "ThreeClassHomomorphismLimit", "homCount"), V("h"), V("g"))),
                    new Formula.Power(Parenthesized(CastReal(V("n"))), V("m"))))))));

    private static Formula HamiltonianFormula() => FamilyBinders(All("g", GraphType(V("n")),
        Equal(Typed(Call("hamiltonian", V("h"), V("β"), V("g")), Reals()),
            Multiply(new Formula.Power(Parenthesized(CastReal(V("n"))), D(2)),
                At(Qualified("dotProduct"), V("β"), LambdaOf("j", FinOf(V("k")),
                    Call("homDensity", At(Qualified("Sigma", "snd"), At(V("h"), V("j"))), V("g"))))))));

    private static Formula GibbsWeightFormula()
    {
        Formula exponential = At(Qualified("Real", "exp"), Call("hamiltonian", V("h"), V("β"), V("g")));
        Formula partitionSum = Seq(Sum, Underscore, Grp(Typed(V("g"), GraphType(V("n")))),
            Sp, Parenthesized(exponential));
        return FamilyBinders(All("g", GraphType(V("n")),
            Equal(Typed(Call("gibbsWeight", V("h"), V("β"), V("g")), Reals()),
                new Formula.Fraction(exponential, partitionSum))));
    }

    private static Formula ExpectationFormula() => FamilyBinders(
        All("f", Arrow(GraphType(V("n")), Reals()),
            Equal(Typed(Call("expectation", V("h"), V("β"), V("f")), Reals()),
                At(Qualified("dotProduct"), Call("gibbsWeight", V("h"), V("β")), V("f")))));

    private static Formula EdgeIndicatorFormula() => All("n", Naturals(),
        All("e", EdgeType(V("n")), All("g", GraphType(V("n")),
            Equal(Typed(Call("edgeIndicator", V("e"), V("g")), Reals()),
                At(Qualified("Set", "indicator"), EdgeSet(V("g")),
                    At(Qualified("Function", "const"), At(Qualified("Sym2"), FinOf(V("n"))), Typed(D(1), Reals())),
                    At(Qualified("Subtype", "val"), V("e")))))));

    private static Formula U3Formula()
    {
        Formula marginalE = Expected(Call("edgeIndicator", V("e")));
        Formula marginalF = Expected(Call("edgeIndicator", V("f")));
        Formula marginalG = Expected(Call("edgeIndicator", V("g")));
        Formula triple = Expected(LambdaOf("a", GraphType(V("n")),
            Multiply(Multiply(IndicatorAt("e"), IndicatorAt("f")), IndicatorAt("g"))));
        Formula pairFG = Expected(LambdaOf("a", GraphType(V("n")), Multiply(IndicatorAt("f"), IndicatorAt("g"))));
        Formula pairEG = Expected(LambdaOf("a", GraphType(V("n")), Multiply(IndicatorAt("e"), IndicatorAt("g"))));
        Formula pairEF = Expected(LambdaOf("a", GraphType(V("n")), Multiply(IndicatorAt("e"), IndicatorAt("f"))));
        Formula body = Add(
            Subtract(Subtract(Subtract(triple, Multiply(marginalE, pairFG)),
                Multiply(marginalF, pairEG)), Multiply(marginalG, pairEF)),
            Multiply(Multiply(Multiply(Typed(D(2), Reals()), marginalE), marginalF), marginalG));
        return FamilyBinders(All("e", EdgeType(V("n")), All("f", EdgeType(V("n")),
            All("g", EdgeType(V("n")),
                Equal(Typed(Call("u3", V("h"), V("β"), V("e"), V("f"), V("g")), Reals()), body)))));
    }

    private static Formula ClaimFormula()
    {
        Formula count = Add(V("k"), D(1));
        Formula firstGraph = Equal(At(V("h"), Typed(D(0), FinOf(count))),
            Typed(Parenthesized(Seq(Typed(D(2), Naturals()), Comma, Sp, Complete(D(2)))), GraphFamily()));
        Formula nonnegative = All("j", FinOf(count),
            Arrow(NotEqual(V("j"), Typed(D(0), FinOf(count))), LE(Typed(D(0), Reals()), At(V("β"), V("j")))));
        Formula marginals = All("e", EdgeType(V("n")),
            LE(Typed(new Formula.Fraction(D(1), D(2)), Reals()), Expected(Call("edgeIndicator", V("e")))));
        Formula ghs = All("e", EdgeType(V("n")), All("f", EdgeType(V("n")), All("g", EdgeType(V("n")),
            LE(Call("u3", V("h"), V("β"), V("e"), V("f"), V("g")), Typed(D(0), Reals())))));
        Formula body = All("n", Naturals(), All("k", Naturals(),
            All("h", Arrow(FinOf(count), GraphFamily()), All("β", Arrow(FinOf(count), Reals()),
                Arrow(firstGraph, Arrow(nonnegative, Equivalence(marginals, ghs)))))));
        return Equivalence(Local("claim"), body);
    }

    private static Formula FamilyBinders(Formula body) => All("n", Naturals(), All("k", Naturals(),
        All("h", Arrow(FinOf(V("k")), GraphFamily()), All("β", Arrow(FinOf(V("k")), Reals()), body))));
    private static Formula GraphFamily() => Seq(Sigma, Sp, Typed(V("m"), Naturals()), Comma, Sp,
        Parenthesized(GraphType(V("m"))));
    private static Formula GraphType(Formula n) => At(Qualified("SimpleGraph"), FinOf(n));
    private static Formula Complete(Formula n) => Typed(Qualified("Top", "top"), GraphType(n));
    private static Formula EdgeSet(Formula g) => At(Qualified("SimpleGraph", "edgeSet"), g);
    private static Formula EdgeType(Formula n) => At(Qualified("Subtype"), EdgeSet(Complete(n)));
    private static Formula FinOf(Formula n) => At(Qualified("Fin"), n);
    private static Formula CastReal(Formula value) => Typed(At(Qualified("Nat", "cast"), value), Reals());
    private static Formula Expected(Formula observable) => Call("expectation", V("h"), V("β"), observable);
    private static Formula IndicatorAt(string edge) => Call("edgeIndicator", V(edge), V("a"));
    private static Formula Local(string name) => Qualified("D5", "S3", "StatisticalMechanics",
        "ErgmGhsMarginalConjectureRefutation", name);
    private static Formula Call(string name, params Formula[] args) => At(Local(name), args);
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula V(string name) => name == "β" ? Beta : F.Id(name);
    private static Formula Qualified(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }

    private static Formula Parenthesized(Formula value) => new Formula.LatexSequence([Open, value, Close]);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(V(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(V(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain));
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula NotEqual(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula LE(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Equivalence(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Multiply(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
}
