using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class OrderedSubgroupFactorizationDocument : IScribeDocumentDefinition
{
    private static Formula.BoundVariable B(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula All(Formula body, params Formula.BoundVariable[] variables) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
    private static Formula Mem(Formula value, Formula collection) =>
        new Formula.Relation(value, FormulaRelationOperator.MemberOf, collection);
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);
    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Some(Formula body, params Formula.BoundVariable[] variables) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [.. variables], body);
    private static Formula Instances(Formula body, params Formula[] instances)
    {
        var items = new List<Formula>();
        foreach (var instance in instances)
            items.AddRange([OpenBracket, instance, CloseBracket, Comma, Sp]);
        items.Add(body);
        return Seq([.. items]);
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual least-cell producer verifies both fixed-factor products and every finite rejection.",
        H("Ordered subgroup factorization"),
        Blocks(
        Describe.Lean(DescribeId.Create("ordered-subgroup-factorization-correct"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Coding/OrderedSubgroupFactorization.ordered_subgroup_factorization_correct"),
                H("The prescribed factor and every finite rejection"),
                StatementSource.FromAuthor(Disp(NativeClaim())), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The checker input source22_4Input is the actual upper-right source Proposition 22.4 entry 3e+g in N[C2], ordered e before g, with K=C2 and b=2. Its first coefficient mismatch is (e,g), and source22_4Certificate is the actual inspectAndConstruct result in the coefficient-rejection branch. Applying this theorem's rejection soundness proves source22_4FixedFactorQuestion: no p satisfies both prescribed fixed-factor equations. The compiled exact application is validation evidence; no separate certified-instance theorem is introduced. This says nothing about unrestricted SSE, including the source's later two-step construction.")),
                    Paragraph(Text("Let H be any finite group with an independently prescribed total order, and let K be any subgroup with decidable membership. The coefficient ring is the natural numbers. The scalar b may be zero. Write q for the number of actual elements of K, uK for subgroupUniform(K), and uH for groupUniform. No normality, commutativity or multiplication-compatible order is assumed.")),
                    Paragraph(Text("RightConstancy(K,a) means that a(x)=a(h) for every h and every x in hK. BlockBalance(K,a,b) means that, for each actual double coset D=KhK, the sum of a over its distinct least right-coset representatives equals their number times b. FixedSolution(K,a,b) means that some natural group-ring p satisfies a=p uK and b uH=uK p. The first equivalence characterizes exactly this fixed second factor. Under right-coset constancy, the equation uK a=(q b) uH is equivalent to block balance. Together with a uK=q a it gives the second, purely group-ring, existence criterion.")),
                    Paragraph(Text("Every right coset and left coset within one double coset have a nonempty intersection. Left and right subgroup multiplication give bijections between these cells, so their cardinalities agree. Partitioning the original cosets by the actual cells proves that the distinct row and column counts coincide. This converts the original block balance into equality of the original totals supplied to orderedAllocation.")),
                    Paragraph(Text("The row and column sums of blockMass equal the corresponding sums of that same allocation table. Distinct cells have distinct least representatives, because each actual group element belongs to exactly one right coset and one left coset. Different double cosets are disjoint as well. Summing blockMass over the sorted double representatives therefore gives orderedFactor with a=orderedFactor uK and b uH=uK orderedFactor. Coefficient multiplication is reindexed separately on each side; group factors are never exchanged.")),
                    Paragraph(Text("CellCount(K) is the equality between the sum of the lengths of the actual sorted row-by-column lists and the sum of dD squared over all distinct double-coset representatives, where dD is the number of rows. Every zero allocation is included in this count. CoefficientMismatch and BalanceMismatch are the actual two finders firstCoefficientMismatch and firstBalanceMismatch. A returned pair consists of two unequal coefficients in one actual right coset. A returned double representative has a failed original block balance.")),
                    Paragraph(Text("The option constructor some retains its actual pair or double representative, and none is equivalent to the corresponding universal condition. inspectAndConstruct returns inr(p) exactly when p is this orderedFactor and both conditions hold; that returned p satisfies both products and CellCount. If it returns inl(bad), RejectedWitness(bad,K,a,b) records the appropriate actual failed condition, and no fixed-factor solution exists. RejectedWitness uses the pair condition for the inner inl branch and the double-coset condition for the inner inr branch. The rejection concerns only the fixed-uK problem."))),
                DescribeRole.Theorem))));

    private static Formula NativeClaim()
    {
        Formula h = F.Id("H"), k = F.Id("K"), a = F.Id("a"), b = F.Id("b");
        Formula p = F.Id("p"), d = F.Id("d"), pair = F.Id("pair"), bad = F.Id("bad");
        Formula ring = Call("MonoidAlgebra", F.Id("Nat"), h);
        Formula q = Call("subgroupCard", k), uk = Call("subgroupUniform", k);
        Formula uh = Call("groupUniform", h);
        Formula constant = Call("RightConstancy", k, a);
        Formula balanced = Call("BlockBalance", k, a, b);
        Formula factor = Call("orderedFactor", k, a, b);
        Formula solution = Some(And(Equal(a, Mul(p, uk)),
            Equal(Call("smul", b, uh), Mul(uk, p))), B("p", ring));
        Formula second = Equal(Mul(uk, a), Call("smul", Mul(q, b), uh));
        Formula pure = And(Equal(Mul(a, uk), Call("smul", q, a)), second);
        Formula coefficientFinder = Call("firstCoefficientMismatch", k, a);
        Formula balanceFinder = Call("firstBalanceMismatch", k, a, b);
        Formula pairFailure = And(
            Mem(Call("second", pair), Call("sourceRightCoset", k, Call("first", pair))),
            new Formula.Not(Equal(Call("coeff", a, Call("first", pair)),
                Call("coeff", a, Call("second", pair)))));
        Formula balanceFailure = And(Mem(d, Call("doubleRepresentatives", k)),
            new Formula.Not(Equal(Call("sumBlockRows", k, a, d),
                Mul(Call("cardBlockRows", k, d), b))));
        Formula inspected = Call("inspectAndConstruct", k, a, b);
        Formula success = Equal(inspected, Call("inr", p));
        Formula count = Call("CellCount", k);
        Formula outputProducts = And(Equal(a, Mul(p, uk)),
            And(Equal(Call("smul", b, uh), Mul(uk, p)), count));
        Formula body = And(Iff(solution, And(constant, balanced)),
            And(Imp(constant, Iff(second, balanced)),
            And(Iff(solution, pure),
            And(Iff(Equal(coefficientFinder, F.Id("none")), constant),
            And(Iff(Equal(balanceFinder, F.Id("none")), balanced),
            And(All(Imp(Equal(coefficientFinder, Call("some", pair)), pairFailure),
                B("pair", Call("Product", h, h))),
            And(All(Imp(Equal(balanceFinder, Call("some", d)), balanceFailure), B("d", h)),
            And(All(Iff(success, And(Equal(p, factor), And(constant, balanced))), B("p", ring)),
            And(All(Imp(success, outputProducts), B("p", ring)),
                All(Imp(Equal(inspected, Call("inl", bad)),
                    And(Call("RejectedWitness", bad, k, a, b), new Formula.Not(solution))),
                    B("bad", Call("Sum", Call("Product", h, h), h))))))))))));
        return All(Instances(All(Instances(All(body, B("a", ring), B("b", F.Id("Nat"))),
            Call("DecidableMembership", k)), B("K", Call("Subgroup", h))),
            Call("Group", h), Call("Fintype", h), Call("LinearOrder", h)), B("H", F.Id("Type")));
    }
}
