using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics;

internal sealed class GranularCellOrderSteadyStateRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/GranularCellOrderSteadyStateRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/StatisticalMechanics/myhill2023granularsteadystates");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Strictly positive merging and splitting rates admit two distinct positive normalized stationary cell-order distributions at C = 10.",
        H("Granular cell-order steady states need not be unique"), Blocks(
            Paragraph(Text(
                "Cell orders are natural numbers from 3 through C. The real-valued function Q "
                    + "gives their fractions, and p and q give the constant merging and splitting rates. "
                    + "Rates are evaluated at the smaller and larger input orders, respectively. "
                    + "All index subtraction is natural-number subtraction, truncated at zero. "
                    + "Only values of Q on the interval from 3 through C enter physicality and the equality conclusion.")),
            Node("J", "The merging and splitting channels", ChannelsFormula(),
                "A channel consists of two input orders i and j with 3 <= i <= j <= C and product order i + j - 2 <= C. Finset.product forms the Cartesian product of the two intervals; Finset.filter selects these channels.",
                AssessedProvenance.FromLiterature(Source)),
            Node("delta", "The Kronecker delta", DeltaFormula(),
                "The counting factors in equations (1) and (2) use the Kronecker delta, equal to one for equal orders and zero otherwise.",
                AssessedProvenance.FromRepo(Source)),
            Node("flux", "The net channel flux", FluxFormula(),
                "Section I.A defines the net flux as the merging rate times the two input fractions, minus the splitting rate times the product-cell fraction. The min and max arguments let both orders of the input pair use the same channel rates.",
                AssessedProvenance.FromLiterature(Source)),
            Node("rhs", "The evolution of a cell-order fraction", RhsFormula(),
                "This is equation (1) read with the net flux of Section I.A. The first sum creates k-cells, the second removes them, and the last term accounts for the changing total number of cells. The factor one half and the delta factors count equal input orders correctly. The printed loss term's splitting factor is read as the product-cell fraction Q_i, as in equation (2).",
                AssessedProvenance.FromLiterature(Source)),
            Node("PositiveRates", "Strictly positive channel rates", PositiveRatesFormula(),
                "Both the merging rate and the splitting rate are strictly positive on every channel in J C. Values of the rate functions outside these channels are unrestricted.",
                AssessedProvenance.FromLiterature(Source)),
            Node("Physical", "Positive normalized cell fractions", PhysicalFormula(),
                "A physical state has a strictly positive real fraction at each order from 3 through C, and these fractions sum to one. Values outside that interval are unrestricted.",
                AssessedProvenance.FromLiterature(Source)),
            Node("Stationary", "Vanishing evolution at every cell order", StationaryFormula(),
                "A stationary state makes the full right-hand side vanish at every order from 3 through C. No separate condition on individual fluxes or their total is imposed.",
                AssessedProvenance.FromLiterature(Source)),
            Node("claim", "The universal steady-state uniqueness conjecture", ClaimFormula(),
                "Sections I.D and III conjecture a unique physical steady state for any constant rates and any upper cell order. Here the uniqueness assertion quantifies over every natural C >= 3 and every pair of rate functions positive on J C: any two physical stationary states agree at every order from 3 through C. It does not assert equality outside that interval or the existence of a stationary state.",
                AssessedProvenance.FromLiterature(Source)),
            Describe.Lean(
                DescribeId.Create("granular-steady-state-result"), DeclarationHandle.Create(Prefix + "result"),
                H("Two stationary states at upper order ten"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(Local("claim"))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Take C = 10. Its sixteen channels, in order, are "
                            + "(3,3), (3,4), (3,5), (3,6), (3,7), (3,8), (3,9), "
                            + "(4,4), (4,5), (4,6), (4,7), (4,8), (5,5), (5,6), (5,7), (6,6). "
                            + "Choose the merging rates "
                            + "p = (10/3, 2/3, 4/15, 4/3, 2/3, 2, 509018/225, 1, "
                            + "35579/175, 2, 422/5, 2, 386/225, 30416/25, 255689/25, 4) "
                            + "and the splitting rates "
                            + "q = (1, 2/5, 2, 972/5, 2, 2, 2138/75, 141/10, 1, 2, 2, "
                            + "3967/35, 35878/315, 2, 233557/35, 2). All these rates are strictly positive.")),
                    Paragraph(Text(
                        "In order from 3 through 10, take "
                            + "X = (3, 2, 5, 1, 2, 1, 1, 1)/16 and "
                            + "Y = (12, 6, 5, 4, 4, 1, 1, 1)/34, with zero values at other orders. "
                            + "Both states have strictly positive fractions on this interval and sum to one. "
                            + "At each state all eight balance rows of equation (2) vanish, and the total "
                            + "flux over J 10 is zero. Thus the full right-hand side vanishes at both states. "
                            + "Their order-three fractions differ: X_3 = 3/16 and Y_3 = 6/17. "
                            + "These two physical stationary states refute the uniqueness assertion."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("myhill-blumenfeld-2023-granular-steady-state-uniqueness-refutation"),
                    ResolutionKind.Refuted))
        )));

    private static DocumentBlock Node(string declaration, string title, Formula formula,
        string prose, AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create("granular-steady-state-" + declaration.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula ChannelsFormula()
    {
        Formula predicate = LambdaOf("a", OrderPair(), And(
            LE(Component(1), Component(2)),
            LE(Subtract(Add(Component(1), Component(2)), D(2)), V("C"))));
        Formula pairs = At(Qualified("Finset", "product"), Icc(D(3), V("C")), Icc(D(3), V("C")));
        return All("C", Naturals(), Equal(LocalCall("J", V("C")),
            At(Qualified("Finset", "filter"), predicate, pairs)));
    }

    private static Formula DeltaFormula() => All("i", Naturals(), All("j", Naturals(),
        Equal(Typed(LocalCall("delta", V("i"), V("j")), Reals()),
            Seq(Word("if"), Sp, Parenthesized(Equal(V("i"), V("j"))), Sp,
                Word("then"), Sp, D(1), Sp, Word("else"), Sp, D(0)))));

    private static Formula FluxFormula()
    {
        Formula smaller = At(Qualified("min"), V("i"), V("j"));
        Formula larger = At(Qualified("max"), V("i"), V("j"));
        Formula forward = Multiply(Multiply(At(V("p"), smaller, larger), At(V("Q"), V("i"))),
            At(V("Q"), V("j")));
        Formula reverse = Multiply(At(V("q"), smaller, larger),
            At(V("Q"), Subtract(Add(V("i"), V("j")), D(2))));
        return RateBinders(StateBinder(All("i", Naturals(), All("j", Naturals(),
            Equal(Typed(LocalCall("flux", V("p"), V("q"), V("Q"), V("i"), V("j")), Reals()),
                Subtract(forward, reverse))))));
    }

    private static Formula RhsFormula()
    {
        Formula partnerGain = Add(Subtract(V("k"), V("i")), D(2));
        Formula partnerLoss = Add(Subtract(V("i"), V("k")), D(2));
        Formula gain = Multiply(Typed(new Formula.Fraction(D(1), D(2)), Reals()),
            SumOver("i", Naturals(), Icc(D(3), Subtract(V("k"), D(1))),
                Multiply(Flux(V("i"), partnerGain),
                    Add(D(1), LocalCall("delta", V("i"), partnerGain)))));
        Formula loss = SumOver("i", Naturals(), Icc(Add(V("k"), D(1)), V("C")),
            Multiply(Flux(V("k"), partnerLoss),
                Add(D(1), LocalCall("delta", V("i"), Subtract(Multiply(D(2), V("k")), D(2))))));
        Formula normalization = Multiply(At(V("Q"), V("k")),
            SumOver("a", OrderPair(), LocalCall("J", V("C")), Flux(Component(1), Component(2))));
        return CutoffBinder(RateBinders(StateBinder(All("k", Naturals(),
            Equal(Typed(LocalCall("rhs", V("C"), V("p"), V("q"), V("Q"), V("k")), Reals()),
                Add(Subtract(gain, loss), normalization))))));
    }

    private static Formula PositiveRatesFormula() => CutoffBinder(RateBinders(
        Equivalence(LocalCall("PositiveRates", V("C"), V("p"), V("q")),
            All("a", OrderPair(), Imp(Member(V("a"), LocalCall("J", V("C"))),
                And(LT(D(0), At(V("p"), Component(1), Component(2))),
                    LT(D(0), At(V("q"), Component(1), Component(2)))))))));

    private static Formula PhysicalFormula() => CutoffBinder(StateBinder(
        Equivalence(LocalCall("Physical", V("C"), V("Q")),
            And(OrderBinders(LT(D(0), At(V("Q"), V("k")))),
                Equal(SumOver("k", Naturals(), Icc(D(3), V("C")), At(V("Q"), V("k"))), D(1))))));

    private static Formula StationaryFormula() => CutoffBinder(RateBinders(StateBinder(
        Equivalence(LocalCall("Stationary", V("C"), V("p"), V("q"), V("Q")),
            OrderBinders(Equal(LocalCall("rhs", V("C"), V("p"), V("q"), V("Q"), V("k")), D(0)))))));

    private static Formula ClaimFormula()
    {
        Formula other = Seq(V("Q"), Apos);
        Formula equality = OrderBinders(Equal(At(V("Q"), V("k")), At(other, V("k"))));
        Formula states = StateBinder(All(other, States(),
            Imp(LocalCall("Physical", V("C"), V("Q")),
                Imp(LocalCall("Physical", V("C"), other),
                    Imp(LocalCall("Stationary", V("C"), V("p"), V("q"), V("Q")),
                        Imp(LocalCall("Stationary", V("C"), V("p"), V("q"), other), equality))))));
        return Equivalence(Local("claim"), CutoffBinder(Imp(LE(D(3), V("C")),
            RateBinders(Imp(LocalCall("PositiveRates", V("C"), V("p"), V("q")), states)))));
    }

    private static Formula V(string name) => F.Id(name);
    private static Formula Qualified(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(V(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula Local(string name) => Qualified("D5", "S3", "StatisticalMechanics",
        "GranularCellOrderSteadyStateRefutation", name);
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula LocalCall(string name, params Formula[] args) => At(Local(name), args);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Word(string name) => Seq(Mathrm, Grp(V(name)));
    private static Formula Naturals() => Seq(Mathbb, Grp(V("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(V("R")));
    private static Formula Arrow(Formula domain, Formula codomain) => new Formula.TypeArrow(domain, codomain);
    private static Formula States() => Parenthesized(Arrow(Naturals(), Reals()));
    private static Formula Rates() => Parenthesized(Arrow(Naturals(), Arrow(Naturals(), Reals())));
    private static Formula OrderPair() => Parenthesized(Seq(Naturals(), Sp, Times, Sp, Naturals()));
    private static Formula Component(byte index) => Seq(V("a"), Dot, D(index));
    private static Formula Icc(Formula lower, Formula upper) => At(Qualified("Finset", "Icc"), lower, upper);
    private static Formula Flux(Formula i, Formula j) => LocalCall("flux", V("p"), V("q"), V("Q"), i, j);
    private static Formula CutoffBinder(Formula body) => All("C", Naturals(), body);
    private static Formula RateBinders(Formula body) => All("p", Rates(), All("q", Rates(), body));
    private static Formula StateBinder(Formula body) => All("Q", States(), body);
    private static Formula OrderBinders(Formula body) => All("k", Naturals(),
        Imp(LE(D(3), V("k")), Imp(LE(V("k"), V("C")), body)));
    private static Formula All(string name, Formula type, Formula body) => All(V(name), type, body);
    private static Formula All(Formula name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(name, type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(V(name), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula SumOver(string name, Formula type, Formula set, Formula body) =>
        Seq(new Formula.Subscript(Sum, Member(Typed(V(name), type), set)), Sp, Parenthesized(body));
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Add, Parenthesized(right));
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Subtract, Parenthesized(right));
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula LT(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula LE(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Member(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Equivalence(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
}
