using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using System.Collections.Immutable;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Budget;

internal sealed class MinimumCompleteSetCoverDocument : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/Observer/Budget/MinimumCompleteSetCover.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite observer completeness is exactly coverage of all distinct ordered state pairs; "
            + "minimum complete budgets are the corresponding natural-cost set covers.",
        H("Minimum Complete Set Cover"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-budget-injective-iff-cover"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "finite_budget_injective_iff_cover"),
                H("Finite-budget injectivity is separation coverage"),
                StatementSource.FromAuthor(FiniteBudgetCoverFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a Finset J, equality of joint readouts means equality at every selected "
                        + "observer. Thus injectivity is equivalent to the union of the selected "
                        + "separation sets being the universe of distinct ordered state pairs. "
                        + "Neither the state type nor the observer type is assumed finite."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("minimum-complete-budget-iff-minimum-cover"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "minimum_complete_budget_iff_minimum_cover"),
                H("Minimum complete budgets are minimum-cost covers"),
                StatementSource.FromAuthor(MinimumCoverFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The injectivity-cover equivalence rewrites both completeness of J and "
                        + "completeness of every competitor K. The remaining comparison is the "
                        + "natural-number sum of supplied observer costs, so this is precisely a "
                        + "finite-budget set-cover instance without an existence claim."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("counterexample-certifies-incomplete-budget"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "counterexample_certifies_incomplete_budget"),
                H("One collision certifies incompleteness"),
                StatementSource.FromAuthor(CounterexampleFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Two distinct states with equal selected joint readouts contradict "
                        + "injectivity. This is the counterexample half of Principle 12.1."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("injective-budget-covers-every-distinct-pair"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "injective_budget_covers_every_distinct_pair"),
                H("Completeness separates every distinct pair"),
                StatementSource.FromAuthor(EveryPairFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "An injective joint readout covers the distinct-pair universe. Membership in "
                        + "that union exposes a selected observer that separates each given pair, "
                        + "formalizing the complete-coverage half of Principle 12.1."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("empty-budget-iff-pair-universe-empty"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "empty_budget_injective_iff_pair_universe_empty"),
                H("The empty budget is complete exactly for an empty pair universe"),
                StatementSource.FromAuthor(EmptyBudgetFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The empty union covers exactly when there are no distinct state pairs. This "
                        + "also characterizes when an empty selected product can be injective."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("fin-zero-empty-budget-complete"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "fin_zero_empty_budget_complete"),
                H("The empty budget is complete on Fin zero"),
                StatementSource.FromAuthor(FinZeroFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Fin 0 has no states and hence no distinct pairs. Its empty-budget readout is "
                        + "injective vacuously, covering the empty-state degeneracy explicitly."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("singleton-empty-budget-complete"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "singleton_empty_budget_complete"),
                H("The empty budget is complete on a singleton"),
                StatementSource.FromAuthor(SingletonFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Unit has no pair of unequal states. Consequently its distinct-pair universe "
                        + "is empty and every empty-budget joint readout is injective."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("constant-observer-separation-set-empty"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "constant_observer_separation_set_empty"),
                H("A constant observer separates no pair"),
                StatementSource.FromAuthor(ConstantObserverFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A constant readout agrees on both components of every pair, so its named "
                        + "separation set is empty on every state space."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("identity-observer-singleton-budget-complete"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "identity_observer_singleton_budget_complete"),
                H("One identity observer is complete"),
                StatementSource.FromAuthor(IdentityObserverFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The identity coordinate recovers the state from the singleton joint readout. "
                        + "The main equivalence then shows that its separation set covers every "
                        + "distinct ordered pair, including on infinite state spaces."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("zero-observer-singleton-budget-incomplete-on-nat"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "zero_observer_singleton_budget_incomplete_on_nat"),
                H("One zero observer is incomplete on Nat"),
                StatementSource.FromAuthor(ZeroObserverFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The constant-zero observer has empty separation set, while the states zero "
                        + "and one collide. This supplies a concrete trivial-map audit."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("zero-cost-budget-minimum-iff-complete"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "zero_cost_budget_minimum_iff_complete"),
                H("With zero costs, minimum means complete"),
                StatementSource.FromAuthor(ZeroCostFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If every observer costs zero, all finite budgets have equal total cost. A "
                        + "budget is therefore minimum complete exactly when it is complete."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("empty-separation-observer-removal-preserves-minimum"),
                DeclarationHandle.Create(
                    DeclarationPrefix
                        + "empty_separation_observer_removal_preserves_minimum"),
                H("A useless observer can be removed from a minimum budget"),
                StatementSource.FromAuthor(RemovalFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Erasing an observer whose separation set is empty leaves the cover unchanged. "
                        + "Natural-number nonnegativity makes the erased budget no more expensive, "
                        + "so minimum completeness is preserved."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("empty-separation-hypothesis-is-necessary"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "empty_separation_hypothesis_is_necessary"),
                H("Empty separation is necessary for the removal theorem"),
                StatementSource.FromAuthor(EmptySeparationNecessaryFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "On Bool, the sole identity observer is a zero-cost minimum complete budget "
                        + "and has nonempty separation set. Erasing it yields the empty incomplete "
                        + "budget, giving a concrete counterexample if the premise is omitted."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("minimum-budget-hypothesis-is-necessary"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "minimum_budget_hypothesis_is_necessary"),
                H("Starting minimality is necessary for the removal theorem"),
                StatementSource.FromAuthor(MinimumHypothesisNecessaryFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For three observers on Bool, observer zero is useless and observer one is an "
                        + "identity of cost two. After erasing zero, that budget remains dominated "
                        + "by the identity observer two of cost one, so it is not minimum."))),
                DescribeRole.Lemma)),
        [DocumentEdge.Dependency.Create(GidRef.Create(
            "D5/S3/ConceptDynamics/Faithfulness/JointFaithfulnessLeibnizCriterion"))]));

    private static Formula.TypeArrow Arrow(Formula domain, Formula codomain) =>
        new(domain, codomain);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula.Logic And(Formula left, Formula right) =>
        new(left, FormulaLogicOperator.And, right);

    private static Formula.Logic ImpliesFormula(Formula left, Formula right) =>
        new(left, FormulaLogicOperator.Implies, right);

    private static Formula.Logic IffFormula(Formula left, Formula right) =>
        new(left, FormulaLogicOperator.Iff, right);

    private static Formula TypeUniverse() =>
        Seq(Operatorname, Grp(F.Id("Type")));

    private static Formula NaturalNumbers() =>
        Seq(Mathbb, Grp(F.Id("N")));

    private static Formula FinsetOf(Formula carrier) =>
        Call("Finset", carrier);

    private static Formula Complete(Formula budget, Formula observers) =>
        Call("Injective", Call("jointReadout", budget, observers));

    private static Formula Cover(
        Formula budget,
        Formula observers,
        Formula stateType) =>
        Equal(
            Call("selectedSeparationUnion", budget, observers),
            Call("statePairUniverse", stateType));

    private static Formula Minimum(
        Formula budget,
        Formula observers,
        Formula costs) =>
        Call("IsMinimumCompleteBudget", budget, observers, costs);

    private static Formula Separation(Formula observers, Formula observer) =>
        Call("observerSeparationSet", observers, observer);

    private static Formula Cost(Formula budget, Formula costs) =>
        Call("budgetCost", budget, costs);

    private static Formula EmptyBudget() => Emptyset;

    private static Formula Singleton(Formula value) =>
        Seq(OpenBrace, value, CloseBrace);

    private static Formula ObserverFamilyType(
        Formula indexType,
        Formula stateType,
        Formula valueFamily) =>
        Call("ObserverFamily", indexType, stateType, valueFamily);

    private static Formula[] StandardObjects()
    {
        Formula stateType = F.Id("X");
        Formula indexType = F.Id("I");
        Formula valueFamily = F.Id("V");
        return
        [
            stateType,
            indexType,
            valueFamily,
            F.Id("q"),
            F.Id("J"),
            F.Id("c"),
        ];
    }

    private static ImmutableArray<Formula.BoundVariable> StandardBindings(
        Formula[] objects,
        bool includeCost)
    {
        Formula stateType = objects[0];
        Formula indexType = objects[1];
        Formula valueFamily = objects[2];
        ImmutableArray<Formula.BoundVariable> core =
        [
            Bound("X", TypeUniverse()),
            Bound("I", TypeUniverse()),
            Bound("V", Arrow(indexType, TypeUniverse())),
            Bound("q", ObserverFamilyType(indexType, stateType, valueFamily)),
            Bound("J", FinsetOf(indexType)),
        ];
        return includeCost
            ? core.Add(Bound("c", Arrow(indexType, NaturalNumbers())))
            : core;
    }

    private static Formula FiniteBudgetCoverFormula()
    {
        Formula[] objects = StandardObjects();
        Formula stateType = objects[0];
        Formula observers = objects[3];
        Formula budget = objects[4];
        Formula body = IffFormula(
            Complete(budget, observers),
            Cover(budget, observers, stateType));
        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            StandardBindings(objects, false),
            body));
    }

    private static Formula MinimumCoverFormula()
    {
        Formula[] objects = StandardObjects();
        Formula stateType = objects[0];
        Formula indexType = objects[1];
        Formula observers = objects[3];
        Formula budget = objects[4];
        Formula costs = objects[5];
        Formula competitor = F.Id("K");
        Formula leastCost = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("K"),
            FinsetOf(indexType),
            ImpliesFormula(
                Cover(competitor, observers, stateType),
                Seq(Cost(budget, costs), Sp, Leq, Sp, Cost(competitor, costs))));
        Formula body = IffFormula(
            Minimum(budget, observers, costs),
            And(Cover(budget, observers, stateType), leastCost));
        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            StandardBindings(objects, true),
            body));
    }

    private static Formula CounterexampleFormula()
    {
        Formula[] objects = StandardObjects();
        Formula stateType = objects[0];
        Formula observers = objects[3];
        Formula budget = objects[4];
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula collision = And(
            NotEqual(x, y),
            Equal(
                Call("jointReadoutAt", budget, observers, x),
                Call("jointReadoutAt", budget, observers, y)));
        Formula witness = new Formula.BindMany(
            FormulaQuantifier.Exists,
            [Bound("x", stateType), Bound("y", stateType)],
            collision);
        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            StandardBindings(objects, false),
            ImpliesFormula(witness, new Formula.Not(Complete(budget, observers)))));
    }

    private static Formula EveryPairFormula()
    {
        Formula[] objects = StandardObjects();
        Formula stateType = objects[0];
        Formula indexType = objects[1];
        Formula observers = objects[3];
        Formula budget = objects[4];
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula observer = F.Id("i");
        Formula selectedSeparation = new Formula.Bind(
            FormulaQuantifier.Exists,
            FormulaIdentifier.Create("i"),
            indexType,
            And(
                Seq(observer, Sp, InMacro, Sp, budget),
                Call("Separates", observers, observer, x, y)));
        Formula everyPair = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("x", stateType), Bound("y", stateType)],
            ImpliesFormula(NotEqual(x, y), selectedSeparation));
        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            StandardBindings(objects, false),
            ImpliesFormula(Complete(budget, observers), everyPair)));
    }

    private static Formula EmptyBudgetFormula()
    {
        Formula[] objects = StandardObjects();
        Formula stateType = objects[0];
        Formula observers = objects[3];
        Formula body = IffFormula(
            Complete(EmptyBudget(), observers),
            Equal(Call("statePairUniverse", stateType), Emptyset));
        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            StandardBindings(objects, false).RemoveAt(4),
            body));
    }

    private static Formula FinZeroFormula()
    {
        Formula indexType = F.Id("I");
        Formula stateType = Call("Fin", D(0));
        Formula observers = F.Id("q");
        Formula body = And(
            Equal(Call("statePairUniverse", stateType), Emptyset),
            Complete(EmptyBudget(), observers));
        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("I", TypeUniverse()),
                Bound("q", Call("ObserverFamily", indexType, stateType)),
            ],
            body));
    }

    private static Formula SingletonFormula()
    {
        Formula indexType = F.Id("I");
        Formula stateType = F.Id("Unit");
        Formula observers = F.Id("q");
        Formula body = And(
            Equal(Call("statePairUniverse", stateType), Emptyset),
            Complete(EmptyBudget(), observers));
        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("I", TypeUniverse()),
                Bound("q", Call("ObserverFamily", indexType, stateType)),
            ],
            body));
    }

    private static Formula ConstantObserverFormula()
    {
        Formula indexType = F.Id("I");
        Formula stateType = F.Id("X");
        Formula values = F.Id("value");
        Formula observer = F.Id("i");
        Formula constantObservers = Call("constantObserverFamily", values);
        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("X", TypeUniverse()),
                Bound("I", TypeUniverse()),
                Bound("value", Call("ValueFamily", indexType)),
                Bound("i", indexType),
            ],
            Equal(Separation(constantObservers, observer), Emptyset)));
    }

    private static Formula IdentityObserverFormula()
    {
        Formula stateType = F.Id("X");
        Formula observers = Call("identityObserverFamily", stateType);
        Formula budget = Singleton(Star);
        Formula body = And(
            Complete(budget, observers),
            Cover(budget, observers, stateType));
        return Disp(new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("X"),
            TypeUniverse(),
            body));
    }

    private static Formula ZeroObserverFormula()
    {
        Formula observers = Call("constantObserverFamily", D(0));
        Formula budget = Singleton(Star);
        return Disp(And(
            Equal(Separation(observers, Star), Emptyset),
            new Formula.Not(Complete(budget, observers))));
    }

    private static Formula ZeroCostFormula()
    {
        Formula[] objects = StandardObjects();
        Formula observers = objects[3];
        Formula budget = objects[4];
        Formula zeroCosts = Call("const", D(0));
        Formula body = IffFormula(
            Minimum(budget, observers, zeroCosts),
            Complete(budget, observers));
        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            StandardBindings(objects, false),
            body));
    }

    private static Formula RemovalFormula()
    {
        Formula[] objects = StandardObjects();
        Formula indexType = objects[1];
        Formula observers = objects[3];
        Formula budget = objects[4];
        Formula costs = objects[5];
        Formula observer = F.Id("i");
        Formula premise = And(
            Equal(Separation(observers, observer), Emptyset),
            Minimum(budget, observers, costs));
        Formula conclusion = Minimum(
            Call("erase", budget, observer),
            observers,
            costs);
        Formula bindings = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("i"),
            indexType,
            ImpliesFormula(premise, conclusion));
        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            StandardBindings(objects, true),
            ImpliesFormula(Call("DecidableEq", indexType), bindings)));
    }

    private static Formula EmptySeparationNecessaryFormula()
    {
        Formula stateType = F.Id("Bool");
        Formula observers = Call("identityObserverFamily", stateType);
        Formula costs = Call("const", D(0));
        Formula budget = Singleton(Star);
        Formula erased = Call("erase", budget, Star);
        return Disp(And(
            Minimum(budget, observers, costs),
            And(
                NotEqual(Separation(observers, Star), Emptyset),
                new Formula.Not(Minimum(erased, observers, costs)))));
    }

    private static Formula MinimumHypothesisNecessaryFormula()
    {
        Formula observers = Call(
            "observerTriple",
            Call("const", F.Id("false")),
            F.Id("id"),
            F.Id("id"));
        Formula costs = Call("costTriple", D(0), D(2), D(1));
        Formula budget = Seq(OpenBrace, D(0), Comma, Sp, D(1), CloseBrace);
        Formula erased = Call("erase", budget, D(0));
        return Disp(And(
            Equal(Separation(observers, D(0)), Emptyset),
            new Formula.Not(Minimum(erased, observers, costs))));
    }
}
