using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DecisionValue;

internal sealed class MixedImitationBestResponseCycleDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/DecisionValue/MixedImitationBestResponseCycle.";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/ConceptDynamics/hasheminejadramazi2023equilibration");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A four-agent coordination network has a persistent mixed imitation and best-response trajectory that never reaches equilibrium.",
        H("A persistent cycle in mixed imitation and best-response dynamics"),
        Blocks(
            Node("utility", "Accumulated utility", UtilityFormula(),
                AssessedProvenance.FromLiterature(Source),
                "For n agents, adj specifies the neighbours and pay gives each agent's real payoff for a pair of Boolean strategies. "
                    + "The strategy false represents A and true represents B. Utility is the sum of pay i (x i) (x j) over all neighbours j of i; "
                    + "an empty neighbourhood contributes zero. This is the accumulated utility in Section 2, lines 134–148 of the v3 TeX source."),
            Node("hasMaximizer", "A strategy among the highest-earning neighbours", HasMaximizerFormula(),
                AssessedProvenance.FromLiterature(Source),
                "The predicate says that a neighbour j uses s and has utility at least that of every neighbour k of i. "
                    + "Utilities are those of the neighbours themselves in the unchanged state x. "
                    + "This expresses the maximization in the imitation rule at lines 149–155. "
                    + "Both strategies can have maximizing neighbours; with no neighbours neither strategy does."),
            Node("update", "The active agent's new strategy", UpdateFormula(),
                AssessedProvenance.FromLiterature(Source),
                "An agent with imitator i equal to true copies the strategy of its highest-earning neighbours when that strategy is unique. "
                    + "If both strategies occur among those neighbours, it retains x i. "
                    + "An agent with imitator i equal to false compares its own utilities after replacing its strategy by false and by true, "
                    + "takes the strictly better strategy, and retains x i when the utilities are equal. "
                    + "These are the rules and tie convention of lines 149–167. "
                    + "As a repository totalization convention, an imitator with no neighbours retains x i; the cited argmax rule leaves this case unspecified."),
            Node("step", "One asynchronous update", StepFormula(),
                AssessedProvenance.FromLiterature(Source),
                "Only coordinate i changes, to the value prescribed by update. Every other coordinate remains equal to its value in x. "
                    + "This is the asynchronous convention at lines 150–151."),
            Node("traj", "The trajectory of an activation sequence", TrajectoryFormula(),
                AssessedProvenance.FromLiterature(Source),
                "The trajectory begins at x. At time t, the sequence a selects the active agent, and one asynchronous step produces the state at time t + 1. "
                    + "This recursion expresses the decision-making dynamics described at lines 150–167 and 206."),
            Node("IsEquilibrium", "Equilibrium under every activation sequence", EquilibriumFormula(),
                AssessedProvenance.FromLiterature(Source),
                "A state is an equilibrium when every activation sequence leaves it fixed at every natural time. "
                    + "The sequence in this definition is arbitrary, without a persistence restriction, as in lines 207–215."),
            Node("IsPersistent", "Arbitrarily late activations of every agent", PersistenceFormula(),
                AssessedProvenance.FromLiterature(Source),
                "For every agent i and every natural time t, some time u at least t activates i. "
                    + "Thus every agent is activated infinitely often, the persistence condition at lines 217–218."),
            Node("claim", "Universal equilibration on finite undirected graphs", ClaimFormula(),
                AssessedProvenance.FromRepo(Source),
                "For every natural n and every symmetric irreflexive adjacency relation, choose any assignment of imitation and best-response rules "
                    + "and any real payoffs satisfying the strict coordination inequality at every agent. "
                    + "The claim says that every initial state and every persistent activation sequence reach an equilibrium at some natural time. "
                    + "It gives the general-graph reading of the question at lines 225 and 668; it asserts no separate conclusion about dense trees or potential functions."),
            Describe.Lean(
                DescribeId.Create("mixed-imitation-best-response-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("A persistent four-agent cycle"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(Local("claim"))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Take four agents 0, 1, 2, 3, with edges {0,1}, {1,2}, {1,3}, {0,3}, {2,3}. "
                            + "Adjacency is symmetric and irreflexive. Agent 1 is a best-responder, and agents 0, 2, 3 are imitators. "
                            + "Their payoff quadruples (R,S,T,P), in that order, are (1,0,0,4), (3,2,2,3), (4,1,0,4), (4,3,3,4). "
                            + "The strict coordination inequalities reduce respectively to 0 < 1, 2 < 3, 1 < 4 and 3 < 4.")),
                    Paragraph(Text(
                        "Repeat the activation block (2,0,3,1). Given any natural t, agents 0, 1, 2, 3 are activated at the respective times "
                            + "4t + 1, 4t + 3, 4t and 4t + 2, all at least t, so the sequence is persistent. "
                            + "Its value at t + 8 equals its value at t.")),
                    Paragraph(Text(
                        "Consider the eight states BABB, BABA, BBBA, BBAA, ABAA, ABAB, AAAB, AABB, with coordinates ordered 0, 1, 2, 3. "
                            + "Their utility vectors are respectively (4,6,4,11), (0,7,0,10), (4,8,4,9), (4,7,5,10), "
                            + "(1,6,5,11), (0,7,2,10), (1,8,5,9), (1,7,4,10). "
                            + "For these same states, agent 1's utility after choosing A is respectively 6, 7, 7, 8, 9, 8, 8, 7; "
                            + "after choosing B it is 9, 8, 8, 7, 6, 7, 7, 8. These values follow by summing the specified edge payoffs.")),
                    Paragraph(Text(
                        "Starting from BABB, the activations at times 0 and 1 leave the state unchanged. "
                            + "From time 2, the next eight active agents are 3, 1, 2, 0, 3, 1, 2, 0. "
                            + "The utility comparisons above show that each activation takes the corresponding state in the eight-state list to the next, "
                            + "with AABB returning to BABB. Consequently the states at times 0, 1, 2 are BABB, "
                            + "and those at times 3 through 10 are BABA, BBBA, BBAA, ABAA, ABAB, AAAB, AABB, BABB.")),
                    Paragraph(Text(
                        "The trajectory has period eight from time 2. For the initial equality, the states at times 10 and 2 are both BABB. "
                            + "For the induction step, equality of the states at t + 8 and t, together with equality of their active agents, "
                            + "gives equality after the same one-agent update at times t + 9 and t + 1. "
                            + "The shifted trajectory at times t + 2 is therefore periodic with period eight. "
                            + "Reducing t modulo eight shows that every state from time 2 belongs to the displayed eight-state list.")),
                    Paragraph(Text(
                        "An equilibrium must be fixed by a step at every agent i: apply its defining condition at time 1 to the constant activation sequence with value i. "
                            + "Each state in the list is moved to a distinct next state by its designated active agent, so none is an equilibrium. "
                            + "The states at times 0 and 1 are also the first state in that list. Thus the trajectory is never at equilibrium. "
                            + "Applying the universal claim to this symmetric irreflexive network, its coordinating payoffs, initial state and persistent sequence "
                            + "would give a time when this very trajectory is at equilibrium, a contradiction."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Node(string declaration, string title, Formula formula,
        AssessedProvenance provenance, string prose) =>
        Describe.Lean(DescribeId.Create("mixed-imitation-best-response-" + declaration.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula UtilityFormula()
    {
        Formula neighbours = At(Qualified("Finset", "filter"), At(X("adj"), X("i")),
            Typed(Qualified("Finset", "univ"), At(Qualified("Finset"), Agents())));
        Formula sum = Seq(new Formula.Subscript(Sum,
            Seq(X("j"), Sp, InMacro, Sp, neighbours)), Sp,
            Parenthesized(At(X("pay"), X("i"), At(X("x"), X("i")), At(X("x"), X("j")))));
        return PayStateBinders(All("i", Agents(), Equal(
            LocalCall("utility", X("adj"), X("pay"), X("x"), X("i")), sum)));
    }

    private static Formula HasMaximizerFormula()
    {
        Formula maximum = Some("j", Agents(), Conjunction(At(X("adj"), X("i"), X("j")),
            Conjunction(Equal(At(X("x"), X("j")), X("s")),
                All("k", Agents(), Implication(At(X("adj"), X("i"), X("k")),
                    LE(Utility(X("x"), X("k")), Utility(X("x"), X("j"))))))));
        return PayStateBinders(All("i", Agents(), All("s", Booleans(), Equivalence(
            LocalCall("hasMaximizer", X("adj"), X("pay"), X("x"), X("i"), X("s")), maximum))));
    }

    private static Formula UpdateFormula()
    {
        Formula hasA = LocalCall("hasMaximizer", X("adj"), X("pay"), X("x"), X("i"), FalseValue());
        Formula hasB = LocalCall("hasMaximizer", X("adj"), X("pay"), X("x"), X("i"), TrueValue());
        Formula current = At(X("x"), X("i"));
        Formula imitate = If(hasA, If(hasB, current, FalseValue()), If(hasB, TrueValue(), current));
        Formula chooseA = Utility(At(Qualified("Function", "update"), X("x"), X("i"), FalseValue()), X("i"));
        Formula chooseB = Utility(At(Qualified("Function", "update"), X("x"), X("i"), TrueValue()), X("i"));
        Formula respond = If(LT(chooseA, chooseB), TrueValue(), If(LT(chooseB, chooseA), FalseValue(), current));
        return NetworkStateBinders(All("i", Agents(), Equal(
            LocalCall("update", X("adj"), X("imitator"), X("pay"), X("x"), X("i")),
            If(Equal(At(X("imitator"), X("i")), TrueValue()), imitate, respond))));
    }

    private static Formula StepFormula() => NetworkStateBinders(All("i", Agents(), Equal(
        LocalCall("step", X("adj"), X("imitator"), X("pay"), X("x"), X("i")),
        At(Qualified("Function", "update"), X("x"), X("i"),
            LocalCall("update", X("adj"), X("imitator"), X("pay"), X("x"), X("i"))))));

    private static Formula TrajectoryFormula() => NetworkStateBinders(All("a", ScheduleType(), Conjunction(
        Equal(Trajectory(Typed(D(0), Naturals())), X("x")),
        All("t", Naturals(), Equal(Trajectory(Add(X("t"), Typed(D(1), Naturals()))),
            LocalCall("step", X("adj"), X("imitator"), X("pay"), Trajectory(X("t")), At(X("a"), X("t"))))))));

    private static Formula EquilibriumFormula() => NetworkStateBinders(Equivalence(
        LocalCall("IsEquilibrium", X("adj"), X("imitator"), X("pay"), X("x")),
        All("a", ScheduleType(), All("t", Naturals(), Equal(Trajectory(X("t")), X("x"))))));

    private static Formula PersistenceFormula() => All("n", Naturals(), All("a", ScheduleType(), Equivalence(
        LocalCall("IsPersistent", X("a")),
        All("i", Agents(), All("t", Naturals(), Some("u", Naturals(), Conjunction(
            LE(X("t"), X("u")), Equal(At(X("a"), X("u")), X("i")))))))));

    private static Formula ClaimFormula()
    {
        Formula coordination = All("i", Agents(), LT(
            At(Qualified("max"), At(X("pay"), X("i"), TrueValue(), FalseValue()),
                At(X("pay"), X("i"), FalseValue(), TrueValue())),
            At(Qualified("min"), At(X("pay"), X("i"), FalseValue(), FalseValue()),
                At(X("pay"), X("i"), TrueValue(), TrueValue()))));
        Formula equilibration = All("x", StateType(), All("a", ScheduleType(),
            Implication(LocalCall("IsPersistent", X("a")), Some("t", Naturals(),
                LocalCall("IsEquilibrium", X("adj"), X("imitator"), X("pay"), Trajectory(X("t")))))));
        return Equivalence(Local("claim"), All("n", Naturals(), All("adj", AdjacencyType(),
            Implication(At(Qualified("Symmetric"), X("adj")),
                Implication(At(Qualified("Std", "Irrefl"), X("adj")),
                    All("imitator", StateType(), All("pay", PayoffType(),
                        Implication(coordination, equilibration))))))));
    }

    private static Formula PayStateBinders(Formula body) => All("n", Naturals(),
        All("adj", AdjacencyType(), All("pay", PayoffType(), All("x", StateType(), body))));
    private static Formula NetworkStateBinders(Formula body) => All("n", Naturals(),
        All("adj", AdjacencyType(), All("imitator", StateType(), All("pay", PayoffType(), All("x", StateType(), body)))));
    private static Formula Utility(Formula x, Formula i) => LocalCall("utility", X("adj"), X("pay"), x, i);
    private static Formula Trajectory(Formula t) =>
        LocalCall("traj", X("adj"), X("imitator"), X("pay"), X("x"), X("a"), t);
    private static Formula Agents() => At(Qualified("Fin"), X("n"));
    private static Formula StateType() => Arrow(Agents(), Booleans());
    private static Formula ScheduleType() => Arrow(Naturals(), Agents());
    private static Formula AdjacencyType() => Arrow(Agents(), Arrow(Agents(), Qualified("Prop")));
    private static Formula PayoffType() => Arrow(Agents(), Arrow(Booleans(), Arrow(Booleans(), Reals())));
    private static Formula Booleans() => Qualified("Bool");
    private static Formula FalseValue() => Qualified("Bool", "false");
    private static Formula TrueValue() => Qualified("Bool", "true");
    private static Formula Naturals() => Seq(Mathbb, Grp(X("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(X("R")));
    private static Formula Local(string name) => Qualified("D5", "S3", "ConceptDynamics", "DecisionValue",
        "MixedImitationBestResponseCycle", name);
    private static Formula LocalCall(string name, params Formula[] arguments) => At(Local(name), arguments);
    private static Formula Qualified(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(X(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula X(string name) => F.Id(name);
    private static Formula At(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Left, Open, value, Right, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula LE(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula LT(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Conjunction(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Implication(Formula left, Formula right) =>
        new Formula.TypeArrow(Parenthesized(left), Parenthesized(right));
    private static Formula Equivalence(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula If(Formula condition, Formula yes, Formula no) => At(Qualified("ite"), condition, yes, no);
}
