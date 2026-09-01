using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Budget;

internal sealed class ProjectivePrimalConvergenceDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Weil/Budget/ProjectivePrimalConvergence.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite circle-moment primal optima converge to the full determining-family value "
            + "by weak-star compactness and closedness.",
        H("Projective Primal Convergence"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("mass-bounded-circle-measures-have-convergent-subsequence"),
                DeclarationHandle.Create(Prefix + "mass_bounded_weakStar_subsequence"),
                H("Mass-bounded circle measures have a weak-star convergent subsequence"),
                StatementSource.FromAuthor(MassSubsequenceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The proof extracts total masses in a compact interval and normalized "
                        + "probability measures in their compact metrizable weak topology, then "
                        + "reconstructs the finite-measure limit by continuous scalar multiplication."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("common-primal-budget-box-is-compact"),
                DeclarationHandle.Create(Prefix + "commonFeasible_isCompact"),
                H("The common primal budget box is weak-star compact"),
                StatementSource.FromAuthor(CommonCompactFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Both the Haar coefficient interval and the mass-bounded residual-measure "
                        + "set are compact, so their product is compact."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-level-primal-feasible-sets-are-closed"),
                DeclarationHandle.Create(Prefix + "levelFeasible_isClosed"),
                H("Finite-level primal feasible sets are weak-star closed"),
                StatementSource.FromAuthor(LevelClosedFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The reconstruction mass cap and every finite moment equality are closed "
                        + "because mass and integration against continuous circle functions are "
                        + "continuous in the weak topology."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("finite-level-primal-optimizer-exists"),
                DeclarationHandle.Create(Prefix + "level_optimizer_exists"),
                H("Every finite level has a primal optimizer"),
                StatementSource.FromAuthor(OptimizerFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Full feasibility makes every finite level nonempty; the continuous Haar-floor "
                        + "coordinate therefore attains its maximum on the compact level set."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("circle-projective-primal-convergence"),
                DeclarationHandle.Create(Prefix + "projective_primal_convergence"),
                H("Circle primal frontiers decrease to the full frontier"),
                StatementSource.FromAuthor(ProjectiveFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Finite-level optimizers lie in one weak-star compact budget box. A "
                            + "convergent subsequence is extracted rather than supplied as a premise.")),
                    Paragraph(Text(
                        "Closedness transfers the reconstruction budget and each fixed determining "
                            + "moment to the cluster, proving full feasibility. Continuity of the "
                            + "Haar-floor coordinate then identifies the antitone value limit with "
                            + "the full optimum."))),
                DescribeRole.Theorem))));

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Apply(Formula function, Formula value) =>
        Call("apply", function, value);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula AtMost(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula ForAll(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    private static Formula Exists(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [.. variables], body);

    private static Formula All(params Formula[] clauses)
    {
        Formula result = clauses[^1];
        for (var index = clauses.Length - 2; index >= 0; index--)
            result = And(clauses[index], result);
        return result;
    }

    private static Formula Natural() => Call("Nat");
    private static Formula Real() => Call("Real");
    private static Formula Nnreal() => Call("NNReal");
    private static Formula Circle() => Call("Circle");
    private static Formula FiniteCircleMeasure() => Call("FiniteMeasure", Circle());
    private static Formula PrimalPoint() => Call("Prod", Nnreal(), FiniteCircleMeasure());

    private static Formula MomentType() => new Formula.TypeArrow(
        Natural(), Call("ContinuousMap", Circle(), Real()));

    private static Formula TargetType() => new Formula.TypeArrow(Natural(), Real());

    private static Formula MassSubsequenceFormula()
    {
        Formula budget = F.Id("C"), sequence = F.Id("mu"), n = F.Id("n");
        Formula limit = F.Id("muStar"), selection = F.Id("phi"), k = F.Id("k");
        Formula sequenceType = new Formula.TypeArrow(Natural(), FiniteCircleMeasure());
        Formula massBound = ForAll(
            [Bound("n", Natural())],
            AtMost(Call("mass", Apply(sequence, n)), budget));
        Formula selectedLimit = Call(
            "Tendsto",
            Seq(Open, k, Mapsto, Apply(sequence, Apply(selection, k)), Close),
            F.Id("atTop"),
            Call("nhds", limit));
        Formula conclusion = Exists(
            [Bound("muStar", FiniteCircleMeasure()),
             Bound("phi", new Formula.TypeArrow(Natural(), Natural()))],
            All(
                AtMost(Call("mass", limit), budget),
                Call("StrictMono", selection),
                selectedLimit));
        return F.Disp(ForAll(
            [Bound("C", Nnreal()), Bound("mu", sequenceType)],
            Implies(massBound, conclusion)));
    }

    private static Formula CommonCompactFormula()
    {
        Formula budget = F.Id("C");
        return F.Disp(ForAll(
            [Bound("C", Nnreal())],
            Call("IsCompact", Call("commonFeasible", budget))));
    }

    private static Formula LevelClosedFormula()
    {
        Formula budget = F.Id("C"), moment = F.Id("Gamma"), target = F.Id("w");
        Formula n = F.Id("N");
        return F.Disp(ForAll(
            [Bound("C", Nnreal()), Bound("Gamma", MomentType()),
             Bound("w", TargetType()), Bound("N", Natural())],
            Call("IsClosed", Call("levelFeasible", budget, moment, target, n))));
    }

    private static Formula OptimizerFormula()
    {
        Formula budget = F.Id("C"), moment = F.Id("Gamma"), target = F.Id("w");
        Formula n = F.Id("N"), optimizer = F.Id("pStar"), competitor = F.Id("p");
        Formula fullNonempty = Call(
            "Nonempty", Call("fullFeasible", budget, moment, target));
        Formula optimizerConclusion = Exists(
            [Bound("pStar", PrimalPoint())],
            All(
                Call("Mem", optimizer, Call("levelFeasible", budget, moment, target, n)),
                ForAll(
                    [Bound("p", PrimalPoint())],
                    Implies(
                        Call("Mem", competitor,
                            Call("levelFeasible", budget, moment, target, n)),
                        AtMost(Call("objective", competitor),
                            Call("objective", optimizer))))));
        return F.Disp(ForAll(
            [Bound("C", Nnreal()), Bound("Gamma", MomentType()),
             Bound("w", TargetType()), Bound("N", Natural())],
            Implies(fullNonempty, optimizerConclusion)));
    }

    private static Formula ProjectiveFormula()
    {
        Formula budget = F.Id("C"), moment = F.Id("Gamma"), target = F.Id("w");
        Formula hierarchy = Call("levelFrontier", budget, moment, target);
        Formula fullValue = Call("fullFrontier", budget, moment, target);
        Formula optimizer = F.Id("optimizer"), cluster = F.Id("cluster");
        Formula selection = F.Id("phi"), n = F.Id("N"), k = F.Id("k");
        Formula fullNonempty = Call(
            "Nonempty", Call("fullFeasible", budget, moment, target));
        Formula selectedOptimizer = Apply(optimizer, Apply(selection, k));
        Formula witnesses = Exists(
            [Bound("optimizer", new Formula.TypeArrow(Natural(), PrimalPoint())),
             Bound("cluster", PrimalPoint()),
             Bound("phi", new Formula.TypeArrow(Natural(), Natural()))],
            All(
                ForAll(
                    [Bound("N", Natural())],
                    Call("Mem", Apply(optimizer, n),
                        Call("levelFeasible", budget, moment, target, n))),
                Call("StrictMono", selection),
                Call(
                    "Tendsto",
                    Seq(Open, k, Mapsto, selectedOptimizer, Close),
                    F.Id("atTop"),
                    Call("nhds", cluster)),
                Call("Mem", cluster, Call("fullFeasible", budget, moment, target)),
                Equal(Call("objective", cluster), fullValue)));
        Formula conclusion = All(
            Call("Antitone", hierarchy),
            Call("Tendsto", hierarchy, F.Id("atTop"), Call("nhds", fullValue)),
            witnesses);
        return F.Disp(ForAll(
            [Bound("C", Nnreal()), Bound("Gamma", MomentType()),
             Bound("w", TargetType())],
            Implies(fullNonempty, conclusion)));
    }
}
