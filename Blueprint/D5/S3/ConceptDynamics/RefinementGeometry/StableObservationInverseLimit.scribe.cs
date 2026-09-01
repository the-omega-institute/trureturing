using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.RefinementGeometry;

internal sealed class StableObservationInverseLimitDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/RefinementGeometry/StableObservationInverseLimit.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Expanding operation languages canonically form an inverse system of observational "
            + "quotients.",
        H("Stable Observation Inverse Limit"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("stable-observation-inverse-limit-laws"),
                DeclarationHandle.Create(Prefix + "stable_observation_inverse_limit_laws"),
                H("Stable observations form a functorial inverse-limit system"),
                StatementSource.FromAuthor(InverseLimitFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "At level n, two states are equivalent when every operation admitted "
                            + "at that level has the same readout on them. Inclusion of each "
                            + "operation family in its successor therefore makes the equivalence "
                            + "relations decrease.")),
                    Paragraph(Text(
                        "The relation inclusion induces the canonical map from the finer "
                            + "quotient to the coarser quotient. It preserves representatives, "
                            + "is independent of their choice, and its maps obey identity and "
                            + "composition along the level order.")),
                    Paragraph(Text(
                        "The stable observation space is the type of compatible threads in this "
                            + "quotient tower, reusing the repository's abstract inverse-thread "
                            + "construction."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("strict-observation-refinement-witness"),
                DeclarationHandle.Create(Prefix + "strict_observation_refinement_witness"),
                H("The observational equivalence tower can decrease strictly"),
                StatementSource.FromAuthor(StrictWitnessFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For Boolean states and one operation, level zero admits no operation and "
                        + "level one admits the identity observation. Thus false and true are "
                        + "equivalent at level zero but separated at level one."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/ConceptDynamics/RefinementFactorization/"
                    + "InterventionFamilyKernelMonotonicity")),
            DocumentEdge.Dependency.Create(GidRef.Create(
                "D5/S3/ConceptDynamics/RefinementGeometry/InverseLimitCompletion")),
        ]));

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula SubsetOf(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.SubsetOf, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula hypothesis, Formula conclusion) =>
        new Formula.Logic(hypothesis, FormulaLogicOperator.Implies, conclusion);

    private static Formula AndMany(params Formula[] clauses)
    {
        Formula result = clauses[^1];
        for (var index = clauses.Length - 2; index >= 0; index--)
        {
            result = And(clauses[index], result);
        }

        return result;
    }

    private static Formula InverseLimitFormula()
    {
        Formula type = F.Id("Type");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula operation = F.Id("A");
        Formula state = F.Id("X");
        Formula observation = F.Id("Y");
        Formula family = F.Id("mathcalA");
        Formula observe = F.Id("O");
        Formula level = F.Id("n");
        Formula coarse = F.Id("i");
        Formula middle = F.Id("j");
        Formula fine = F.Id("k");
        Formula left = F.Id("x");
        Formula right = F.Id("y");
        Formula thread = F.Id("s");
        Formula next = Seq(level, Plus, D(1));
        Formula familyType = new Formula.TypeArrow(naturals, Call("Set", operation));
        Formula observeType = new Formula.TypeArrow(
            operation,
            new Formula.TypeArrow(state, observation));

        Formula RelationAt(Formula index) =>
            Call("operationSetoid", family, observe, index);

        Formula Restrict(Formula lower, Formula upper) =>
            Call("r", upper, lower);

        Formula Class(Formula value, Formula index) =>
            Call("class", value, index);

        Formula Value(Formula value, Formula index) =>
            new Formula.Subscript(value, index);

        Formula decreasing = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("n", naturals)],
            SubsetOf(RelationAt(next), RelationAt(level)));

        Formula representativeLaw = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("n", naturals), Bound("x", state)],
            Equal(
                Apply(Restrict(level, next), Class(left, next)),
                Class(left, level)));

        Formula wellDefined = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("n", naturals), Bound("x", state), Bound("y", state)],
            Implies(
                Call("EquivalentAt", family, observe, next, left, right),
                Equal(
                    Apply(Restrict(level, next), Class(left, next)),
                    Apply(Restrict(level, next), Class(right, next)))));

        Formula identityLaw = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("n", naturals)],
            Equal(Restrict(level, level), F.Id("id")));

        Formula order = And(Le(coarse, middle), Le(middle, fine));
        Formula compositionLaw = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("i", naturals), Bound("j", naturals), Bound("k", naturals)],
            Implies(
                order,
                Equal(
                    Restrict(coarse, fine),
                    Seq(
                        Restrict(coarse, middle),
                        Sp,
                        Circ,
                        Sp,
                        Restrict(middle, fine)))));

        Formula stableSpace = Call("StableObservationSpace", family, observe);
        Formula compatibility = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("s", stableSpace), Bound("n", naturals)],
            Equal(
                Apply(Restrict(level, next), Value(thread, next)),
                Value(thread, level)));

        Formula conclusion = AndMany(
            decreasing,
            representativeLaw,
            wellDefined,
            And(identityLaw, compositionLaw),
            compatibility);

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("A", type),
                Bound("X", type),
                Bound("Y", type),
                Bound("mathcalA", familyType),
                Bound("O", observeType),
            ],
            Implies(Call("Increasing", family), conclusion)));
    }

    private static Formula StrictWitnessFormula()
    {
        Formula family = F.Id("strictOperationFamily");
        Formula observe = F.Id("strictObservation");
        Formula fine = Call("operationSetoid", family, observe, D(1));
        Formula coarse = Call("operationSetoid", family, observe, D(0));
        return Disp(Call("StrictSubset", fine, coarse));
    }
}
