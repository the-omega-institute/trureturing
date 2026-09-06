using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Negation;

internal sealed class DaoConceptBoundarySpecializationDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/Negation/DaoConceptBoundarySpecialization.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A set-theoretic specialization makes precise how a concept, its relative "
            + "opposite, and the ambient horizon delimit one another.",
        H("Dao Concept Boundary Specialization"),
        Blocks(
            Paragraph(Text(
                "The horizon is an explicitly chosen set, a concept is a subset, and its "
                    + "opposite is the relative difference of the horizon by that concept. "
                    + "This is a conditional mathematical model of non-exhaustive naming. "
                    + "It does not identify the historical Dao with a set, prove that every "
                    + "expression has a set-valued meaning, or establish the metaphysical "
                    + "premise that every expression leaves a nonempty remainder.")),
            Describe.Lean(
                DescribeId.Create("concept-boundary-iff-nonempty-remainder"),
                Handle("concept_boundary_iff_nonempty_remainder"),
                H("A concept boundary is exactly a nonempty remainder"),
                StatementSource.FromAuthor(ConceptBoundaryFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A concept is a proper subset of its horizon exactly when it lies inside "
                        + "that horizon and leaves at least one point of the horizon outside "
                        + "the concept."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("relative-opposite-is-proper-iff-concept-present"),
                Handle("relative_opposite_is_proper_iff_concept_present"),
                H("The relative opposite is proper exactly when the concept is present"),
                StatementSource.FromAuthor(RelativeOppositeFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Removing the concept from the horizon leaves a proper part precisely "
                        + "when the concept contains a point that also lies in the horizon."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("relative-opposite-and-concept-cover-horizon"),
                Handle("relative_opposite_and_concept_cover_horizon"),
                H("Concept and relative opposite recover the horizon"),
                StatementSource.FromAuthor(CoverHorizonFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Whenever the concept lies inside the horizon, the union of the concept "
                        + "and its relative opposite is exactly the horizon."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("equal-relative-opposites-iff-equal-concepts"),
                Handle("equal_relative_opposites_iff_equal_concepts"),
                H("Relative opposites distinguish concepts in one horizon"),
                StatementSource.FromAuthor(OppositeInjectivityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For two concepts contained in the same horizon, their relative "
                        + "opposites are equal exactly when the concepts are equal."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("admissible-expressions-are-proper-parts"),
                Handle("admissible_expressions_are_proper_parts"),
                H("Every non-exhaustive expression denotes a proper part"),
                StatementSource.FromAuthor(AllExpressionsFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If each expression denotes something inside the horizon and leaves a "
                        + "nonempty relative remainder, then every such denotation is a proper "
                        + "part of the horizon."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("dao-name-is-a-proper-part-under-the-same-premises"),
                Handle("dao_name_is_a_proper_part_under_the_same_premises"),
                H("The name Dao obeys the same conditional boundary"),
                StatementSource.FromAuthor(DaoNameFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A distinguished expression token called Dao is no exception: under the "
                        + "same universal containment and remainder premises, its denotation "
                        + "is a proper part of the horizon."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("empty-concept-opposite-is-whole"),
                Handle("empty_concept_opposite_is_whole"),
                H("An empty concept has the whole horizon as its opposite"),
                StatementSource.FromAuthor(EmptyConceptFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The empty-concept boundary case shows why concept presence is necessary: "
                        + "its relative opposite is the entire horizon."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("whole-horizon-leaves-no-remainder"),
                Handle("whole_horizon_leaves_no_remainder"),
                H("The whole horizon leaves no relative remainder"),
                StatementSource.FromAuthor(WholeHorizonFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At the other boundary, taking the entire horizon as the concept leaves "
                        + "the empty relative remainder."))),
                DescribeRole.Theorem))));

    private static DeclarationHandle Handle(string declaration) =>
        DeclarationHandle.Create(Prefix + declaration);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);

    private static Formula SetType(Formula carrier) => Call("Set", carrier);

    private static Formula Subset(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.SubsetOf, right);

    private static Formula ProperSubset(Formula left, Formula right) =>
        And(Subset(left, right), NotEqual(left, right));

    private static Formula Difference(Formula left, Formula right) =>
        Call("sdiff", left, right);

    private static Formula Intersection(Formula left, Formula right) =>
        Call("inter", left, right);

    private static Formula Union(Formula left, Formula right) =>
        Call("union", left, right);

    private static Formula Nonempty(Formula set) => Call("Nonempty", set);

    private static Formula EmptySet() => new Formula.SetLiteral([]);

    private static Formula ConceptBoundaryFormula()
    {
        Formula carrier = F.Id("X");
        Formula horizon = F.Id("H");
        Formula concept = F.Id("C");

        return F.Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("X", F.Id("Type")),
                Bound("H", SetType(carrier)),
                Bound("C", SetType(carrier)),
            ],
            Iff(
                ProperSubset(concept, horizon),
                And(Subset(concept, horizon), Nonempty(Difference(horizon, concept))))));
    }

    private static Formula RelativeOppositeFormula()
    {
        Formula carrier = F.Id("X");
        Formula horizon = F.Id("H");
        Formula concept = F.Id("C");

        return F.Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("X", F.Id("Type")),
                Bound("H", SetType(carrier)),
                Bound("C", SetType(carrier)),
            ],
            Iff(
                ProperSubset(Difference(horizon, concept), horizon),
                Nonempty(Intersection(horizon, concept)))));
    }

    private static Formula CoverHorizonFormula()
    {
        Formula carrier = F.Id("X");
        Formula horizon = F.Id("H");
        Formula concept = F.Id("C");

        return F.Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("X", F.Id("Type")),
                Bound("H", SetType(carrier)),
                Bound("C", SetType(carrier)),
            ],
            Implies(
                Subset(concept, horizon),
                Equal(Union(Difference(horizon, concept), concept), horizon))));
    }

    private static Formula OppositeInjectivityFormula()
    {
        Formula carrier = F.Id("X");
        Formula horizon = F.Id("H");
        Formula first = F.Id("C");
        Formula second = F.Id("D");

        return F.Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("X", F.Id("Type")),
                Bound("H", SetType(carrier)),
                Bound("C", SetType(carrier)),
                Bound("D", SetType(carrier)),
            ],
            Implies(
                And(Subset(first, horizon), Subset(second, horizon)),
                Iff(
                    Equal(Difference(horizon, first), Difference(horizon, second)),
                    Equal(first, second)))));
    }

    private static Formula AllExpressionsFormula()
    {
        Formula carrier = F.Id("X");
        Formula expressionType = F.Id("E");
        Formula horizon = F.Id("H");
        Formula meaning = F.Id("m");
        Formula expression = F.Id("e");
        Formula denotation = Apply(meaning, expression);
        Formula allInside = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("e"),
            expressionType,
            Subset(denotation, horizon));
        Formula allLeaveRemainder = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("e"),
            expressionType,
            Nonempty(Difference(horizon, denotation)));
        Formula conclusion = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("e"),
            expressionType,
            ProperSubset(denotation, horizon));

        return F.Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("X", F.Id("Type")),
                Bound("E", F.Id("Type")),
                Bound("H", SetType(carrier)),
                Bound("m", Arrow(expressionType, SetType(carrier))),
            ],
            Implies(And(allInside, allLeaveRemainder), conclusion)));
    }

    private static Formula DaoNameFormula()
    {
        Formula carrier = F.Id("X");
        Formula expressionType = F.Id("E");
        Formula horizon = F.Id("H");
        Formula meaning = F.Id("m");
        Formula expression = F.Id("e");
        Formula daoName = F.Id("d");
        Formula denotation = Apply(meaning, expression);
        Formula assumptions = And(
            new Formula.Bind(
                FormulaQuantifier.ForAll,
                FormulaIdentifier.Create("e"),
                expressionType,
                Subset(denotation, horizon)),
            new Formula.Bind(
                FormulaQuantifier.ForAll,
                FormulaIdentifier.Create("e"),
                expressionType,
                Nonempty(Difference(horizon, denotation))));

        return F.Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("X", F.Id("Type")),
                Bound("E", F.Id("Type")),
                Bound("H", SetType(carrier)),
                Bound("m", Arrow(expressionType, SetType(carrier))),
                Bound("d", expressionType),
            ],
            Implies(assumptions, ProperSubset(Apply(meaning, daoName), horizon))));
    }

    private static Formula EmptyConceptFormula()
    {
        Formula carrier = F.Id("X");
        Formula horizon = F.Id("H");

        return F.Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("X", F.Id("Type")),
                Bound("H", SetType(carrier)),
            ],
            Equal(Difference(horizon, EmptySet()), horizon)));
    }

    private static Formula WholeHorizonFormula()
    {
        Formula carrier = F.Id("X");
        Formula horizon = F.Id("H");

        return F.Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("X", F.Id("Type")),
                Bound("H", SetType(carrier)),
            ],
            Equal(Difference(horizon, horizon), EmptySet())));
    }
}
