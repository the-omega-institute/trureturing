using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Reporting;

internal sealed class PublicCausalActivityCriterionDocument
    : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Reporting/PublicCausalActivityCriterion.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Public causal activity rules out public dynamic equivalence, while Boolean "
            + "witnesses separate public activity, phenomenal difference, inertia, and "
            + "static public equality.",
        H("Public Causal Activity Criterion and Separations"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("public-causal-activity-excludes-dynamic-equivalence"),
                DeclarationHandle.Create(
                    DeclarationPrefix
                        + "public_causal_activity_excludes_dynamic_equivalence"),
                H("Public causal activity excludes dynamic equivalence"),
                StatementSource.FromAuthor(ActivityExclusionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A publicly active pair has an allowed action whose two resulting "
                            + "states receive different public values. Dynamic equivalence "
                            + "would require those values to agree after every allowed action.")),
                    Paragraph(Text(
                        "The action witnessing activity therefore directly contradicts dynamic "
                            + "equivalence. The conclusion is one-way and does not assume that "
                            + "failure of a universal equality supplies a separating action."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("public-dynamic-equivalence-is-public-inertia"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "public_dynamic_equiv_iff_inert"),
                H("Public dynamic equivalence is public inertia"),
                StatementSource.FromAuthor(DynamicInertiaFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Two states are dynamically equivalent exactly when every allowed "
                            + "action leaves their resulting public readouts equal. Thus the "
                            + "dynamic class records complete public inertia across the action "
                            + "family, rather than equality under only one chosen action."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("public-dynamic-equivalence-is-an-equivalence-relation"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "public_dynamic_equiv_is_equivalence"),
                H("Public dynamic equivalence is an equivalence relation"),
                StatementSource.FromAuthor(DynamicEquivalenceRelationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Equality of public outcomes after every allowed action is reflexive "
                            + "and symmetric. If a first state agrees dynamically with a second "
                            + "and the second with a third, pointwise transitivity of equality "
                            + "makes the first and third dynamically equivalent.")),
                    Paragraph(Text(
                        "Consequently the state space is partitioned into public dynamic "
                            + "classes for every intervention family and public readout."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("phenomenal-difference-with-public-inertia"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "phenomenal_difference_with_public_inertia"),
                H("Phenomenal difference can coexist with public inertia"),
                StatementSource.FromAuthor(PhenomenalInertiaWitnessFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For the Boolean zombie pair, the phenomenal readout is the identity "
                            + "and therefore distinguishes false from true. Both coordinates of "
                            + "the joint public readout are constant, so the same pair is a "
                            + "zombie witness.")),
                    Paragraph(Text(
                        "The only allowed intervention preserves the state. The constant public "
                            + "readout therefore remains equal on the pair after intervention, "
                            + "making the pair dynamically equivalent and not publicly active."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("public-activity-with-phenomenal-agreement"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "public_activity_with_phenomenal_agreement"),
                H("Public activity can coexist with phenomenal agreement"),
                StatementSource.FromAuthor(PublicActivityAgreementFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "With the identity public readout and the identity intervention, false "
                            + "and true produce different public values and hence form a publicly "
                            + "active pair.")),
                    Paragraph(Text(
                        "A constant phenomenal readout assigns false to both states. Their "
                            + "phenomenal values agree, so public causal activity does not by "
                            + "itself imply phenomenal difference."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("static-public-equality-with-dynamic-separation"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "static_public_equality_with_dynamic_separation"),
                H("Static public equality can hide dynamic separation"),
                StatementSource.FromAuthor(StaticEqualityDynamicSeparationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The two private Boolean pairs have the same first bit, so the static "
                            + "public readout cannot distinguish them. They differ only in the "
                            + "second, initially hidden bit.")),
                    Paragraph(Text(
                        "The revealing intervention copies that hidden bit into the public first "
                            + "coordinate. Their resulting public values then differ, making the "
                            + "pair publicly active and dynamically inequivalent despite its "
                            + "static public equality."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("public-causal-activity-criterion-and-separations"),
                DeclarationHandle.Create(
                    DeclarationPrefix
                        + "public_causal_activity_criterion_and_separations"),
                H("The public causal activity criterion and all separations hold together"),
                StatementSource.FromAuthor(CriterionAndSeparationsFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The criterion combines the general obstruction from public activity, "
                            + "the pointwise characterization of dynamic inertia, and the "
                            + "equivalence-relation structure of the Boolean zombie dynamics.")),
                    Paragraph(Text(
                        "Its three concrete witnesses then separate the relevant notions in "
                            + "both directions: phenomenal difference can be publicly inert, "
                            + "public activity can leave phenomenal values equal, and static "
                            + "public equality can be broken only after intervention."))),
                DescribeRole.Theorem))));

    private static Formula TypeUniverse() => F.Id("Type");

    private static Formula Concept(Formula state, Formula value) =>
        Call("Concept", state, value);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula ImpliesFormula(Formula hypothesis, Formula conclusion) =>
        new Formula.Logic(hypothesis, FormulaLogicOperator.Implies, conclusion);

    private static Formula IffFormula(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);

    private static Formula Active(
        Formula intervene,
        Formula publicReadout,
        Formula left,
        Formula right) =>
        Call("PubliclyCausallyActive", intervene, publicReadout, left, right);

    private static Formula DynamicEquiv(
        Formula intervene,
        Formula publicReadout,
        Formula left,
        Formula right) =>
        Call("PublicDynamicEquiv", intervene, publicReadout, left, right);

    private static Formula PhenomenallyDifferent(
        Formula phenomenal,
        Formula left,
        Formula right) =>
        Call("PhenomenallyDifferent", phenomenal, left, right);

    private static Formula Pair(Formula first, Formula second) =>
        Call("pair", first, second);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula ActivityExclusion()
    {
        Formula state = F.Id("State");
        Formula action = F.Id("Action");
        Formula publicValue = F.Id("Public");
        Formula intervene = F.Id("intervene");
        Formula publicReadout = F.Id("publicReadout");
        Formula left = F.Id("x");
        Formula right = F.Id("y");

        return new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("State", TypeUniverse()),
                Bound("Action", TypeUniverse()),
                Bound("Public", TypeUniverse()),
                Bound("intervene", Arrow(action, Arrow(state, state))),
                Bound("publicReadout", Concept(state, publicValue)),
                Bound("x", state),
                Bound("y", state),
            ],
            ImpliesFormula(
                Active(intervene, publicReadout, left, right),
                new Formula.Not(DynamicEquiv(intervene, publicReadout, left, right))));
    }

    private static Formula DynamicInertia()
    {
        Formula state = F.Id("State");
        Formula action = F.Id("Action");
        Formula publicValue = F.Id("Public");
        Formula intervene = F.Id("intervene");
        Formula publicReadout = F.Id("publicReadout");
        Formula left = F.Id("x");
        Formula right = F.Id("y");
        Formula actionValue = F.Id("m");
        Formula samePublicResult = Equal(
            Apply(publicReadout, Apply(intervene, actionValue, left)),
            Apply(publicReadout, Apply(intervene, actionValue, right)));

        return new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("State", TypeUniverse()),
                Bound("Action", TypeUniverse()),
                Bound("Public", TypeUniverse()),
                Bound("intervene", Arrow(action, Arrow(state, state))),
                Bound("publicReadout", Concept(state, publicValue)),
                Bound("x", state),
                Bound("y", state),
            ],
            IffFormula(
                DynamicEquiv(intervene, publicReadout, left, right),
                new Formula.Bind(
                    FormulaQuantifier.ForAll,
                    FormulaIdentifier.Create("m"),
                    action,
                    samePublicResult)));
    }

    private static Formula ActivityExclusionFormula() =>
        F.Disp(ActivityExclusion());

    private static Formula DynamicInertiaFormula() =>
        F.Disp(DynamicInertia());

    private static Formula DynamicEquivalenceRelationFormula()
    {
        Formula state = F.Id("State");
        Formula action = F.Id("Action");
        Formula publicValue = F.Id("Public");
        Formula intervene = F.Id("intervene");
        Formula publicReadout = F.Id("publicReadout");

        return F.Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("State", TypeUniverse()),
                Bound("Action", TypeUniverse()),
                Bound("Public", TypeUniverse()),
                Bound("intervene", Arrow(action, Arrow(state, state))),
                Bound("publicReadout", Concept(state, publicValue)),
            ],
            Call(
                "Equivalence",
                Call("PublicDynamicEquiv", intervene, publicReadout))));
    }

    private static Formula PhenomenalInertiaWitness()
    {
        Formula phenomenal = F.Id("zombiePhenomenal");
        Formula publicReadout = F.Id("zombiePublic");
        Formula intervene = F.Id("zombieIntervention");
        Formula left = F.Id("false");
        Formula right = F.Id("true");

        return And(
            Call("ZombieWitness", phenomenal, publicReadout),
            And(
                PhenomenallyDifferent(phenomenal, left, right),
                And(
                    DynamicEquiv(intervene, publicReadout, left, right),
                    new Formula.Not(Active(intervene, publicReadout, left, right)))));
    }

    private static Formula PhenomenalInertiaWitnessFormula() =>
        F.Disp(PhenomenalInertiaWitness());

    private static Formula PublicActivityAgreement()
    {
        Formula intervene = F.Id("zombieIntervention");
        Formula publicReadout = F.Id("identityPublic");
        Formula phenomenal = F.Id("constantPhenomenal");
        Formula left = F.Id("false");
        Formula right = F.Id("true");

        return And(
            Active(intervene, publicReadout, left, right),
            And(
                Equal(Apply(phenomenal, left), Apply(phenomenal, right)),
                new Formula.Not(PhenomenallyDifferent(phenomenal, left, right))));
    }

    private static Formula PublicActivityAgreementFormula() =>
        F.Disp(PublicActivityAgreement());

    private static Formula StaticEqualityDynamicSeparation()
    {
        Formula publicReadout = F.Id("hiddenBitPublic");
        Formula intervene = F.Id("revealHiddenBit");
        Formula left = Pair(F.Id("false"), F.Id("false"));
        Formula right = Pair(F.Id("false"), F.Id("true"));

        return And(
            Equal(Apply(publicReadout, left), Apply(publicReadout, right)),
            And(
                Active(intervene, publicReadout, left, right),
                new Formula.Not(DynamicEquiv(intervene, publicReadout, left, right))));
    }

    private static Formula StaticEqualityDynamicSeparationFormula() =>
        F.Disp(StaticEqualityDynamicSeparation());

    private static Formula CriterionAndSeparationsFormula()
    {
        Formula zombieEquivalence = Call(
            "Equivalence",
            Call(
                "PublicDynamicEquiv",
                F.Id("zombieIntervention"),
                F.Id("zombiePublic")));

        return F.Disp(And(
            ActivityExclusion(),
            And(
                DynamicInertia(),
                And(
                    zombieEquivalence,
                    And(
                        PhenomenalInertiaWitness(),
                        And(
                            PublicActivityAgreement(),
                            StaticEqualityDynamicSeparation()))))));
    }
}
