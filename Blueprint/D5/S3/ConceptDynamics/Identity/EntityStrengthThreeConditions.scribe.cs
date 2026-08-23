using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Identity;

internal sealed class EntityStrengthThreeConditionsDocument : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Identity/EntityStrengthThreeConditions.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Process stability, target fidelity, and nontrivial resolution are independent yet "
            + "jointly realizable.",
        H("Three Conditions of Entity Strength"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("entity-strength-conditions-are-independent"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "three_conditions_are_independent"),
                H("The three entity-strength conditions are independent"),
                StatementSource.FromAuthor(IndependenceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "None of process stability, target fidelity, and nontrivial resolution "
                            + "follows from the other two. Three explicit concepts witness the "
                            + "three missing implications.")),
                    Paragraph(Text(
                        "A constant Boolean-to-Unit concept is stable under every process and "
                            + "faithful to a constant target, but it distinguishes no states. "
                            + "On a Boolean pair, the first-coordinate concept is stable under "
                            + "all processes that preserve that coordinate and has nontrivial "
                            + "resolution, but it cannot recover the second-coordinate target.")),
                    Paragraph(Text(
                        "Finally, the identity concept on Bool is faithful to the identity target "
                            + "and distinguishes false from true, while Boolean negation is an "
                            + "allowed process that violates stability."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("entity-strength-conditions-are-jointly-realizable"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "three_conditions_jointly_realizable"),
                H("The three entity-strength conditions are jointly realizable"),
                StatementSource.FromAuthor(JointRealizabilityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Reading the first coordinate of a Boolean pair satisfies all three "
                            + "conditions when the designated processes are exactly those that "
                            + "preserve that coordinate.")),
                    Paragraph(Text(
                        "Preservation gives process stability directly, using the same first-"
                            + "coordinate readout as the target gives fidelity through the "
                            + "identity decoder, and pairs with different first coordinates "
                            + "supply nontrivial resolution."))),
                DescribeRole.Lemma))));

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula ProcessSet(Formula source) =>
        Call("Set", Arrow(source, source));

    private static Formula Stable(Formula processes, Formula concept) =>
        Call("ProcessStable", processes, concept);

    private static Formula Faithful(Formula target, Formula concept) =>
        Call("TargetFaithful", target, concept);

    private static Formula Resolved(Formula concept) =>
        Call("NontrivialResolution", concept);

    private static Formula IndependenceFormula()
    {
        Formula boolean = F.Id("Bool");
        Formula unit = F.Id("Unit");
        Formula pair = Seq(boolean, Sp, Times, Sp, boolean);

        Formula conceptOne = F.Id("c1");
        Formula targetOne = F.Id("t1");
        Formula processesOne = F.Id("P1");
        Formula stableFaithfulTrivial = new Formula.BindMany(
            FormulaQuantifier.Exists,
            [
                Bound("c1", Arrow(boolean, unit)),
                Bound("t1", Arrow(boolean, unit)),
                Bound("P1", ProcessSet(boolean)),
            ],
            And(
                Stable(processesOne, conceptOne),
                And(
                    Faithful(targetOne, conceptOne),
                    new Formula.Not(Resolved(conceptOne)))));

        Formula conceptTwo = F.Id("c2");
        Formula targetTwo = F.Id("t2");
        Formula processesTwo = F.Id("P2");
        Formula stableResolvedUnfaithful = new Formula.BindMany(
            FormulaQuantifier.Exists,
            [
                Bound("c2", Arrow(pair, boolean)),
                Bound("t2", Arrow(pair, boolean)),
                Bound("P2", ProcessSet(pair)),
            ],
            And(
                Stable(processesTwo, conceptTwo),
                And(
                    Resolved(conceptTwo),
                    new Formula.Not(Faithful(targetTwo, conceptTwo)))));

        Formula conceptThree = F.Id("c3");
        Formula targetThree = F.Id("t3");
        Formula processesThree = F.Id("P3");
        Formula faithfulResolvedUnstable = new Formula.BindMany(
            FormulaQuantifier.Exists,
            [
                Bound("c3", Arrow(boolean, boolean)),
                Bound("t3", Arrow(boolean, boolean)),
                Bound("P3", ProcessSet(boolean)),
            ],
            And(
                Faithful(targetThree, conceptThree),
                And(
                    Resolved(conceptThree),
                    new Formula.Not(Stable(processesThree, conceptThree)))));

        return Disp(And(
            stableFaithfulTrivial,
            And(stableResolvedUnfaithful, faithfulResolvedUnstable)));
    }

    private static Formula JointRealizabilityFormula()
    {
        Formula boolean = F.Id("Bool");
        Formula pair = Seq(boolean, Sp, Times, Sp, boolean);
        Formula concept = F.Id("c");
        Formula target = F.Id("t");
        Formula processes = F.Id("P");

        return Disp(new Formula.BindMany(
            FormulaQuantifier.Exists,
            [
                Bound("c", Arrow(pair, boolean)),
                Bound("t", Arrow(pair, boolean)),
                Bound("P", ProcessSet(pair)),
            ],
            And(
                Stable(processes, concept),
                And(
                    Faithful(target, concept),
                    Resolved(concept)))));
    }
}
