using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Control;

internal sealed class MaximalSafeControllableDomainDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Control/MaximalSafeControllableDomain."
            + "maximal_safe_controllable_domain";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The semantic indefinitely safe domain is the greatest controlled-safe fixed point.",
        H("Maximal Safe Controllable Domain"),
        Blocks(Describe.Lean(
            DescribeId.Create("maximal-safe-controllable-domain"),
            DeclarationHandle.Create(Declaration),
            H("The indefinitely safe domain is the greatest fixed point"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "A control system supplies a state-dependent action type and a nonempty "
                        + "successor set for every available action. The controlled predecessor "
                        + "uses existential action choice and universal successor containment.")),
                Paragraph(Text(
                    "The indefinitely safe set is constructed semantically: a state must lie "
                        + "in some subset of the safe states that offers a confining action at "
                        + "each of its states. It is not defined as a fixed point.")),
                Paragraph(Text(
                    "Independently, the displayed monotone operator intersects the safe set with "
                        + "the canonical controlled predecessor. Knaster-Tarski identifies its "
                        + "greatest fixed point with the semantic indefinitely safe set.")),
                Paragraph(Text(
                    "The remaining public clauses expose the confining action, indefinite-safety "
                        + "inclusion, and converse maximality. Repository searches found no exact "
                        + "theorem; Mathlib's greatest-fixed-point laws are applied directly."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula type = F.Id("Type");
        Formula stateType = F.Id("X");
        Formula system = F.Id("system");
        Formula safe = F.Id("S");
        Formula stateSet = Call("Set", stateType);
        Formula domain = F.Id("K");
        Formula safetyOperator = F.Id("F");
        Formula foreverSafe = F.Id("Kstar");
        Formula state = F.Id("x");
        Formula current = F.Id("y");
        Formula action = F.Id("u");
        Formula invariant = F.Id("I");
        Formula operatorType = Call("OrderHom", stateSet, stateSet);
        Formula operatorDefinition = F.Seq(
            F.Operatorname, F.Grp(F.Id("let")), F.Sp, safetyOperator,
            F.Sp, F.Colon, F.Sp, operatorType, F.Sp, F.Colon, F.Eq, F.Sp,
            domain, F.Sp, F.Mapsto, F.Sp,
            Call("intersect", safe, Call("CPre", system, domain)),
            F.Semi, F.RowBreak, F.Grp());
        Formula currentControlled = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("y"),
            invariant,
            new Formula.Bind(
                FormulaQuantifier.Exists,
                FormulaIdentifier.Create("u"),
                Call("Action", system, current),
                Relation(
                    Call("successor", system, current, action),
                    FormulaRelationOperator.SubsetOf,
                    invariant)));
        Formula invariantWitness = new Formula.Bind(
            FormulaQuantifier.Exists,
            FormulaIdentifier.Create("I"),
            stateSet,
            And(
                Relation(state, FormulaRelationOperator.MemberOf, invariant),
                And(
                    Relation(invariant, FormulaRelationOperator.SubsetOf, safe),
                    currentControlled)));
        Formula foreverSet = F.Seq(
            F.OpenBrace, state, F.Sp, F.InMacro, F.Sp, stateType,
            F.Sp, F.Mid, F.Sp, invariantWitness, F.CloseBrace);
        Formula foreverDefinition = F.Seq(
            F.Operatorname, F.Grp(F.Id("let")), F.Sp, foreverSafe,
            F.Sp, F.Colon, F.Sp, stateSet, F.Sp, F.Colon, F.Eq, F.Sp,
            foreverSet, F.Semi, F.RowBreak, F.Grp());
        Formula greatest = Call("gfp", safetyOperator);
        Formula hasSafeAction = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("x"),
            greatest,
            new Formula.Bind(
                FormulaQuantifier.Exists,
                FormulaIdentifier.Create("u"),
                Call("Action", system, state),
                Relation(
                    Call("successor", system, state, action),
                    FormulaRelationOperator.SubsetOf,
                    greatest)));
        Formula conclusion = And(
            Relation(foreverSafe, FormulaRelationOperator.Equal, greatest),
            And(
                hasSafeAction,
                And(
                    Relation(greatest, FormulaRelationOperator.SubsetOf, foreverSafe),
                    Relation(foreverSafe, FormulaRelationOperator.SubsetOf, greatest))));
        Formula inputs = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("system", Call("ControlSystem", stateType)),
                Bound("S", stateSet),
            ],
            F.Seq(operatorDefinition, foreverDefinition, conclusion));

        return F.Disp(new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("X"),
            type,
            inputs));
    }

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Relation(
        Formula left,
        FormulaRelationOperator operation,
        Formula right) => new Formula.Relation(left, operation, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
}
