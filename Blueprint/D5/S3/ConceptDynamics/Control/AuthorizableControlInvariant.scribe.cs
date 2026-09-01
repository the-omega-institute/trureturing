using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Control;

internal sealed class AuthorizableControlInvariantDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/ConceptDynamics/Control/AuthorizableControlInvariant."
            + "authorizable_control_dynamic_invariant";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Componentwise preservation makes authorizable future control dynamically invariant.",
        H("Authorizable Control Invariant"),
        Blocks(Describe.Lean(
            DescribeId.Create("authorizable-control-dynamic-invariant"),
            DeclarationHandle.Create(Declaration),
            H("The joint autonomy core is invariant under every finite update"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The autonomy core is the intersection of viability, liveness, "
                        + "recoverability, observation-rate adequacy, causal control, "
                        + "provenance, identity correction, revision governance, and "
                        + "expandability.")),
                Paragraph(Text(
                    "Each premise says that one closed-loop update maps one named condition "
                        + "back into itself. The standard intersection law combines those "
                        + "premises into preservation of the full autonomy core.")),
                Paragraph(Text(
                    "The standard finite-iteration law then transports the combined invariant "
                        + "through every natural-number time horizon. The theorem does not "
                        + "assert libertarian branching or supply domain-specific dynamics."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula stateType = F.Id("X");
        Formula step = F.Id("F");
        Formula viability = F.Id("V");
        Formula liveness = F.Id("L");
        Formula recoverability = F.Id("R");
        Formula observation = F.Id("O");
        Formula causalControl = F.Id("C");
        Formula provenance = F.Id("P");
        Formula identity = F.Id("I");
        Formula governance = F.Id("G");
        Formula expandability = F.Id("E");
        Formula time = F.Id("n");
        Formula stateSet = Call("Set", stateType);
        Formula core = Call(
            "Core",
            viability,
            liveness,
            recoverability,
            observation,
            causalControl,
            provenance,
            identity,
            governance,
            expandability);
        Formula premises = And(
            Preserves(step, viability),
            And(
                Preserves(step, liveness),
                And(
                    Preserves(step, recoverability),
                    And(
                        Preserves(step, observation),
                        And(
                            Preserves(step, causalControl),
                            And(
                                Preserves(step, provenance),
                                And(
                                    Preserves(step, identity),
                                    And(
                                        Preserves(step, governance),
                                        Preserves(step, expandability)))))))));
        Formula conclusion = new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("n"),
            F.Id("Nat"),
            Call("MapsTo", Call("iterate", step, time), core, core));
        Formula theorem = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("F", Arrow(stateType, stateType)),
                Bound("V", stateSet),
                Bound("L", stateSet),
                Bound("R", stateSet),
                Bound("O", stateSet),
                Bound("C", stateSet),
                Bound("P", stateSet),
                Bound("I", stateSet),
                Bound("G", stateSet),
                Bound("E", stateSet),
            ],
            F.Seq(premises, F.Sp, F.Rightarrow, F.Sp, conclusion));

        return F.Disp(new Formula.Bind(
            FormulaQuantifier.ForAll,
            FormulaIdentifier.Create("X"),
            F.Id("Type"),
            theorem));
    }

    private static Formula Preserves(Formula step, Formula condition) =>
        Call("MapsTo", step, condition, condition);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Arrow(Formula source, Formula target) =>
        F.Seq(source, F.Sp, F.To, F.Sp, target);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
}
