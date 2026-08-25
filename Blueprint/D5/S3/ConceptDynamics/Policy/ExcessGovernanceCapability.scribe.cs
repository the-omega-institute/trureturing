using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Policy;

internal sealed class ExcessGovernanceCapabilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A higher readout can add policy capability although a lower readout already suffices "
            + "for the target.",
        H("Excess Governance Capability"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("excess-governance-capability-without-target-need"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Policy/ExcessGovernanceCapability."
                        + "excess_governance_capability_without_target_need"),
                H("Higher governance can add power without adding target necessity"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The target, lower readout, higher readout, states, and actions are "
                            + "independent source primitives. The lower readout is publicly "
                            + "assumed already sufficient for the target, while the higher "
                            + "readout refines it.")),
                    Paragraph(Text(
                        "A public pair of states records the extra distinction: the lower "
                            + "readout identifies the pair and the higher readout separates it. "
                            + "Two distinct actions make that distinction operational.")),
                    Paragraph(Text(
                        "Refinement composition preserves target sufficiency at the higher "
                            + "readout. Policy monotonicity includes every lower policy in the "
                            + "higher capability, while strict policy growth constructs a "
                            + "higher-only policy that distinguishes the pair and proves all "
                            + "lower policies identify it.")),
                    Paragraph(Text(
                        "All three proof components are exact repository hits and are applied "
                            + "directly; no sibling capability, refinement, or target object is "
                            + "redeclared."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        Seq(domain, Sp, To, Sp, codomain);

    private static Formula Capability(Formula readout, Formula actions) =>
        Call("policyCapability", readout, actions);

    private static Formula TheoremFormula()
    {
        Formula state = F.Id("X");
        Formula targetValue = F.Id("T");
        Formula lowerValue = F.Id("C");
        Formula higherValue = F.Id("D");
        Formula action = F.Id("U");
        Formula target = F.Id("target");
        Formula lower = F.Id("lower");
        Formula higher = F.Id("higher");
        Formula left = F.Id("x");
        Formula right = F.Id("y");
        Formula firstAction = F.Id("u0");
        Formula secondAction = F.Id("u1");
        Formula policy = F.Id("p");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula policyType = Arrow(state, action);
        Formula lowerCapability = Capability(lower, action);
        Formula higherCapability = Capability(higher, action);

        Formula extraDistinction = Seq(
            Apply(lower, left), Sp, Eq, Sp, Apply(lower, right), Sp, Land, Sp,
            Apply(higher, left), Sp, Neq, Sp, Apply(higher, right));
        Formula distinctActions = Seq(
            Exists, Sp, firstAction, Comma, Sp, secondAction,
            Colon, Sp, action, Comma, Sp,
            firstAction, Sp, Neq, Sp, secondAction);
        Formula premise = Seq(
            Call("Refines", target, lower), Sp, Land, Sp,
            Call("Refines", lower, higher), Sp, Land, RowBreak, Grp(),
            Grp(extraDistinction), Sp, Land, Sp, Grp(distinctActions));
        Formula newPolicy = Seq(
            Exists, Sp, policy, Colon, Sp, policyType, Comma, Sp,
            policy, Sp, InMacro, Sp, higherCapability, Sp, Land, Sp,
            Neg, Grp(policy, Sp, InMacro, Sp, lowerCapability), Sp, Land, Sp,
            Apply(policy, left), Sp, Neq, Sp, Apply(policy, right));
        Formula lowerCannotSeparate = Seq(
            Forall, Sp, policy, Colon, Sp, policyType, Comma, Sp,
            policy, Sp, InMacro, Sp, lowerCapability, Sp, Rightarrow, Sp,
            Apply(policy, left), Sp, Eq, Sp, Apply(policy, right));
        Formula conclusion = Seq(
            Call("Refines", target, higher), Sp, Land, RowBreak, Grp(),
            lowerCapability, Sp, Subseteq, Sp, higherCapability, Sp, Land,
            RowBreak, Grp(), Grp(newPolicy), Sp, Land, RowBreak, Grp(),
            Grp(lowerCannotSeparate));

        return Disp(Seq(
            Forall, Sp, state, Comma, Sp, targetValue, Comma, Sp, lowerValue,
            Comma, Sp, higherValue, Comma, Sp, action,
            Colon, Sp, type, Comma, RowBreak, Grp(),
            target, Colon, Sp, Arrow(state, targetValue), Comma, Sp,
            lower, Colon, Sp, Arrow(state, lowerValue), Comma, Sp,
            higher, Colon, Sp, Arrow(state, higherValue), Comma, RowBreak, Grp(),
            left, Comma, Sp, right, Colon, Sp, state, Comma, RowBreak, Grp(),
            Grp(premise), Sp, Rightarrow, RowBreak, Grp(), Grp(conclusion), Dot));
    }
}
