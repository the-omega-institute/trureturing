using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics;

internal sealed class PolicyCapabilityMonotonicityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Refining a readout enlarges its implementable policy set.",
        H("Policy Capability Monotonicity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("policy-capability-monotonicity"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/PolicyCapabilityMonotonicity.policy_capability_monotone"),
                H("Policy capability is monotone under refinement"),
                StatementSource.FromAuthor(MonotonicityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The policy-capability set of a readout consists of all state-level "
                            + "actions obtained by composing the readout with a decision rule.")),
                    Paragraph(Text(
                        "A refinement factor recovers the coarse value from the fine value. "
                            + "Precomposing every coarse decision rule with that factor gives "
                            + "the stated inclusion of policy-capability sets."))),
                DescribeRole.Theorem))));

    private static Formula Refines(Formula coarse, Formula fine) =>
        Call("Refines", coarse, fine);

    private static Formula Capability(Formula readout, Formula action) =>
        Call("policyCapability", readout, action);

    private static Formula MonotonicityFormula()
    {
        Formula source = F.Id("X");
        Formula coarse = F.Id("C");
        Formula fine = F.Id("D");
        Formula action = F.Id("U");
        Formula readoutC = Subscript(F.Id("q"), coarse);
        Formula readoutD = Subscript(F.Id("q"), fine);
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula readout(Formula codomain) => Seq(source, Sp, To, Sp, codomain);

        return Disp(Seq(
            Forall, Sp, source, Comma, Sp, coarse, Comma, Sp, fine, Comma, Sp,
            action, Colon, Sp, type, Comma, Sp,
            readoutC, Colon, Sp, readout(coarse), Comma, Sp,
            readoutD, Colon, Sp, readout(fine), Comma, Esc,
            Refines(readoutC, readoutD), Sp, Rightarrow, Sp,
            Capability(readoutC, action), Sp, Subseteq, Sp,
            Capability(readoutD, action), Dot));
    }

    private static Formula Subscript(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));
}
