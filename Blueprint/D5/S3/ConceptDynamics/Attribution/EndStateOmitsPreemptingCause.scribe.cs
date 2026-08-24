using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Attribution;

internal sealed class EndStateOmitsPreemptingCauseDocument : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/ConceptDynamics/Attribution/EndStateOmitsPreemptingCause.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Reversing trigger order preserves the endpoint while changing the active cause; "
            + "first-trigger provenance restores recovery.",
        H("End States Omit Preempting Causes"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("end-state-omits-preempting-cause"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "end_state_omits_preempting_cause"),
                H("An end state does not determine the preempting cause"),
                StatementSource.FromAuthor(EndStateOmissionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "In one two-step history, A triggers before B; in the reversed history, "
                            + "B triggers before A. Each history is an ordered preemption and "
                            + "reaches the same endpoint, but its first trigger, hence its active "
                            + "cause, is different.")),
                    Paragraph(Text(
                        "Because the endpoint readout assigns the same value to histories with "
                            + "different active causes, no decoder from that endpoint alone can "
                            + "recover the active cause. The obstruction is loss of event order, "
                            + "not failure of either history to produce the outcome."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("active-cause-factors-through-provenance"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "active_cause_factors_through_provenance"),
                H("First-trigger provenance restores active-cause recovery"),
                StatementSource.FromAuthor(ProvenanceRecoveryFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Refine the endpoint by recording the first trigger alongside the final "
                        + "outcome. The active cause is exactly this first-trigger component, so "
                        + "projecting the refined readout onto that component recovers the cause "
                        + "for every trace."))),
                DescribeRole.Lemma))));

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Compose(Formula outer, Formula inner) =>
        Seq(outer, Sp, Circ, Sp, inner);

    private static Formula EndStateOmissionFormula()
    {
        Formula firstTrace = F.Id("aThenB");
        Formula secondTrace = F.Id("bThenA");
        Formula firstMechanism = F.Id("shooterA");
        Formula secondMechanism = F.Id("shooterB");
        Formula activeCause = F.Id("activeCause");
        Formula endState = F.Id("endState");
        Formula recover = F.Id("recover");
        Formula optionMechanism = Call("Option", F.Id("Mechanism"));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Call("IsOrderedPreemption", firstTrace, firstMechanism, secondMechanism),
            Sp, Land, RowBreak, Grp(),
            Call("IsOrderedPreemption", secondTrace, secondMechanism, firstMechanism),
            Sp, Land, RowBreak, Grp(),
            Call("endState", firstTrace), Sp, Eq, Sp, Call("endState", secondTrace),
            Sp, Land, RowBreak, Grp(),
            Call("activeCause", firstTrace), Sp, Neq, Sp,
            Call("activeCause", secondTrace),
            Sp, Land, RowBreak, Grp(),
            Neg, Sp, Exists, Sp, recover, Colon, Sp,
            Arrow(F.Id("Bool"), optionMechanism), Comma, Sp,
            activeCause, Sp, Eq, Sp, Compose(recover, endState), Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula ProvenanceRecoveryFormula()
    {
        Formula recover = F.Id("recover");
        Formula optionMechanism = Call("Option", F.Id("Mechanism"));
        Formula provenance = Seq(F.Id("Bool"), Sp, Times, Sp, optionMechanism);

        return Disp(Seq(
            Exists, Sp, recover, Colon, Sp,
            Arrow(provenance, optionMechanism), Comma, Sp,
            F.Id("activeCause"), Sp, Eq, Sp,
            Compose(recover, F.Id("provenanceReadout")), Dot));
    }
}
