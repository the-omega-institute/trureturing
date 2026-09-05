using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscapeRealizations;

internal sealed class EndStateOmitsPreemptingCauseDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/InformationEscapeRealizations/EndStateOmitsPreemptingCause.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Endpoint and active-cause readouts realize the five-class preemption kernel.",
        H("End State Omits Preempting Cause Realization"),
        Blocks(
            DefinitionNode("end-state-preemption-realization-definition",
                "endStateOmitsPreemptingCauseRealization", "Concrete preemption realization",
                "The realization supplies endpoint, active-cause, ordered-preemption, and named-anchor data."),
            TheoremNode("end-state-preemption-realization",
                "end_state_omits_preempting_cause_realization",
                "Preemption realization equivalence", RealizationFormula(),
                "Both directions encode or decode every clause of the frozen preemption statement."),
            TheoremNode("end-state-preemption-partition-count",
                "end_state_omits_preempting_cause_partition_count",
                "Five kernel classes", PartitionFormula(),
                "The concrete six-component image of all preemption traces has five elements."),
            TheoremNode("end-state-preemption-private-pair",
                "end_state_omits_preempting_cause_private_pair",
                "Private trace separation", PrivatePairFormula(),
                "The compiled primitive bundle separates the two named traces."))));

    private static DocumentBlock.Describe DefinitionNode(
        string id, string declaration, string title, string explanation) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(explanation))), DescribeRole.Definition);

    private static DocumentBlock.Describe TheoremNode(
        string id, string declaration, string title, Formula statement, string explanation) =>
        Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(statement), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(explanation))), DescribeRole.Theorem);

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Tuple(params Formula[] entries)
    {
        var items = new List<Formula> { Open };
        for (var index = 0; index < entries.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(entries[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Ordered(Formula trace, Formula first, Formula delayed) =>
        Call("IsOrderedPreemption", trace, first, delayed);

    private static Formula FrozenStatement()
    {
        Formula aThenB = F.Id("aThenB");
        Formula bThenA = F.Id("bThenA");
        Formula shooterA = F.Id("shooterA");
        Formula shooterB = F.Id("shooterB");
        Formula recover = F.Id("recover");
        Formula recoverType = Seq(F.Id("Bool"), Sp, To, Sp,
            Call("Option", F.Id("Mechanism")));
        Formula noRecovery = new Formula.Not(Grp(Seq(
            Exists, Sp, recover, Colon, Sp, recoverType, Comma, Sp,
            F.Id("activeCause"), Sp, Eq, Sp, recover, Sp, Circ, Sp, F.Id("endState"))));
        return Seq(
            Ordered(aThenB, shooterA, shooterB), Sp, Land, Sp,
            Ordered(bThenA, shooterB, shooterA), Sp, Land, Sp,
            Call("endState", aThenB), Sp, Eq, Sp, Call("endState", bThenA), Sp, Land, Sp,
            Call("activeCause", aThenB), Sp, Neq, Sp, Call("activeCause", bThenA), Sp,
            Land, Sp, noRecovery);
    }

    private static Formula RealizationFormula() => Disp(Seq(
        FrozenStatement(), Sp, Iff, Sp,
        F.Id("endStateOmitsPreemptingCauseArena"), Dot, F.Id("Law"), Sp,
        F.Id("endStateOmitsPreemptingCauseRealization"), Dot));

    private static Formula PartitionFormula()
    {
        Formula trace = F.Id("trace");
        Formula shooterA = F.Id("shooterA");
        Formula shooterB = F.Id("shooterB");
        Formula signature = Tuple(
            Call("endState", trace),
            Call("activeCause", trace),
            Call("decide", Ordered(trace, shooterA, shooterB)),
            Call("decide", Ordered(trace, shooterB, shooterA)),
            Call("decide", Seq(trace, Sp, Eq, Sp, F.Id("aThenB"))),
            Call("decide", Seq(trace, Sp, Eq, Sp, F.Id("bThenA"))));
        Formula image = Seq(
            F.Id("Finset"), Dot, F.Id("univ"), Dot, F.Id("image"), Open,
            LambdaLower, Sp, trace, Colon, Sp, F.Id("PreemptionTrace"), Comma, Sp,
            signature, Close);
        return Disp(Seq(Open, image, Close, Dot, F.Id("card"), Sp, Eq, Sp, D(5), Dot));
    }

    private static Formula PrivatePairFormula() => Disp(Seq(
        new Formula.Not(Grp(Seq(
            F.Id("endStateOmitsPreemptingCauseRealization"), Dot,
            F.Id("toPrimitiveBundle"), Dot, F.Id("agrees"), Sp,
            F.Id("aThenB"), Sp, F.Id("bThenA")))), Dot));
}
