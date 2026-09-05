using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscapeCounting;

internal sealed class EnumerationsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Explicit arena lists and executable censuses exercise the fused counter.",
        H("Fused Counting Enumerations"),
        Blocks(
            Paragraph(Text(
                "The eleven witnesses are authored Example nodes because DeclarationHandle " +
                    "resolves only the final declaration suffix and cannot bind eleven " +
                    "declarations all named __state_enumeration.")),
            Enumeration("agenda-state-enumeration", "Agenda-power state enumeration",
                "FirstThreeArenas.agendaPowerArena", "agendaPowerArena"),
            Enumeration("residue-state-enumeration", "Adaptive-residue state enumeration",
                "FirstThreeArenas.residueArena", "residueArena"),
            Enumeration("spectrum-state-enumeration", "Spectrum state enumeration",
                "FirstThreeArenas.spectrumArena", "spectrumArena"),
            Enumeration("context-state-enumeration", "Interpretation-context state enumeration",
                "FourthFifthArenas.contextArena", "contextArena"),
            Enumeration("intervention-state-enumeration", "Intervention state enumeration",
                "FourthFifthArenas.interventionArena", "interventionArena"),
            Enumeration("observation-state-enumeration",
                "Observation-intervention state enumeration",
                "ObservationIntervention.observationInterventionArena",
                "observationInterventionArena"),
            Enumeration("static-state-enumeration", "Static-experiment state enumeration",
                "StaticExactExperimentDesign.staticExactExperimentArena",
                "staticExactExperimentArena"),
            Enumeration("completion-state-enumeration", "Commuting-completion state enumeration",
                "CommutingCompletionExchange.commutingCompletionArena",
                "commutingCompletionArena"),
            Enumeration("gluing-state-enumeration", "Local-law-gluing state enumeration",
                "LocalLawGluingObstruction.localLawGluingArena", "localLawGluingArena"),
            Enumeration("preemption-state-enumeration", "Preemption-trace state enumeration",
                "EndStateOmitsPreemptingCause.endStateOmitsPreemptingCauseArena",
                "endStateOmitsPreemptingCauseArena"),
            Enumeration("system-state-enumeration", "SYSTEM stage enumeration",
                "SystemUnit.arena", "arena"),
            Census("singleton-censuses", "Eleven fused singleton censuses",
                "The unique counts are 570, 12, 20, 56, 240, 968, 6, 12, 48, 60, and 2."),
            Census("two-theorem-census", "Two-theorem Bool-pair census",
                "The jointly faithful two-index catalog has full zero and unique counts 4/4."))));

    private static DocumentBlock.Describe Enumeration(
        string id, string title, string owner, string arena) =>
        Describe.Example(
            DescribeId.Create(id), H(title),
            Seq(F.Id("stateEnumeration"), Colon, Sp,
                Call("StateEnumeration", F.Id(arena))),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                owner + ".__state_enumeration supplies an explicit duplicate-free complete " +
                    "state list."))));

    private static DocumentBlock.Describe Census(string id, string title, string paragraph) =>
        Describe.Example(
            DescribeId.Create(id), H(title), F.Id("kernelDecide"),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(paragraph))));

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
}
