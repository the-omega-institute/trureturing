using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscapeArenas;

internal sealed class FirstThreeArenasDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/InformationEscapeArenas/FirstThreeArenas.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite typed arenas for agenda power, adaptive residues, and spectrum atoms.",
        H("First Three Information-Escape Arenas"),
        Blocks(
            DefinitionNode("agenda-fintype", "agendaFintype", "Agenda finite instance",
                "A finite instance obtained through a private equivalence."),
            DefinitionNode("agenda-readout", "AgendaReadout", "Agenda readout indices",
                "The readout index type separates the sequential winner from agenda validity."),
            DefinitionNode("agenda-power-signature", "agendaPowerSignature",
                "Agenda power signature",
                "The typed signature assigns a three-valued winner output and a Boolean validity output to the agenda carrier."),
            DefinitionNode("agenda-power-arena", "agendaPowerArena", "Agenda power arena",
                "The arena packages the finite Agenda state, agendaPowerSignature, and the realization law asserting all winners plus a separating valid pair."),
            NondegenerateNode("agenda-power-arena-nondegenerate", "agendaPowerArena"),
            DefinitionNode("adaptive-depth-for", "adaptiveDepthFor", "Adaptive depth",
                "The noncomputable depth helper selects the least exact adaptive depth when one exists and returns zero otherwise."),
            DefinitionNode("static-depth-for", "staticDepthFor", "Static depth",
                "The noncomputable depth helper selects the least exact static cardinality when one exists and returns zero otherwise."),
            DefinitionNode("residue-signature", "residueSignature", "Residue signature",
                "The typed signature exposes each residue sensor as a Boolean CUT readout on ResidueState."),
            DefinitionNode("residue-arena", "residueArena", "Adaptive residue arena",
                "The arena packages the residue readouts, their exact fibers, an injective two-step protocol, the lower bounds, and the adaptive-versus-static depth comparison."),
            NondegenerateNode("residue-arena-nondegenerate", "residueArena"),
            DefinitionNode("spectrum-signature", "spectrumSignature", "Spectrum signature",
                "The typed signature exposes the spectrum atom index as one five-valued CUT readout."),
            DefinitionNode("spectrum-arena", "spectrumArena", "Spectrum atom arena",
                "The arena packages SpectrumAtom with the signature and requires the sole readout to be bijective."),
            NondegenerateNode("spectrum-arena-nondegenerate", "spectrumArena"))));

    private static DocumentBlock.Describe DefinitionNode(
        string id, string declaration, string title, string paragraph) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(paragraph))),
            DescribeRole.Definition);

    private static DocumentBlock.Describe NondegenerateNode(string id, string arena) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + arena + "_nondegenerate"),
            H("The " + arena + " state space is nondegenerate"),
            StatementSource.FromAuthor(Disp(Seq(
                Operatorname, Grp(F.Id("Nondegenerate")), Open,
                Operatorname, Grp(F.Id("toArena")), Open, F.Id(arena), Close,
                Close))),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "The finite arena contains at least two distinct states."))),
            DescribeRole.Theorem);
}
