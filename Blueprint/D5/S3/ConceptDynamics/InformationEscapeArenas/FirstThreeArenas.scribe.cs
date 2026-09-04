using static StrataLint.Scribe.DefinitionDsl;

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
            DefinitionNode("adaptive-depth-for", "adaptiveDepthFor", "Adaptive depth",
                "The noncomputable depth helper selects the least exact adaptive depth when one exists and returns zero otherwise."),
            DefinitionNode("static-depth-for", "staticDepthFor", "Static depth",
                "The noncomputable depth helper selects the least exact static cardinality when one exists and returns zero otherwise."),
            DefinitionNode("residue-signature", "residueSignature", "Residue signature",
                "The typed signature exposes each residue sensor as a Boolean CUT readout on ResidueState."),
            DefinitionNode("residue-arena", "residueArena", "Adaptive residue arena",
                "The arena packages the residue readouts, their exact fibers, an injective two-step protocol, the lower bounds, and the adaptive-versus-static depth comparison."),
            DefinitionNode("spectrum-signature", "spectrumSignature", "Spectrum signature",
                "The typed signature exposes the spectrum atom index as one five-valued CUT readout."),
            DefinitionNode("spectrum-arena", "spectrumArena", "Spectrum atom arena",
                "The arena packages SpectrumAtom with the signature and requires the sole readout to be bijective."))));

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
}
