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
            Arena("agenda-power-arena", "agendaPowerArena",
                "Agenda power arena", "Agenda", "AgendaPowerLaw"),
            Arena("adaptive-residue-arena", "residueArena",
                "Adaptive residue arena", "ResidueState", "ResidueLaw"),
            Arena("spectrum-atom-arena", "spectrumArena",
                "Spectrum atom arena", "SpectrumAtom", "BijectiveIndexLaw"))));

    private static DocumentBlock Arena(
        string id, string declaration, string title, string state, string law) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.FromAuthor(Disp(Call("PrimitiveLawArena", F.Id(state), F.Id(law)))),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "The finite carrier, typed primitive signature, and realization-dependent law "
                    + "are packaged for the information-escape engine."))),
            DescribeRole.Definition);

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
