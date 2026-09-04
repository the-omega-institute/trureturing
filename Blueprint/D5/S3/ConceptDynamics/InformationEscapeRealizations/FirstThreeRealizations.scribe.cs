using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscapeRealizations;

internal sealed class FirstThreeRealizationsDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/InformationEscapeRealizations/FirstThreeRealizations.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The first three frozen statements are equivalent to their realization laws.",
        H("First Three Legacy Primitive Realizations"),
        Blocks(
            Realization("agenda-power-realization",
                "agenda_power_realization", "Agenda power realization",
                "agendaPowerArena", "agendaPowerStatement", "agendaPowerRealization"),
            Realization("adaptive-residue-realization",
                "two_step_adaptive_residue_identification_realization",
                "Adaptive residue realization", "residueArena",
                "twoStepAdaptiveResidueIdentification", "residueRealization"),
            Realization("spectrum-index-realization",
                "spectrum_atom_index_bijective_realization",
                "Spectrum index realization", "spectrumArena",
                "spectrumAtomIndexBijective", "spectrumRealization"))));

    private static DocumentBlock Realization(
        string id, string declaration, string title, string arena,
        string statement, string realization) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.FromAuthor(Disp(Call(
                "LegacyPrimitiveRealization", F.Id(arena), F.Id(statement), F.Id(realization)))),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "Both directions identify the frozen theorem's object-level statement with the "
                    + "Law of the concrete typed readouts; the backward direction does not invoke "
                    + "the source theorem."))),
            DescribeRole.Theorem);

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
