using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.InformationEscapeArenas;

internal sealed class LocalLawGluingObstructionDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/InformationEscapeArenas/LocalLawGluingObstruction.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The three-cycle gluing obstruction is expressed by three coded admission tests.",
        H("Local-Law Gluing Obstruction Arena"),
        Blocks(
            Node("same-law", "sameLaw", "Adjacent equality law",
                "The equality relation supplies each of the two adjacent local laws."),
            Node("different-law", "differentLaw", "Outer inequality law",
                "The inequality relation supplies the outer local law that obstructs global gluing."),
            Node("gluing-readout", "GluingReadout", "Gluing readout indices",
                "The finite index type names the three coded ADMIT readouts."),
            Node("gluing-readout-decidable-equality", "instDecidableEqGluingReadout",
                "Decidable equality for gluing readouts",
                "This is the finite/decidable-equality instance obtained through a private equivalence."),
            Node("gluing-readout-fintype", "instFintypeGluingReadout",
                "Finite gluing readouts",
                "This is the finite/decidable-equality instance obtained through a private equivalence."),
            Node("local-law-gluing-signature", "localLawGluingSignature",
                "Typed gluing signature",
                "The signature assigns Boolean outputs and the ADMIT axis to all three readout indices."),
            Node("local-law-gluing-statement", "LocalLawGluingStatement",
                "Frozen gluing statement type",
                "This alias is definitionally the type of the frozen theorem D5/S3/ConceptDynamics/Gluing/LocalLawGluingObstruction.compatible_local_laws_can_lack_global_state."),
            Node("local-law-gluing-arena", "localLawGluingArena", "Local-law gluing arena",
                "The law compares existential fibers of the three realization ADMIT slots and rejects a jointly admitted triple."),
            Describe.Lean(
                DescribeId.Create("local-law-gluing-arena-nondegenerate"),
                DeclarationHandle.Create(Prefix + "localLawGluingArena_nondegenerate"),
                H("Local-law gluing arena is nondegenerate"),
                StatementSource.FromAuthor(NondegenerateFormula("localLawGluingArena")),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The finite arena has at least two distinct attempted global states."))),
                DescribeRole.Theorem))));

    private static DocumentBlock.Describe Node(
        string id, string declaration, string title, string explanation) => Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(explanation))),
            DescribeRole.Definition);

    private static Formula NondegenerateFormula(string arena) => Disp(Seq(
        Operatorname, Grp(F.Id("Nondegenerate")), Open,
        Operatorname, Grp(F.Id("toArena")), Open, F.Id(arena), Close, Close));
}
