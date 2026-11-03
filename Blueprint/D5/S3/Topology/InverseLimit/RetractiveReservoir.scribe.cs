using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.InverseLimit;

internal sealed class RetractiveReservoirDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Topology/InverseLimit/RetractiveReservoir.";
    private static AssessedProvenance Provenance => AssessedProvenance.FromRepo(
        LibraryNoteRef.Create("D5/L/Topology/retractive2026reviewed"));
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Classical arbitrary-set retractive attachment supplier; original Efimov KPI 0.",
        H("RetractiveReservoir"), Blocks(
            Paragraph(Text("Statements below are projected from the compiled Lean declarations with their complete actual telescopes. The scientific source and independent ordinary review are identified in the cited Library note; neither source-level review nor this exposition substitutes for kernel checking.")),
            Describe.Lean(DescribeId.Create("persistent-reservoir-sequence"), DeclarationHandle.Create(Owner + "persistent_reservoir_sequence"), H("Direct consumed reservoir obstruction in the final actual carrier"), StatementSource.FromLean(), Provenance, Blocks(Paragraph(Text("The core is the actual TopCat.limitCone G thread space; component i is the actual TopCat.limitCone (F i) thread space; its attachment is the actual continuous coordinatewise limitMap of the supplied natural transformation. A fixed infinite set R of indices and one actual core thread b are given. Proper-stage actual range membership for every index in R is the only range premise. CompactRangePersistence proves final membership for every such index. The attachment theorem then constructs an actual injective natural sequence converging to the literal final core point, with that point outside all terms. This directly consumes both suppliers. No final-range premise is assumed, and the proof makes no irreducibility assertion about any prefix or successor. In the reviewed example the prefix is reducible and only its specified final successor is irreducible. No sequence-free core is constructed; original ZFC Efimov remains unsolved and all supplier/helper credit is original KPI 0."))), DescribeRole.Theorem))));
}
