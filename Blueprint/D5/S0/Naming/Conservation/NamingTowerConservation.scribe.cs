using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Naming.Conservation;

internal sealed class NamingTowerConservationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Countable naming towers leave a full-measure anonymous complement.",
        H("Naming Tower Conservation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("countable-tower-anonymous-full-measure"),
                DeclarationHandle.Create(
                    "D5/S0/Naming/Conservation/NamingTowerConservation.countable_tower_anonymous_full_measure"),
                H("Countable towers leave a full-measure anonymous complement"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("Countable"), Open, F.Id("namedUnion"), Open, F.Id("systems"), Close, Close,
                    Sp, Land, Sp,
                    Mu, Open, F.Id("namedUnion"), Open, F.Id("systems"), Close, Close,
                    Sp, Eq, Sp, D(0), Sp, Land, Sp,
                    Mu, Open,
                    F.Id("X"), Sp, Setminus, Sp,
                    F.Id("namedUnion"), Open, F.Id("systems"), Close,
                    Close, Sp, Eq, Sp, Mu, Open, F.Id("X"), Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The index type is arbitrary but countable, so it covers finite towers and "
                        + "countably infinite limiting towers without imposing an unclaimed nesting "
                        + "condition. Each layer is a NamingSystem, whose finite height sublevels make "
                        + "its named image countable.")),
                    Paragraph(Text(
                        "The countable union of those named images is countable. Atomlessness makes "
                        + "that union null, and the complement-null measure identity then gives the "
                        + "anonymous complement exactly the measure of the whole carrier.")),
                    Paragraph(Text(
                        "Pinned Mathlib supplies Set.Countable.measure_zero and "
                        + "measure_of_measure_compl_eq_zero. The repository theorem "
                        + "D5.S0.Naming.dark_side_conservation supplies the nullity clause; this "
                        + "corollary retains the countability mechanism and the full-measure "
                        + "complement conclusion explicitly."))),
                DescribeRole.Proposition)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Naming/NamingSystem"))]));
}
