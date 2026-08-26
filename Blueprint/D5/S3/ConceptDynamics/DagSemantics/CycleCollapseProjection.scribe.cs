using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DagSemantics;

internal sealed class CycleCollapseProjectionDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/DagSemantics/CycleCollapseProjection.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cyclic realization paths collapse to one logical node under an antisymmetric monotone "
            + "projection.",
        H("Cycle Collapse Projection"),
        Blocks(Describe.Lean(
            DescribeId.Create("mutual-paths-collapse-under-a-partial-order-projection"),
            DeclarationHandle.Create(Prefix + "cycle_segment_collapses_in_partialOrder"),
            H("Mutual realization paths collapse in a partial order"),
            StatementSource.FromAuthor(CollapseFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Fix a partially ordered logical carrier and a projection that sends every "
                        + "realization edge to a nondecreasing logical step. Supply reachable "
                        + "paths in both directions between two realization states.")),
                Paragraph(Text(
                    "The projected endpoints are then ordered in both directions, so partial-order "
                        + "antisymmetry identifies them. The theorem does not identify the "
                        + "original "
                        + "states unless projection injectivity is separately assumed."))),
            DescribeRole.Theorem))));

    private static Formula Relation(Formula carrier) =>
        Seq(carrier, Sp, To, Sp, carrier, Sp, To, Sp, F.Id("Prop"));

    private static Formula CollapseFormula()
    {
        Formula edge = F.Id("realEdge");
        Formula projection = F.Id("projection");
        Formula first = F.Id("first");
        Formula second = F.Id("second");
        Formula logical = F.Id("Logical");
        Formula hypotheses = Seq(
            Call("EdgeMonotoneProjection", edge, F.Id("le"), projection), Sp, Land, Sp,
            Call("ReflTransGen", edge, first, second), Sp, Land, RowBreak, Grp(),
            Call("ReflTransGen", edge, second, first));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, edge, Colon, Sp, Relation(F.Id("Real")), Comma, Sp,
            projection, Colon, Sp, F.Id("Real"), Sp, To, Sp, logical, Comma, Sp,
            first, Comma, Sp, second, Colon, Sp, F.Id("Real"), Comma, RowBreak, Grp(),
            OpenBracket, Call("PartialOrder", logical), CloseBracket, Comma, RowBreak, Grp(),
            Open, hypotheses, Close, Sp, Rightarrow, RowBreak, Grp(),
            Call("projection", first), Sp, Eq, Sp, Call("projection", second), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
