using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DagSemantics;

internal sealed class FiberInternalPathsDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/DagSemantics/FiberInternalPaths.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Paths whose edges stay inside readout fibers cannot change the observed coordinate.",
        H("Fiber-Internal Paths"),
        Blocks(Describe.Lean(
            DescribeId.Create("fiber-internal-reachability-preserves-readout"),
            DeclarationHandle.Create(Prefix + "readout_eq_of_reachable"),
            H("Fiber-internal paths preserve the readout"),
            StatementSource.FromAuthor(ReadoutFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Quantify a state relation and a readout, and assume every direct edge stays "
                        + "inside one readout fiber. A reflexive-transitive path then connects "
                        + "states with equal readout values.")),
                Paragraph(Text(
                    "The conclusion states equality only for the supplied path endpoints. It does "
                        + "not assert that equal readouts create a path in the reverse "
                        + "direction."))),
            DescribeRole.Theorem))));

    private static Formula ReadoutFormula()
    {
        Formula edge = F.Id("edge");
        Formula readout = F.Id("readout");
        Formula first = F.Id("first");
        Formula last = F.Id("last");
        Formula hypotheses = Seq(
            Call("FiberInternal", edge, readout), Sp, Land, Sp,
            Call("ReflTransGen", edge, first, last));

        return Disp(Seq(
            Forall, Sp, edge, Colon, Sp,
            F.Id("State"), Sp, To, Sp, F.Id("State"), Sp, To, Sp, F.Id("Prop"),
            Comma, Sp, readout, Colon, Sp,
            Call("Concept", F.Id("State"), F.Id("Coordinate")), Comma, RowBreak, Grp(),
            first, Comma, Sp, last, Colon, Sp, F.Id("State"), Comma, Sp,
            Open, hypotheses, Close, Sp, Rightarrow, RowBreak, Grp(),
            Call("readout", first), Sp, Eq, Sp, Call("readout", last), Dot));
    }
}
