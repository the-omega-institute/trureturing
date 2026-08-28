using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DependencyTopology;

internal sealed class DepthClosedFiltrationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/DependencyTopology/DepthClosedFiltration.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Strict edge depth yields a closed Alexandrov sublevel filtration.",
        H("Depth-Closed Filtration"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("strict-paths-strictly-increase-depth"),
                DeclarationHandle.Create(Prefix + "depth_strict_of_strictReachable"),
                H("Strict reachability strictly increases compatible depth"),
                StatementSource.FromAuthor(StrictDepthFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Depth compatibility requires every edge to move from a smaller "
                            + "natural depth to a larger one.")),
                    Paragraph(Text(
                        "Induction along a nonempty reachability path composes these strict "
                            + "inequalities, so the path endpoint has strictly larger depth."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("depth-sublevels-are-alexandrov-closed"),
                DeclarationHandle.Create(Prefix + "depthSublevel_isClosed"),
                H("Every compatible depth sublevel is closed"),
                StatementSource.FromAuthor(ClosedSublevelFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Reachability can only increase a depth compatible with the edge "
                            + "relation. Therefore the strict superlevel above any natural "
                            + "level is upward closed.")),
                    Paragraph(Text(
                        "Upward-closed sets are open in the dependency Alexandrov topology. "
                            + "The complementary sublevel is consequently closed.")),
                    Paragraph(Text(
                        "The conclusion is conditional on DepthCompatible and is asserted "
                            + "for the explicitly displayed level only."))),
                DescribeRole.Theorem))));

    private static Formula Arrow(Formula source, Formula target) =>
        Seq(source, Sp, To, Sp, target);

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula SharedBindings(
        Formula vertex,
        Formula edge,
        Formula depth) =>
        Seq(
            Forall, Sp, edge, Colon, Sp,
            Arrow(vertex, Arrow(vertex, Seq(Operatorname, Grp(F.Id("Prop"))))),
            Comma, Sp,
            depth, Colon, Sp, Arrow(vertex, Seq(Mathbb, Grp(F.Id("N")))), Comma, Sp);

    private static Formula StrictDepthFormula()
    {
        Formula vertex = F.Id("V");
        Formula edge = F.Id("edge");
        Formula depth = F.Id("depth");
        Formula source = F.Id("u");
        Formula target = F.Id("v");
        Formula hypotheses = Seq(
            Call("DepthCompatible", edge, depth), Sp, Land, Sp,
            Call("StrictReachable", edge, source, target));

        return Disp(Seq(
            SharedBindings(vertex, edge, depth),
            source, Comma, Sp, target, Colon, Sp, vertex, Comma, Sp,
            Open, hypotheses, Close, Sp, Rightarrow, Sp,
            Apply(depth, source), Sp, Lt, Sp, Apply(depth, target), Dot));
    }

    private static Formula ClosedSublevelFormula()
    {
        Formula vertex = F.Id("V");
        Formula edge = F.Id("edge");
        Formula depth = F.Id("depth");
        Formula level = F.Id("n");
        Formula topology = Call("upperSetTopology", Call("Reachable", edge));

        return Disp(Seq(
            SharedBindings(vertex, edge, depth),
            level, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp,
            Call("DepthCompatible", edge, depth), Sp, Rightarrow, Sp,
            Call(
                "IsClosed",
                topology,
                Call("depthSublevel", depth, level)),
            Dot));
    }
}
