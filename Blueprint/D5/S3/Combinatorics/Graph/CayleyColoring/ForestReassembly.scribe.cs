using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.CayleyColoring;

internal sealed class CayleyTreeForestReassemblyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Reassembling the conflict components turns peaks into vertices without retained children.",
        H("Peak transport in a retained forest"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("forest-peaks"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/ForestReassembly.forestEquiv_peaks"),
                H("Count transport for marked trees"),
                StatementSource.FromAuthor(Disp(Statement1())),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Asymptotics/depanafieu2026stabilization")),
                Blocks(Paragraph(Text("The sample consists of a tree and a spanning subgraph obtained by retaining some edges. Each component is rooted at its entry vertex on paths from the ambient root. Replace its tree by the fixed-root image and leave all intercomponent edges in place. This relates its original peak count to the number of vertices with no retained child in the new rooted tree."))),
                DescribeRole.Theorem)),
        []));

    private static Formula Statement1()
    {
        var v = F.Id("V");
        var r = F.Id("r");
        var s = F.Id("S");
        var image = At(Call("forestEquiv", r), s);
        var oldPeaks = Call("card", Call("PeakSet", Call("retained", s)));
        var newLeaves = Call("card", Call("NoRetainedChildSet",
            Call("tree", image), Call("retained", image), r));
        return All("V", F.Id("Type"), Seq(Instance("Fintype", v), Instance("LinearOrder", v),
            All("r", v, All("S", Call("ForestSample", v), Equal(oldPeaks, newLeaves)))));
    }

    private static Formula At(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);

    private static Formula All(string x, Formula type, Formula body) =>
        Seq(Forall, Sp, Open, F.Id(x), Colon, Sp, type, Close, Comma, Sp, body);

    private static Formula Instance(string type, Formula parameter) =>
        Seq(OpenBracket, Call(type, parameter), CloseBracket, Sp);
}
