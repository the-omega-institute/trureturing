using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.CayleyColoring;

internal sealed class CayleyTreeTreeDecompositionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A fixed-root bijection sends peaks to leaves in cardinality.",
        H("Peaks and leaves of a native rooted tree"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("peak-leaf"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/TreeDecomposition.fixedRootEquiv_filterCard"),
                H("Peak and rooted-leaf counts"),
                StatementSource.FromAuthor(Disp(Statement1())),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Combinatorics/seitz2011labelledtrees")),
                Blocks(Paragraph(Text("A peak has no greater-labeled neighbor. A rooted leaf has no adjacent vertex farther from the root. The equivalence removes the least label, recursively replaces the attached branches, and relabels the pivot to the specified root. Seitz gives the peak-to-leaf bijection in Corollary 5.2.2 and §5.3.1.2, and de Panafieu et al. use its distributional consequence in Proposition 5."))),
                DescribeRole.Theorem)),
        []));

    private static Formula Statement1()
    {
        var v = F.Id("V");
        var r = F.Id("r");
        var t = F.Id("T");
        var peakCount = Call("filterCard", Call("Peak", Call("graph", t)));
        var converted = At(Call("fixedRootEquiv", r), t);
        var leafCount = Call("filterCard", Call("RootedLeaf", Call("graph", converted), r));
        return All("V", F.Id("Type"), Seq(
            Instance("Fintype", v), Instance("LinearOrder", v),
            All("r", v, All("T", Call("Tree", v), Equal(peakCount, leafCount)))));
    }

    private static Formula At(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);

    private static Formula All(string x, Formula type, Formula body) =>
        Seq(Forall, Sp, Open, F.Id(x), Colon, Sp, type, Close, Comma, Sp, body);

    private static Formula Instance(string type, Formula parameter) =>
        Seq(OpenBracket, Call(type, parameter), CloseBracket, Sp);
}
