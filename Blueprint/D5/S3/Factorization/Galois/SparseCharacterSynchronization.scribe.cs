using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Galois;

internal sealed class SparseCharacterSynchronizationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Factorization/Galois/SparseCharacterSynchronization.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Sparse comparisons synchronize a common phase exactly on preconnected graphs.",
        H("Sparse Character Synchronization"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("edge-difference"), DeclarationHandle.Create(Prefix + "edgeDifference"),
                H("Sparse comparisons"), StatementSource.FromAuthor(DifferenceFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let E(G) consist of ordered pairs of adjacent vertices. The "
                    + "additive homomorphism edgeDifference sends a vertex label x to the edge "
                    + "label x(u) minus x(v). All comparisons take place in the same group A."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("edge-difference-kernel-eq-constants-iff"),
                DeclarationHandle.Create(Prefix + "edge_difference_kernel_eq_constants_iff"),
                H("Exact synchronization criterion"), StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For any simple graph G and nontrivial abelian additive group A, "
                        + "the edge-difference kernel equals the diagonal subgroup if and only if "
                        + "G is preconnected: every two vertices are joined by a finite path. "
                        + "Vertex and edge sets need not be finite.")),
                    Paragraph(Text("The upstream additive homomorphism Pi.constAddMonoidHom V A "
                        + "sends a value a in A to the vertex labeling w mapped to a. Its range "
                        + "is the diagonal subgroup of constant labels.")),
                    Paragraph(Text("A zero difference forces equal labels at both endpoints. "
                        + "Induction along a path propagates that equality. A nonempty vertex set "
                        + "provides the common value; on the empty vertex set the zero phase "
                        + "represents the unique labeling.")),
                    Paragraph(Text("Conversely, fix a vertex and a nonzero coefficient. Give the "
                        + "reachable component value zero and its complement the nonzero value. "
                        + "This labeling has zero difference on every edge. If all kernel labels "
                        + "are constant, the complement must be empty.")),
                    Paragraph(Text("For cyclic coefficient groups of orders four and three, the "
                        + "criterion synchronizes common character values through any connected "
                        + "comparison graph. It does not identify elements of distinct finite "
                        + "fields. Arithmetic normalization, prime roles and denominator "
                        + "conditions remain separate hypotheses in any arithmetic application."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < args.Length; i++)
        {
            if (i > 0) items.AddRange([Comma, Sp]);
            items.Add(args[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Bind(string name, Formula type) =>
        Seq(Open, F.Id(name), Colon, Sp, type, Close);

    private static Formula Group(Formula a) =>
        Seq(OpenBracket, Call("AddCommGroup", a), CloseBracket);

    private static Formula DifferenceFormula()
    {
        Formula v = F.Id("V"), a = F.Id("A"), g = F.Id("G"), x = F.Id("x"), e = F.Id("e");
        return Disp(Seq(Forall, Sp, Bind("V", F.Id("Type")), Sp,
            Bind("G", Call("SimpleGraph", v)), Sp, Bind("A", F.Id("Type")), Sp,
            Group(a), Sp, Bind("x", Seq(v, Sp, To, Sp, a)), Sp,
            Bind("e", Call("E", g)), Comma, Sp, Call("edgeDifference", g, a, x, e), Sp, Eq, Sp,
            Call("x", Call("fst", e)), Sp, Minus, Sp, Call("x", Call("snd", e))));
    }

    private static Formula TheoremFormula()
    {
        Formula v = F.Id("V"), a = F.Id("A"), g = F.Id("G");
        return Disp(Seq(Forall, Sp, Bind("V", F.Id("Type")), Sp,
            Bind("G", Call("SimpleGraph", v)), Sp, Bind("A", F.Id("Type")), Sp,
            Group(a), Sp, OpenBracket, Call("Nontrivial", a), CloseBracket, Comma, RowBreak,
            Call("ker", Call("edgeDifference", g, a)), Sp, Eq, Sp,
            Call("range", Seq(Operatorname, Grp(F.Id("Pi"), Dot, F.Id("constAddMonoidHom")),
                Open, v, Comma, Sp, a, Close)), Sp, Iff, Sp, Call("Preconnected", g)));
    }
}
