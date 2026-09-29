using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Permutations;

internal sealed class MamedeShapeExtractionDocument : IScribeDocumentDefinition
{
    private const string Root = "D5/S1/Words/Permutations/MamedeShapeExtraction.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/mamede2026commutation");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Endpoint and exterior fixed-point data force the first-orientation shape in every singleton word.",
        H("Source Shape Extraction"),
        Blocks(
            Paragraph(Text("Fix the first orientation with 1<=m<i<=j<M<=n. "
                + "The permutation product applies the rightmost generator first. "
                + "A singleton word here is an actual reduced consecutive word for sigma. "
                + "EndpointExteriorFixedSource consists only of these order bounds, "
                + "the three endpoint equations, and fixed points outside [m,M+1]. "
                + "It assumes neither a nonoscillating word nor separate nonfixed endpoint clauses.")),
            Describe.Lean(
                DescribeId.Create("mamede-shape-endpoint-exterior-fixed-source"),
                DeclarationHandle.Create(Root + "endpointExteriorFixedSource"),
                H("Endpoint and exterior fixed-point hypothesis"),
                StatementSource.FromAuthor(Disp(Q(
                    Call("EndpointExteriorFixedSource", V("n"), V("m"), V("M"),
                        V("i"), V("j"), V("sigma")), Iff,
                    D(1), Le, V("m"), Lt, V("i"), Le, V("j"), Lt, V("M"),
                    Le, V("n"), Land,
                    Call("sigma", Call("position", V("n"), Q(V("M"), Plus, D(1)))),
                    Eq, Call("position", V("n"), V("m")), Land,
                    Call("sigma", Call("position", V("n"), V("m"))),
                    Eq, Call("position", V("n"), Q(V("j"), Plus, D(1))), Land,
                    Call("sigma", Call("position", V("n"), V("i"))),
                    Eq, Call("position", V("n"), Q(V("M"), Plus, D(1))), Land,
                    Forall, V("k"), InMacro, Call("Fin", Q(V("n"), Plus, D(1))),
                    Comma, Parenthesized(Q(Call("val", V("k")), Plus, D(1), Lt, V("m"),
                        Lor, V("M"), Plus, D(1), Lt, Call("val", V("k")), Plus, D(1))),
                    Implies, Call("sigma", V("k")), Eq, V("k")))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The exact Lean definition has no oscillation or "
                    + "nonfixed endpoint clause; the three endpoint equations and "
                    + "outside fixed points are its only permutation conditions."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("mamede-shape-source-forced-runs"),
                DeclarationHandle.Create(Root + "source_forced_runs"),
                H("Three forced runs and generator support"),
                StatementSource.FromAuthor(Disp(Q(
                    Call("EndpointExteriorFixedSource", V("n"), V("m"), V("M"), V("i"), V("j"), V("sigma")),
                    Land, Call("Singleton", V("n"), V("sigma"), V("a")),
                    Implies, Call("FirstDescent", V("a"), V("j"), V("m")),
                    Land, Call("CentralAscent", V("a"), V("m"), V("M")),
                    Land, Call("LastDescent", V("a"), V("M"), V("i")),
                    Land, Call("GeneratorSupport", V("a"), V("m"), V("M"))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("FirstDescent means a=p++descending(j,m)++q, "
                    + "all letters of p are below j and all letters of q exceed m. "
                    + "CentralAscent means a=p++ascending(m,M)++q, all letters of p exceed m "
                    + "and all letters of q are below M. LastDescent means "
                    + "a=p++descending(M,i)++q, all letters of p are below M and all letters "
                    + "of q exceed i. Each decomposition has its own p and q. GeneratorSupport "
                    + "means every letter of a lies in [m,M]. The three decompositions "
                    + "are initially separate; the next theorem aligns them. This endpoint-based "
                    + "strengthening is repository-derived; the cited paper's Proposition 3.3 "
                    + "and Lemma 3.6 do not assert it under these weaker premises."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("mamede-shape-source-all-singletons"),
                DeclarationHandle.Create(Root + "source_shape_for_every_singleton"),
                H("Every source singleton has the first orientation"),
                StatementSource.FromAuthor(Disp(Q(
                    Call("EndpointExteriorFixedSource", V("n"), V("m"), V("M"), V("i"), V("j"), V("sigma")),
                    Land, Call("Singleton", V("n"), V("sigma"), V("a")),
                    Implies, Exists, V("p"), Comma, Exists, V("q"), Comma,
                    Call("SourceShape", V("m"), V("M"), V("i"), V("j"),
                        V("a"), V("p"), V("q"))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The unique shared occurrences of m and M align "
                    + "the three forced runs into one Full(m,M,i,j). The first prefix lies "
                    + "strictly in (m,j), and the final suffix lies strictly in (i,M). "
                    + "This endpoint-based strengthening is proved in Lean for each actual "
                    + "singleton word. The cited paper derives endpoint identities from "
                    + "a nonoscillating word; this theorem starts from explicit endpoint "
                    + "identities. This does not resolve Conjecture 5.1."))),
                DescribeRole.Theorem))));

    private static Formula Q(params Formula[] items)
    {
        var spaced = new Formula[items.Length * 2 - 1];
        for (var i = 0; i < items.Length; i++)
        {
            spaced[2 * i] = items[i];
            if (i + 1 < items.Length) spaced[2 * i + 1] = Sp;
        }
        return Seq(spaced);
    }

    private static Formula V(string name) => F.Id(name);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Q(Operatorname, Grp(V(name))), [.. args]);
}
