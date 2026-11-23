using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.CayleyColoring;

internal sealed class CayleyTreeCentralSchedulerDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A uniform ranking gives the same legal terminal-history probabilities as sequential uniform enabled choices.",
        H("The random central coloring daemon"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("terminal-law"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Graph/CayleyColoring/CentralScheduler.policy_terminal_law"),
                H("Exact terminal-history law"),
                StatementSource.FromAuthor(Disp(Statement1())),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Combinatorics/depanafieu2026stabilization")),
                Blocks(Paragraph(Text("A history is accepted when following the free-color policy produces a proper final coloring. Its ranking fiber consists of permutations yielding that ordered mover list. The enabled sets shrink after each actual recoloring, and permuting the ranks of currently enabled vertices preserves the prefix constraints. The product counts the successive enabled choices from the initial conflict graph. An invalid or nonterminal history has an empty fiber."))),
                DescribeRole.Theorem)),
        []));

    private static Formula Statement1()
    {
        var v = F.Id("V");
        var k = F.Id("K");
        var g = F.Id("G");
        var policy = F.Id("P");
        var c = F.Id("c");
        var l = F.Id("h");
        var accept = Call("LegalTerminal", g, policy, c, l);
        var ranks = Call("RankFiber", g, c, l);
        var product = Call("choiceProduct", Call("conflict", g, c),
            Call("univ", v), l);
        var equation = Equal(Multiply(Call("card", ranks), product),
            Call("card", Call("Perm", v)));
        var invalid = Seq(Neg, Sp, accept, Sp, Implies, Sp, Call("IsEmpty", ranks));
        var law = Seq(Open, accept, Sp, Implies, Sp, equation, Close, Sp,
            Land, Sp, Open, invalid, Close);
        var inputs = All("G", Call("SimpleGraph", v), All("P", Call("FreePolicy", k, g),
            All("c", Arrow(v, k), All("h", Call("List", v), law))));
        return All("V", F.Id("Type"), All("K", F.Id("Type"),
            Seq(Instance("Fintype", v), Instance("LinearOrder", v), inputs)));
    }

    private static Formula Arrow(Formula source, Formula target) => new Formula.TypeArrow(source, target);

    private static Formula All(string x, Formula type, Formula body) =>
        Seq(Forall, Sp, Open, F.Id(x), Colon, Sp, type, Close, Comma, Sp, body);

    private static Formula Instance(string type, Formula parameter) =>
        Seq(OpenBracket, Call(type, parameter), CloseBracket, Sp);
}
