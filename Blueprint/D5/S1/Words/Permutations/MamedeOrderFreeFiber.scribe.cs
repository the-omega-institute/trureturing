using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Permutations;

internal sealed class MamedeOrderFreeFiberDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The first-orientation endpoint data determine the entire singleton-word fiber when j<i.",
        H("First-Orientation Singleton Fiber"),
        Blocks(Describe.Lean(
            DescribeId.Create("mamede-order-free-singleton-fiber"),
            DeclarationHandle.Create(
                "D5/S1/Words/Permutations/MamedeOrderFreeFiber.singleton_fiber_unique_of_j_lt_i"),
            H("Whole-fiber uniqueness for j<i"),
            StatementSource.FromAuthor(Disp(Q(
                D(1), Le, V("m"), Lt, V("j"), Lt, V("i"), Lt, V("M"), Le, V("n"),
                Land, Call("Endpoints", V("sigma"), V("m"), V("M"), V("i"), V("j")),
                Land, Call("ExteriorFixed", V("sigma"), V("m"), V("M")),
                Land, Call("SingletonWord", V("n"), V("sigma"), V("a")),
                Land, Call("SingletonWord", V("n"), V("sigma"), V("b")),
                Implies, V("a"), Eq, V("b")))),
            AssessedProvenance.FromLiterature(
                LibraryNoteRef.Create("D5/L/Words/mamede2026commutation")),
            Blocks(Paragraph(Text(
                "For arbitrary n,m,M,i,j with 1<=m<j<i<M<=n, let sigma be a permutation "
                + "of the n+1 positions in the repository's one-based position convention. "
                + "Assume sigma(M+1)=m, sigma(m)=j+1, sigma(i)=M+1, and sigma fixes every "
                + "position outside [m,M+1]. Then any two singletonWord(n,sigma) lists "
                + "are equal. For each source list, guarded walks force a descent j..m, "
                + "an ascent m..M, and a descent M..i. Aligning their shared m and M "
                + "markers yields the exact sourceShape, with every prefix letter in "
                + "(m,j) and every suffix letter in (i,M). The existing factor-separation "
                + "theorem then identifies two such lists. The proof includes adjacent "
                + "endpoints i=j+1 and empty outer factors. The theorem is conditional "
                + "on all three endpoint equations and exterior fixedness; the separate "
                + "nonoscillating source-endpoint theorem derives these from an actual "
                + "first-orientation source word with attained generator extrema. "
                + "It formalizes "
                + "this first-orientation part of Proposition 3.7 and does not settle "
                + "global Conjecture 5.1. The repository's singletonWord interpretation "
                + "of the paper's commutation classes remains a source-translation "
                + "judgment."))),
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
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Q(Operatorname, Grp(V(name))), [.. args]);
}
