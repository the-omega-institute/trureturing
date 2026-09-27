using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Permutations;

internal sealed class MamedeFactorSeparationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Equal-product source shapes are unique when their interior endpoints satisfy j<i.",
        H("Separated Source Factors"),
        Blocks(Describe.Lean(
            DescribeId.Create("mamede-separated-source-uniqueness"),
            DeclarationHandle.Create(
                "D5/S1/Words/Permutations/MamedeFactorSeparation.source_shape_unique_of_j_lt_i"),
            H("Conditional uniqueness for j<i"),
            StatementSource.FromAuthor(Disp(Q(
                V("1"), Le, V("m"), Lt, V("j"), Lt, V("i"), Lt, V("M"), Le, V("n"), Land,
                Call("ReducedConsecutive", V("n"), V("a")), Land,
                Call("ReducedConsecutive", V("n"), V("b")), Land,
                Call("WordProduct", V("n"), V("a")), Eq,
                Call("WordProduct", V("n"), V("b")), Land,
                Call("SourceShape", V("m"), V("M"), V("i"), V("j"),
                    V("a"), V("p"), V("q")), Land,
                Call("SourceShape", V("m"), V("M"), V("i"), V("j"),
                    V("b"), V("r"), V("s")), Implies, V("a"), Eq, V("b")))),
            AssessedProvenance.FromLiterature(
                LibraryNoteRef.Create("D5/L/Words/mamede2026commutation")),
            Blocks(Paragraph(Text(
                "For arbitrary n,m,M,i,j with 1<=m<j<i<M<=n, let a and b be reduced "
                + "consecutive adjacent-swap words with the same permutation product. "
                + "Assume a=p++fullExcursion(m,M,i,j)++q and "
                + "b=r++fullExcursion(m,M,i,j)++s, with every prefix generator strictly "
                + "between m and j and every suffix generator strictly between i and M. "
                + "Then a=b. The central product fixes the prefix positions [m+1,j] "
                + "and suffix positions [i+1,M]. An extra descent relates it to the "
                + "existing deleted-excursion action formula; this descent is empty "
                + "when i=j+1. Commuting the central product past the suffixes and "
                + "cancelling it leaves equal products on disjoint supports. Pointwise "
                + "evaluation recovers the prefix products; cancellation recovers the "
                + "suffix products. Reducedness and consecutiveness pass to each "
                + "subword. Nonempty prefixes end at their common maximum j-1 and "
                + "nonempty suffixes start at their common minimum i+1, so extremal "
                + "endpoint uniqueness identifies them. Empty subwords are handled "
                + "by minimality against the empty representative. This formalizes "
                + "the factor-separation argument in Proposition 3.7, conditional on "
                + "both source shapes. It assumes no oscillation or endpoint equations. "
                + "It does not derive those shapes for an arbitrary singleton-word "
                + "fiber: the existing extraction theorems assume i<=j. No global "
                + "Conjecture 5.1 resolution or KPI change follows."))),
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
