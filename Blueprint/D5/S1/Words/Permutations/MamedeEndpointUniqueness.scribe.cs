using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Permutations;

internal sealed class MamedeEndpointUniquenessDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Extremal endpoints force oscillation and determine reduced consecutive words.",
        H("Extremal Endpoint Structure"),
        Blocks(
        Describe.Lean(
            DescribeId.Create("mamede-extremal-maximum-peel"),
            DeclarationHandle.Create(
                "D5/S1/Words/Permutations/MamedeEndpointUniqueness.maximum_peel"),
            H("Forced descent from a maximal first letter"),
            StatementSource.FromAuthor(Disp(Q(
                Call("ReducedConsecutive", V("n"), Call("Cons", V("M"), V("a"))), Land,
                Call("AllLettersAtMost", V("M"), Call("Cons", V("M"), V("a"))),
                Implies, Exists, V("i"), Comma, Exists, V("q"), Comma,
                Call("InitialDescendingRun", V("M"), V("i"), V("a"), V("q"))))),
            AssessedProvenance.FromLiterature(
                LibraryNoteRef.Create("D5/L/Words/mamede2026commutation")),
            Blocks(Paragraph(Text(
                "For a reduced consecutive word M::a with every generator at most M, "
                + "there are i and q with 1<=i<=M, M::a=descending(M,i)++q, "
                + "and every letter of q strictly above i. Its product sends position i "
                + "to position M+1. The descent is an initial run, with no assumed "
                + "oscillation. The theorem is the existing forced-run proof exposed for "
                + "reuse by the endpoint-uniqueness proof; it does not constrain all later "
                + "spike lengths or establish Lemma 3.2's oscillation direction."))),
            DescribeRole.Theorem),
        Describe.Lean(
            DescribeId.Create("mamede-extremal-endpoint-oscillation"),
            DeclarationHandle.Create(
                "D5/S1/Words/Permutations/MamedeEndpointUniqueness.extremal_endpoint_oscillation"),
            H("Oscillation from an extremal endpoint"),
            StatementSource.FromAuthor(Disp(Q(
                Call("ReducedConsecutive", V("n"), V("w")), Land,
                Call("Endpoint", V("k"), V("w")), Land,
                Call("GeneratorExtremum", V("k"), V("w")),
                Implies, Call("Oscillation", V("w"))))),
            AssessedProvenance.FromLiterature(
                LibraryNoteRef.Create("D5/L/Words/mamede2026commutation")),
            Blocks(Paragraph(Text(
                "Let w be a reduced consecutive adjacent-swap word on n+1 positions. "
                + "Suppose its first or last letter is k, and all its letters are at "
                + "most k or all are at least k. Then oscillation(w) holds: the absolute "
                + "differences between its first letter, strict internal peaks and valleys, "
                + "and last letter form a weakly increasing or weakly decreasing list. "
                + "The endpoint condition excludes the empty word and makes k an attained "
                + "extremum. A maximal first letter forces a descending run; its final "
                + "letter starts a shorter suffix at its minimum. Reflection and induction "
                + "give weakly decreasing lengths, and reversal supplies the last-letter "
                + "cases. This proves the endpoint-to-oscillation direction of Lemma 3.2 "
                + "in the repository's exact model. The paper invokes its Theorem 2.2, "
                + "but this proof uses the existing reduced-word crossing results. It does "
                + "not prove the reverse characterization or derive an extremal endpoint "
                + "from two opposite position maps."))),
            DescribeRole.Theorem),
        Describe.Lean(
            DescribeId.Create("mamede-symmetric-excursion-outer-empty"),
            DeclarationHandle.Create(
                "D5/S1/Words/Permutations/MamedeEndpointUniqueness.symmetric_excursion_outer_empty"),
            H("No two exterior factors around a symmetric excursion"),
            StatementSource.FromAuthor(Disp(Q(
                Call("ReducedConsecutiveSymmetricExcursion", V("n"), V("m"), V("M"),
                    V("p"), V("q")), Land,
                Call("InteriorSupport", V("m"), V("M"), V("p"), V("q")),
                Implies, V("p"), Eq, Call("EmptyWord"), Lor,
                V("q"), Eq, Call("EmptyWord")))),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(
                "Let 1<=m<M<=n and let the middle word descend from M to m, then "
                + "ascend from m+1 to M. If p and q contain only generators strictly "
                + "between m and M, and the combined word is reduced and consecutive, "
                + "then p or q is empty. The middle product swaps positions m and M+1 "
                + "and fixes the interior. When both factors are nonempty, consecutiveness "
                + "forces generator M-1 at both boundaries; the two copies commute through "
                + "the middle product and cancel, contradicting reducedness. This is an "
                + "unbounded source theorem. It does not derive the displayed factorization "
                + "from opposite endpoint maps or prove their oscillation consequence."))),
            DescribeRole.Theorem),
        Describe.Lean(
            DescribeId.Create("mamede-extremal-endpoint-uniqueness"),
            DeclarationHandle.Create(
                "D5/S1/Words/Permutations/MamedeEndpointUniqueness.extremal_endpoint_unique"),
            H("Uniqueness at either end"),
            StatementSource.FromAuthor(Disp(Q(
                Call("ReducedConsecutive", V("n"), V("a")), Land,
                Call("ReducedConsecutive", V("n"), V("b")), Land,
                Call("WordProduct", V("n"), V("a")), Eq,
                Call("WordProduct", V("n"), V("b")), Land,
                Call("CommonEndpoint", V("k"), V("a"), V("b")), Land,
                Call("CommonExtremum", V("k"), V("a"), V("b")),
                Implies, V("a"), Eq, V("b")))),
            AssessedProvenance.FromLiterature(
                LibraryNoteRef.Create("D5/L/Words/mamede2026commutation")),
            Blocks(Paragraph(Text(
                "Let a and b be reduced consecutive adjacent-swap words on n+1 positions "
                + "with the same permutation product. Suppose both first letters are k, "
                + "or both last letters are k. Suppose also that every letter of both "
                + "words is at most k, or every letter of both words is at least k. "
                + "Then a=b. The endpoint condition excludes empty words. The minimum "
                + "and maximum alternatives apply separately, and the compared endpoints "
                + "are on the same side. No oscillation assumption is needed: this is the "
                + "endpoint-extremum form of Mamede, Santos and Soares, Lemmas 3.2 and 3.4. "
                + "For a maximal first letter, the largest strand forces a common initial "
                + "descent. Removing it leaves shorter words starting at their minimum, "
                + "so induction determines the tails. Reflection gives the minimal-first "
                + "case; reversal gives the last-letter cases. The result compares words "
                + "at an extremal endpoint. It does not assert uniqueness for arbitrary "
                + "endpoints or for an entire singleton-word fiber."))),
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
