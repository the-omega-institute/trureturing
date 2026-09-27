using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Permutations;

internal sealed class MamedeEndpointUniquenessDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A common extremal endpoint determines a reduced consecutive word.",
        H("Extremal Endpoint Uniqueness"),
        Blocks(Describe.Lean(
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
