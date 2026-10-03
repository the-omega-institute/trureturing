using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Permutations;

internal sealed class MamedeExtremalOrientationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Extremal generators determine an endpoint orientation.",
        H("Extremal Orientation"),
        Blocks(Describe.Lean(
            DescribeId.Create("mamede-extremal-orientation"),
            DeclarationHandle.Create(
                "D5/S1/Words/Permutations/MamedeExtremalOrientation.extremal_orientation"),
            H("Support and full extremal run"),
            StatementSource.FromAuthor(Disp(Q(
                Call("Reduced", V("n"), V("w")), Land,
                Call("Consecutive", V("w")), Land, V("w"), Neq, Call("nil"),
                Implies, Exists, V("m"), V("M"), Comma,
                Call("AttainedSupport", V("n"), V("w"), V("m"), V("M")), Land,
                Call("ExteriorFixed", V("n"), V("w"), V("m"), V("M")), Land,
                Open, Call("DescendingOrientation", V("n"), V("w"), V("m"), V("M")),
                Lor, Call("AscendingOrientation", V("n"), V("w"), V("m"), V("M")), Close))),
            AssessedProvenance.FromLiterature(
                LibraryNoteRef.Create("D5/L/Words/mamede2026commutation")),
            Blocks(Paragraph(Text(
                "For every nonempty reduced consecutive adjacent-swap word w, there are "
                + "attained generator extrema 1<=m<=M<=n, and every letter lies in [m,M]. "
                + "The product fixes all one-based positions outside [m,M+1]. In the "
                + "descending orientation it maps m to M+1 and w=p++descending(M,m)++q, "
                + "with every prefix letter below M and every suffix letter above m. "
                + "In the ascending orientation it maps M+1 to m and "
                + "w=p++ascending(m,M)++q, with every prefix letter above m and every "
                + "suffix letter below M. Either or both orientations can hold. "
                + "This is the generator-extrema form of Mamede, Santos and Soares, "
                + "Lemma 3.1, together with the exterior support property. Word reversal "
                + "represents permutation inversion. No nonoscillation assumption or "
                + "strict internal endpoints are asserted; the result applies to "
                + "oscillating words and single-generator words as well."))),
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
