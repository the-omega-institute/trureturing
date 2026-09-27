using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Permutations;

internal sealed class MamedeConditionalConverseDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/mamede2026commutation");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A first-orientation source singleton makes excursion deletion surjective onto target singletons.",
        H("Conditional Deletion Converse"),
        Blocks(
            Paragraph(Text("Fix 1<=m<i<=j<M<=n and the endpoint, exterior fixed-point, "
                + "and non-oscillating-source conditions of ExactSource. Suppose in "
                + "addition that a0 is an actual singleton reduced word for sigma and "
                + "has SourceShape(m,M,i,j,a0,p0,q0). Let gamma be the product of "
                + "Deleted(m,M,i), and put pi=sigma gamma inverse.")),
            Describe.Lean(
                DescribeId.Create("mamede-conditional-source-deletion-surjective"),
                DeclarationHandle.Create(
                    "D5/S1/Words/Permutations/MamedeConditionalConverse.source_deletion_surjective"),
                H("Every target singleton lifts"),
                StatementSource.FromAuthor(Disp(Q(
                    Call("ExactSource", V("n"), V("m"), V("M"), V("i"), V("j"), V("sigma")),
                    Land, Call("SourceShape", V("m"), V("M"), V("i"), V("j"),
                        V("a0"), V("p0"), V("q0")),
                    Land, Call("Singleton", V("n"), V("sigma"), V("a0")),
                    Implies, Forall, V("b"), Comma,
                    Call("Singleton", V("n"), V("pi"), V("b")), Implies,
                    Exists, V("a"), Comma, Exists, V("p"), Comma,
                    Exists, V("q"), Comma,
                    Call("Singleton", V("n"), V("sigma"), V("a")),
                    Land, Call("SourceShape", V("m"), V("M"), V("i"), V("j"),
                        V("a"), V("p"), V("q")),
                    Land, Call("Image", V("i"), V("j"), V("p"), V("q")), Eq, V("b"),
                    Land, Call("length", V("b")), Lt, Call("length", V("a"))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For every singleton reduced word b of pi, there "
                    + "are p and q with all letters of p in (m,j) and of q in (i,M). "
                    + "The word a=p ++ Full(m,M,i,j) ++ q is a singleton reduced word "
                    + "for sigma. Its deletion image is exactly b and b is strictly "
                    + "shorter than a. The theorem does not derive the SourceShape premise "
                    + "from ExactSource, and it makes no reflected-orientation, "
                    + "cardinality, oscillation, or induction assertion."))),
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
