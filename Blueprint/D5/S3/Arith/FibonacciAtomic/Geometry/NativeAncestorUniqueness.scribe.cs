using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Geometry;

internal sealed class NativeAncestorUniquenessDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Geometry/NativeAncestorUniqueness.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The full ordered leaf word and the exact inorder ancestor-area vector determine the native labelled tree.",
        H("Native Tree Uniqueness from Ancestor Coordinates"), Blocks(
            Describe.Lean(DescribeId.Create("native-ancestor-uniqueness"),
                DeclarationHandle.Create(Prefix + "native_ancestor_uniqueness"),
                H("Equality of the Two Observations Forces Tree Equality"),
                StatementSource.FromAuthor(ResultFormula()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Source is FreeMagma Bool: all nonempty finite ordered full binary trees "
                        + "with Boolean leaf labels. The word wd lists every label in left-to-right order. "
                        + "The ancestor coordinate list has one entry at each leaf gap, namely the product "
                        + "of the left and right child leaf counts at that gap's common ancestor. Its order "
                        + "is the left-child coordinates, the root product, and the right-child coordinates.")),
                    Paragraph(Text("For any two actual sources s and t, equality of their full words and "
                        + "equality of their exact natural coordinate lists imply s=t as labelled ordered trees. "
                        + "Both labels, repeated labels, and repeated equal subtrees at different addresses "
                        + "remain in the domain. A singleton tree has an empty coordinate list; its word "
                        + "still identifies its label. There is no empty native tree.")),
                    Paragraph(Text("The complete-interval criterion identifies every subtree interval "
                        + "from consecutive coordinate sums. In a paired tree, any complete prefix that "
                        + "is shorter than the whole tree lies inside the left child: its address is "
                        + "nonempty, and a right step would give a positive offset. The left child's full "
                        + "leaf interval is itself such a prefix. Transfer that interval between the two "
                        + "trees using coordinate equality. Each left-child size is at most the other's, "
                        + "so their root split positions agree.")),
                    Paragraph(Text("The common split separates the words into the two child words. It also "
                        + "separates the coordinate lists: the left child has length(left)-1 gaps, then comes "
                        + "the root gap, then the right child. Hence both child pairs have equal words and "
                        + "equal coordinate lists. Structural induction identifies each child and therefore "
                        + "the entire native tree. Leaf cases use the complete ordered word directly.")),
                    Paragraph(Text("This is an exact uniqueness statement about the specified observations. "
                        + "It supplies no observation-acquisition procedure, decoder, resource estimate, "
                        + "or finite-precision stability bound. Coordinates depend on actual ancestor "
                        + "relations; equality does not make them obtainable from the leaf word alone."))),
                DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, Par(body));
    private static Formula EqOf(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));
    private static Formula ResultFormula()
    {
        Formula s=V("s"), t=V("t"), source=Seq(Operatorname, Grp(V("Source")));
        Formula result=Imp(EqOf(Call("wd",s),Call("wd",t)),
            Imp(EqOf(Call("coordinates",s),Call("coordinates",t)),EqOf(s,t)));
        return Disp(All("s",source,All("t",source,result)));
    }
}
