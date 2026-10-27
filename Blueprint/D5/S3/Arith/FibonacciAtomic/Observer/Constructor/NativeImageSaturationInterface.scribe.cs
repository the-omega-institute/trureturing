using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer.Constructor;

internal sealed class NativeImageSaturationInterfaceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "NativeImageSaturationInterface", H("Recursive decomposition of unrestricted native image languages"), Blocks(
            Describe.Lean(DescribeId.Create("native-image-decomposition"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeImageSaturationInterface.native_image_iff"),
                H("Actual native images split into bounded terminals and recursive pairs"), Statement(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("NativeImage(k,X) means that X is the actual image of some unrestricted completed native tree under rho iterated k times. The domain is the existing PFunctor.M completion: finite trees, arbitrary infinite trees, and the leafless Omega all remain in scope. No source-size, depth, rationality, or finite-prefix bound is introduced.")),
                    Paragraph(Text("For every k and X, actual image membership has exactly three alternatives. X is the alpha atomic iterate atomic(k), X is the beta atomic iterate atomic(k+1), or X is an ordered pair whose two children are themselves actual k-images. The pair alternative preserves ordered children and repeated values; it is a structural recursive clause, not an enumeration of finite trees.")),
                    Paragraph(Text("The forward direction analyzes the unrestricted preimage at its root. A leaf becomes one of the two atomic terminals, while a pair remains a pair because rho distributes over both children. The reverse direction constructs a preimage for each terminal and combines preimages of both children into one ordered pair. Injectivity and the native iterate identities are retained through the existing CompletionHomogeneousFixedPoints declarations.")),
                    Paragraph(Text("This is the image-language interface needed by finite-exception saturation: terminal matches are bounded to the two consecutive atomic values, while all nonterminal obligations recurse on both actual children. It does not yet state the finite system normalization, arbitrary free-state unique extension, mode partition, canonical replacement, filter preservation, or the full existence biconditional of NIS.15; those remain open source obligations.")),
                    Paragraph(Text("The result is an unrestricted structural theorem over the native completion. It is not a fixed-instance certificate, bounded enumeration, checker, numeric reduction, or claim that all solutions collapse to canonical assignments."))
                ), DescribeRole.Theorem)
        )));

    private static StatementSource Statement()
    {
        var k = V("k"); var x = V("X"); var u = V("U"); var v = V("V");
        var tree = V("CompletionTree");
        var image = Call("NativeImage", k, x);
        var decomposition = OrOf(
            EqOf(x, Call("atomic", k)),
            OrOf(
                EqOf(x, Call("atomic", Seq(k, Plus, Num(1)))),
                Some("U", tree, Some("V", tree,
                    And(EqOf(x, Call("node", u, v)),
                        Call("NativeImage", k, u),
                        Call("NativeImage", k, v))))));
        return StatementSource.FromAuthor(Disp(
            All("k", V("Nat"), All("X", tree, IffOf(image, decomposition)))));
    }

    private static Formula V(string name) => F.Id(name);
    private static Formula Par(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula EqOf(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula And(params Formula[] values) =>
        Seq(values.Select((value, index) => index == 0 ? Par(value) : Seq(Sp, Land, Sp, Par(value))).ToArray());
    private static Formula OrOf(Formula left, Formula right) => Seq(Par(left), Sp, Lor, Sp, Par(right));
    private static Formula IffOf(Formula left, Formula right) => Seq(Par(left), Sp, Iff, Sp, Par(right));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, Par(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, V(name), Colon, Sp, type, Comma, Sp, Par(body));
}
