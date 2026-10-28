using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer.Constructor;

internal sealed class NativeFreeStateCardinalityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "NativeFreeStateCardinality", H("Free native states resist countable parameterization"), Blocks(
            Describe.Lean(DescribeId.Create("native-free-state-cardinality"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Observer/Constructor/NativeFreeStateCardinality.free_state_cardinality"),
                H("Infinite stream trees and the complete solution domain"), Statement(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The domain is the existing unrestricted native completion, including arbitrary infinite ordered trees. A Boolean stream s determines a tree U(s) whose left child is U(tail(s)) and whose right child is the atomic leaf for its first bit. False selects the alpha leaf and true the beta leaf. Thus this construction retains exactly the two native atoms of ranks zero and one, without introducing a new leaf label.")),
                    Paragraph(Text("The address bitAddress(j) consists of j left edges followed by one right edge. The subtree there is exactly the leaf for s(j); it is reached for every natural j. The corecursor constructs one complete tree for the entire stream, and induction on j proves this whole-subtree identity. Equal completed trees therefore have equal bits at every index. Every constructed tree has actual finite leaf subtrees and differs from the entirely leafless Omega.")),
                    Paragraph(Text("In the formula U denotes streamTree, tail(s)(j) is s(j+1), and not is Boolean negation. Subtree returns an optional whole tree, so some explicitly certifies presence. The final quantifier ranges over every countable parameter type A and every function decode into CompletionTree. Surjective has its ordinary function-theoretic meaning.")),
                    Paragraph(Text("Injectivity supplies continuum many distinct completed native solutions of the retained equation X = X. If the completed domain were countable, encoding its elements by natural numbers and composing with this injection and characteristic functions of subsets of the naturals would contradict the existing Cantor theorem. A surjection from any countable parameter domain would make the completed domain countable, so no such surjection exists.")),
                    Paragraph(Text("A finite family of branches with finitely many integer parameters in each branch has a countable disjoint union of parameter tuples. Any deterministic assignment of canonical terminals or Omega from those data is a function of that countable domain and therefore cannot enumerate all native completed solutions. This statement concerns branches determined by their data. A branch retaining an unrestricted completed free state has a different parameter domain and is not ruled out. Neither a normalization algorithm for arbitrary retained equations nor an effective elimination of free states follows.")),
                    Paragraph(Text("The result is an unrestricted recursive construction and structural obstruction. It is not a bounded enumeration, a finite numerical instance, a checker or a numerical reduction. No literature-wide novelty is asserted."))
                ), DescribeRole.Theorem)
        )));

    private static StatementSource Statement()
    {
        var s = V("s"); var j = V("j"); var a = V("A"); var d = V("decode");
        var streams = Seq(V("Nat"), Sp, To, Sp, V("Bool"));
        var tree = V("CompletionTree");
        var u = Call("U", s);
        var negBit = Call("not", Call("s", j));
        return StatementSource.FromAuthor(Disp(And(
            All("s", streams, EqOf(u, Call("node", Call("U", Call("tail", s)),
                Call("leaf", Call("not", Call("s", Num(0))))))),
            All("s", streams, All("j", V("Nat"),
                EqOf(Call("subtree", Call("bitAddress", j), u), Call("some", Call("leaf", negBit))))),
            Call("Injective", V("U")),
            All("s", streams, Seq(u, Sp, Neq, Sp, V("Omega"))),
            All("A", V("Type"), Seq(OpenBracket, Call("Countable", a), CloseBracket, Sp,
                All("decode", Seq(a, Sp, To, Sp, tree),
                    Seq(Neg, Par(Call("Surjective", d)))))))));
    }

    private static Formula V(string name) => F.Id(name);
    private static Formula Par(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula EqOf(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula And(params Formula[] values) =>
        Seq(values.Select((value, index) => index == 0 ? Par(value) : Seq(Sp, Land, Sp, Par(value))).ToArray());
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, Par(body));
}
