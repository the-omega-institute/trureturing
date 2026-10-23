using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer;
internal sealed class NativeCompletionBranchExistenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "NativeCompletionBranchExistence", H("Actual infinite branches of native completion trees"), Blocks(
            Describe.Lean(DescribeId.Create("native-completion-infinite-branch"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Observer/NativeCompletionBranchExistence.infinite_of_not_finite"),
                H("Every completion outside the finite embedding has an infinite branch"), Statement(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The completion is the unrestricted final coalgebra PFunctor.M for Boolean leaves and ordered binary nodes. Source is the existing finite FreeMagma Bool carrier, and embed preserves the actual constructors and four-valued address readout. The premise excludes exactly the image of that finite embedding. It does not mean that the tree has infinitely many different subtree values.")),
                    Paragraph(Text("Child(S,T) means that T is an actual node and S is one of its two children. Accessibility for this relation reconstructs a finite source by induction: a leaf supplies its Boolean source leaf, and the two inductive source preimages combine into a source pair. The resulting embedding equals the original completion itself, not merely a selected finite approximation.")),
                    Paragraph(Text("The contrapositive gives nonaccessibility. Mathlib's not_acc_iff_exists_descending_chain then supplies one infinite chain of actual children starting at the given completion. A direction is selected for each chain edge. Induction on the length of the direction prefix preserves every subsequent address readout: reading prefix followed by a in the original tree equals reading a in the current chain tree. Its root is present, so every finite prefix of the single direction sequence is present in the original tree.")),
                    Paragraph(Text("Left and right children may coincide, and the child relation may have loops. A fully branching self-similar tree is therefore included. No default subtree is substituted for an invalid address, no regularity or computability of the completion is assumed, and no finite procedure for deciding membership in the finite embedding is claimed. The argument combines the classical descending-chain theorem with the native constructor and readout correspondence; no literature originality is claimed."))
                ), DescribeRole.Theorem)
        )));
    private static StatementSource Statement()
    {
        var finite = Some("t", V("Source"), EqOf(Call("embed", V("t")), V("T")));
        return StatementSource.FromAuthor(Disp(All("T", V("CompletionTree"),
            Imp(Imp(finite, V("False")), Call("HasInfiniteBranch", V("T"))))));
    }

    private static Formula V(string n) => F.Id(n);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Call(string n, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(n))), [.. args]);
    private static Formula EqOf(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));
    private static Formula All(string ns, Formula t, Formula b) => Seq(Forall, Sp,
        Seq(ns.Split(',').Select((n, i) => i == 0 ? V(n) : Seq(Comma, Sp, V(n))).ToArray()),
        Colon, Sp, t, Comma, Sp, Par(b));
    private static Formula Some(string ns, Formula t, Formula b) => Seq(Exists, Sp,
        Seq(ns.Split(',').Select((n, i) => i == 0 ? V(n) : Seq(Comma, Sp, V(n))).ToArray()),
        Colon, Sp, t, Comma, Sp, Par(b));
}
