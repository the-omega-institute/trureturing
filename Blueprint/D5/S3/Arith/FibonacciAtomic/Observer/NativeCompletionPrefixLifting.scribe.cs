using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer;
internal sealed class NativeCompletionPrefixLiftingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "NativeCompletionPrefixLifting", H("Infinite completion prefixes and finite simultaneous separation"), Blocks(
            Describe.Lean(DescribeId.Create("native-completion-prefix-cylinder"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Observer/NativeCompletionPrefixLifting.prefix_cylinder"),
                H("The complete reply table is exactly a native filling cylinder"), CylinderStatement(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("CompletionTree is the pinned Mathlib PFunctor.M for the native polynomial with shape Bool plus Unit. A Boolean shape is a leaf and has no children; the Unit shape is a branch with two ordered Boolean children. This is the unrestricted final coalgebra of consistent finite approximations. The theorem imposes no regularity, computability, finite-state representation or bound on the tree.")),
                    Paragraph(Text("CompletionReadout recursively inspects the actual destructor. True leaves report alpha and false leaves report beta. False selects the left child and true selects the right child. Every word is a legal query; any nonempty word under a leaf returns absent. Embed uses the existing FreeMagma Bool Source and preserves its exact readout at every address. The arbitrary M-type reader never uses the upstream default-returning iselect API.")),
                    Paragraph(Text("Cutoff d retains every leaf and ordered branch strictly above depth d, leaving a hole only at an originally reached depth-d position. A new depth/address induction proves cutoff equality if and only if all four-valued replies on all words of length less than d agree. The finite embedding's cutoff is exactly the existing decompose pattern. At d equal to h plus one this is precisely the inclusive prefix through depth h, including early terminal children and all absent descendants.")),
                    Paragraph(Text("The existing depthEquiv inverse laws supply both directions of the cylinder. Every native filling of cutoff(h+1,T) has exactly the prescribed inclusive table; every finite tree with that table is such a filling. No inverse law, finite readout implementation or original-prefix locality proof is duplicated. No equality of the boundary replies at the unobserved exact depth h+1 is asserted."))
                ), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("native-completion-simultaneous-prefix-disequality"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Observer/NativeCompletionPrefixLifting.simultaneous_prefix_disequality"),
                H("One finite tuple preserves independent infinite-tree prefixes"), SeparationStatement(),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The input fixes arbitrary natural ranks n and arbitrary finite coordinates f, together with one finite joint witness for the whole finite list of disequalities. RankedExpr and fixedEval are the existing native mixed-expression syntax and interpretation. The residual coordinates are partitioned into fixed Fin r and live Fin m coordinates by the existing sum equivalence. The fixed coordinates never change; repeated uses of a residual name use that same original coordinate and its same holes.")),
                    Paragraph(Text("Each supplied completion has an actual infinite branch: there is a function from Nat to Bool whose finite initial word exists at every depth. A new induction on a present address gives a reached frontier position in each cutoff. Applying it to that supplied branch proves liveness at every cut without compactness or a new Koenig assumption. Infinity is not replaced by liveness at one requested depth.")),
                    Paragraph(Text("For each independently chosen height h(i), use cutoff(h(i)+1,T(i)). Apply the existing simultaneous_prefix_separation once to the complete list and all these independent live patterns. Its canonical prefixTuple is a finite filling in every coordinate. The exact cylinder bridge transports these fillings to the original complete four-valued tables. The same tuple satisfies every listed disequality at the unchanged n and f.")),
                    Paragraph(Text("The list may be empty or contain repetitions. Residual names may repeat or remain unused. There is no finite rank bound and no synchronization of the coordinate heights. When m is zero the live tuple is empty and the fixed f itself carries the supplied disequalities. When the list is empty every finite tuple extending the prescribed tables satisfies its empty conjunction.")),
                    Paragraph(Text("This establishes the completion-tree prefix-preserving simultaneous disequality statement. It makes no claim about the full Functional Joint Contact theorem, Presburger elimination, acquisition costs or resource guarantees. The bridge and simultaneous conclusion are repository-derived applications of the pinned final-coalgebra machinery and the existing native finite separation theorem; no literature originality is claimed. An unknown audit continuation is not a theorem of undecidability or inexhaustibility."))
                ), DescribeRole.Theorem)
        )));

    private static StatementSource CylinderStatement()
    {
        var d = Seq(V("h"), Sp, Plus, Sp, D(1));
        var p = Call("cutoff", d, V("T"));
        var table = All("a", V("Address"), Imp(LeOf(Call("length", V("a")), V("h")),
            EqOf(Call("readout", V("a"), V("t")), Call("completionReadout", V("a"), V("T")))));
        var filling = Some("w", Arr(Call("Frontier", p), V("Source")), EqOf(V("t"), Call("fill", p, V("w"))));
        return StatementSource.FromAuthor(Disp(All("h", V("Nat"), All("T", V("CompletionTree"),
            All("t", V("Source"), IffOf(table, filling))))));
    }

    private static StatementSource SeparationStatement()
    {
        var coord = Call("Fin", V("m"));
        var expr = Call("RankedExpr", V("k"), Seq(V("r"), Sp, Plus, Sp, V("m")));
        var pair = Call("Prod", expr, expr);
        Formula Negatives(Formula z) => All("e", pair, Imp(Mem(V("e"), V("L")),
            NeOf(Call("fixedEval", V("n"), V("f"), z, Call("fst", V("e"))),
                Call("fixedEval", V("n"), V("f"), z, Call("snd", V("e"))))));
        var witness = Some("w", Arr(coord, V("Source")), Negatives(V("w")));
        var branches = All("i", coord, Call("HasInfiniteBranch", Call("T", V("i"))));
        var prefixes = All("i", coord, All("a", V("Address"),
            Imp(LeOf(Call("length", V("a")), Call("h", V("i"))),
                EqOf(Call("readout", V("a"), Call("z", V("i"))),
                    Call("completionReadout", V("a"), Call("T", V("i")))))));
        var conclusion = Some("z", Arr(coord, V("Source")), AndOf(prefixes, Negatives(V("z"))));
        return StatementSource.FromAuthor(Disp(All("k,r,m", V("Nat"), All("L", Call("List", pair),
            All("n", Arr(Call("Fin", V("k")), V("Nat")), All("f", Arr(Call("Fin", V("r")), V("Source")),
                Imp(witness, All("T", Arr(coord, V("CompletionTree")), Imp(branches,
                    All("h", Arr(coord, V("Nat")), conclusion))))))))));
    }

    private static Formula V(string n) => F.Id(n);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Call(string n, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(n))), [.. args]);
    private static Formula EqOf(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula NeOf(Formula a, Formula b) => Seq(a, Sp, Neq, Sp, b);
    private static Formula LeOf(Formula a, Formula b) => Seq(a, Sp, Le, Sp, b);
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));
    private static Formula IffOf(Formula a, Formula b) => Seq(Par(a), Sp, Iff, Sp, Par(b));
    private static Formula Arr(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula Mem(Formula a, Formula b) => Seq(a, Sp, InMacro, Sp, b);
    private static Formula AndOf(Formula a, Formula b) => Seq(Par(a), Sp, Land, Sp, Par(b));
    private static Formula All(string ns, Formula t, Formula b) => Seq(Forall, Sp,
        Seq(ns.Split(',').Select((n, i) => i == 0 ? V(n) : Seq(Comma, Sp, V(n))).ToArray()),
        Colon, Sp, t, Comma, Sp, Par(b));
    private static Formula Some(string ns, Formula t, Formula b) => Seq(Exists, Sp,
        Seq(ns.Split(',').Select((n, i) => i == 0 ? V(n) : Seq(Comma, Sp, V(n))).ToArray()),
        Colon, Sp, t, Comma, Sp, Par(b));
}
