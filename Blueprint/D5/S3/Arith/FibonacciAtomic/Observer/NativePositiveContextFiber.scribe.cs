using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer;
internal sealed class NativePositiveContextFiberDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Observer/NativePositiveContextFiber.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "NativePositiveContextFiber", H("Positive contexts and unrestricted role valuations"), Blocks(
            Entry("WellAddressed", "Original addressed exterior", Blocks(
                Paragraph(Text("Source is the free ordered binary tree on Boolean leaves. A HoleExterior has either a concrete Boolean leaf, an original hole address, or an ordered pair. For a finite cut P, WellAddressed checks the displayed syntax from a specified current address: concrete leaves and pairs lie outside P; every hole is labelled by precisely its current address in P; pair children continue at the original left and right addresses.")),
                Paragraph(Text("The condition is syntactic and independent of any source or valuation. It does not assume that P is prefix-free. Cuts lying below an already displayed hole are not exposed by this exterior, so no preservation of their individual reach status is asserted."))
            ), DescribeRole.Definition),
            Entry("PositiveContext", "Independent exterior and positive role equalities", Blocks(
                Paragraph(Text("A role label assigns a natural name to each original address. ActualCutPartitionDecoder.nameExterior replaces the addressed holes in X by their role names and retains every concrete leaf and ordered pair. PositiveContext means that cutting the original source produces exactly X and that any two displayed holes with the same role have equal original subtrees. It imposes no inequality between different roles.")),
                Paragraph(Text("A representative map chooses one displayed occurrence of every supported role. The premise concerns only names in labels(nameExterior(label,X)); unused names and their representatives have no constraint. The independent exterior equality ensures that all displayed role occurrences, including the chosen representatives, are reached in the source."))
            ), DescribeRole.Definition),
            Entry("positive_context_history_exact", "Exact finite history for a positive context", Blocks(
                Paragraph(Text("expression turns a role row into a native MixedExpr: a concrete Boolean leaf is a ground tree, a role is a generator with substitution power zero, and an ordered pair is preserved. The existing compiler runs at the original root with the chosen representative map. It receives neither a source nor a role valuation.")),
                Paragraph(Text("The equivalence retains the complete concrete exterior and all within-role equalities. Every compiler link is an actual guarded positive equality, so both endpoints must be reached. Structural induction on the addressed exterior relates compiler literals and links to the independent cut and representative equalities. Transitivity recovers every pairwise equality for a repeated role.")),
                Paragraph(Text("The finite context may be completely ground, have no supported roles, or consist only of a root hole. Repeated roles and equal values at different roles are permitted. Concrete terminal leaves exclude hidden descendants, while values inserted at displayed holes have no size bound."))
            ), DescribeRole.Theorem),
            Entry("recoverRoles", "Explicit inverse by representative readout", Blocks(
                Paragraph(Text("For each supported role, recoverRoles reads its original representative subtree. The total function has a fixed Boolean default, but reachedness is proved on every source in PositiveContext before that default is eliminated. This is a mathematical source operation and supplies no observer-accessible equality port."))
            ), DescribeRole.Definition),
            Entry("positiveContextEquiv", "Unrestricted valuation and source equivalence", Blocks(
                Paragraph(Text("With the same well-addressed and representative hypotheses, positiveContextEquiv is an equivalence from all functions Classes(nameExterior(label,X)) to Source onto the subtype of sources satisfying PositiveContext. Classes contains exactly the supported role names. The forward map fills the row using evaluateRow and extend; the inverse reads the representatives with recoverRoles.")),
                Paragraph(Text("The existing unrestricted rowAt_evaluate theorem proves that filling reaches each representative with its assigned value. NativePayloadHistoryInstallation.payload_history_exact then identifies the whole root source with the evaluated row. These facts establish both inverse equations, including the empty role domain. No injectivity of the role valuation is assumed; the distinct-class condition in NativeCutFibers.LegalValues belongs to the separate full-partition problem.")),
                Paragraph(Text("This finite-tree reconstruction uses ordinary structural induction and existing native evaluation results; no literature-originality claim is made. It supplies the original-exterior and within-role part of a positive correspondence. Atomic feedback, rank-only refinements, different-role inequalities, additional negative records and the complete acquired-fiber construction remain separate conditions. No arbitrary-policy decision procedure or complexity bound follows here."))
            ), DescribeRole.Definition)
        )));
    private static DocumentBlock Entry(string n, string title, BlockSequence prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("native-positive-context-" + n.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + n), H(title), Statement(n),
            AssessedProvenance.FromRepo(), prose, role);
    private static StatementSource Statement(string n)
    {
        if (n != "positive_context_history_exact") return StatementSource.WithoutFormula();
        var c = Call("nameExterior", V("label"), V("X"));
        var representatives = All("n", V("Nat"), Imp(
            Seq(V("n"), Sp, InMacro, Sp, Call("labels", c)),
            EqOf(Call("rowAt", Call("rep", V("n")), c),
                Call("some", Call("of", Call("inr", V("n")))))));
        var positive = Call("PositiveContext", V("P"), V("X"), V("label"), V("U"));
        var history = Call("Holds", V("U"), Call("compile", V("rep"), V("nil"), Call("expression", c)));
        Formula result = All("U", V("Source"), Seq(Par(positive), Sp, Iff, Sp, Par(history)));
        result = Imp(representatives, result);
        result = Imp(Call("WellAddressed", V("P"), V("nil"), V("X")), result);
        result = All("rep", Arr(V("Nat"), V("Address")), result);
        result = All("label", Arr(V("Address"), V("Nat")), result);
        result = All("X", V("HoleExterior"), result);
        result = All("P", V("CutSet"), result);
        return StatementSource.FromAuthor(Disp(result));
    }
    private static Formula V(string n) => F.Id(n);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Call(string n, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(n))), [.. args]);
    private static Formula EqOf(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula Arr(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));
    private static Formula All(string n, Formula t, Formula b) =>
        Seq(Forall, Sp, V(n), Colon, Sp, t, Comma, Sp, Par(b));
}
