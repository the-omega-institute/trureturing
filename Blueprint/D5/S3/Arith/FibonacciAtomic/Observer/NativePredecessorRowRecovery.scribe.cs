using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer;
internal sealed class NativePredecessorRowRecoveryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Observer/NativePredecessorRowRecovery.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "NativePredecessorRowRecovery", H("Native predecessor-row recovery"), Blocks(
            Entry("H", "Old reached occurrences", "H extracts the finite hole-address set from the entire canonical old row. The existing literalRow_hole_support and canonicalRow_reached identify it with the reached public cuts. Empty cuts, root cuts and absent deeper cuts are included.", DescribeRole.Definition),
            Entry("sigma", "Substitution with opaque markers", "The native Source is FreeMagma Bool, with true alpha and false beta. Opaque substitution sends concrete alpha to beta and concrete beta to the ordered pair of beta and alpha. Every equality-class marker is fixed, and every ordered bracket is retained.", DescribeRole.Definition),
            Entry("repairAt", "Repair at actual occurrence addresses", "The finite traversal carries its current address. An occurrence in the supplied old set stays an opaque marker, renamed by ActualCutPartitionDecoder.decoderClass on that restricted support. A newborn marker is restored to beta at a final false edge and alpha at a final true edge. A newborn root is rejected. Concrete leaves and ordered pairs retain their syntax. Decisions use occurrence membership even when an old and a newborn occurrence share one current class. Class names are first-hole ordinals and can be sparse.", DescribeRole.Definition),
            Entry("repair", "Whole-row repair", "Repair starts the address traversal at the root. On an actual one-step transition, contextual induction over the original source proves repair of the current row equals opaque substitution of the old canonical row. Old cut stops use equality-kernel preservation under the existing injective native substitution and idxOf_map_relation. An alpha leaf produces beta. A beta leaf produces a beta/alpha pair whose separately optional child cuts are restored by their final edges. A source pair recursively preserves both sides. Prefix freedom permits descent without a strict cut ancestor.", DescribeRole.Definition),
            Entry("delta", "Finite opaque image parsing", "Beta parses to alpha, a bare alpha fails, and an opaque marker stays fixed. The exact ordered beta/alpha pair parses to beta before the general-pair rule recursively parses both children. An opaque substitution image cannot be a concrete alpha, so the special block cannot collide with a pair of opaque images. Structural induction proves parsing after opaque substitution returns the entire input term.", DescribeRole.Definition),
            Entry("back", "Uniform partial predecessor decoder", "Back composes repair with opaque parsing. Its runtime arguments are only the current LiteralRow and old reached CutSet; it receives no source, source value, alpha-class supplement, rank or depth bound. Finite structural recursion terminates, with no further complexity claim.", DescribeRole.Definition),
            Entry("native_predecessor_row_recovery", "Exact recovery and conditional equivalence", "For every finite prefix-free public cut and every finite native source, Back returns exactly some of the old canonical row after one actual native substitution. The complete exterior, all reached occurrences, the entire equality/disequality partition and absent-cut guards are therefore recovered. For two actual sources with equal current rows, their old rows agree exactly when their old reached sets agree. The forward implication extracts support; the reverse uses identical decoder inputs and exact recovery. The original-present transport supplier is NativeDepthPatterns.original_present_transport at epoch one. Source injectivity is reused from SourceTransportCentralizer.source_transport_centralizer. Neither full-image choice inversion nor common-suffix recutting is a runtime operation. Successful parsing of an alleged row and set certifies no physical provenance, continuity, origin or inverse action. These are source-specific deductions using known finite syntax and partition methods, with no claim of literature priority.", DescribeRole.Theorem)
        )));
    private static DocumentBlock Entry(string n, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("nativepredecessorrowrecovery-" + n.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + n), H(title), Statement(n),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
    private static StatementSource Statement(string n)
    {
        if (n != "native_predecessor_row_recovery") return StatementSource.WithoutFormula();
        Formula Row(Formula v) => Call("canonicalRow", V("P"), v);
        Formula Current(Formula v) => Row(Call("substitution", v));
        Formula Old(Formula v) => Call("H", V("P"), v);
        var recovery = All("v", V("Source"), EqOf(
            Call("back", Current(V("v")), Old(V("v"))), Call("some", Row(V("v")))));
        var conditional = All("v,w", V("Source"), Imp(
            EqOf(Current(V("v")), Current(V("w"))),
            IffOf(EqOf(Row(V("v")), Row(V("w"))), EqOf(Old(V("v")), Old(V("w"))))));
        return StatementSource.FromAuthor(Disp(All("P", V("CutSet"),
            Imp(Call("CutPrefixFree", V("P")), And(recovery, conditional)))));
    }
    private static Formula V(string n) => F.Id(n);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Call(string n, params Formula[] args) => new Formula.Apply(Seq(Operatorname, Grp(V(n))), [.. args]);
    private static Formula EqOf(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula And(Formula a, Formula b) => Seq(Par(a), Sp, Land, Sp, Par(b));
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));
    private static Formula IffOf(Formula a, Formula b) => Seq(Par(a), Sp, Iff, Sp, Par(b));
    private static Formula All(string ns, Formula t, Formula b) => Seq(Forall, Sp,
        Seq(ns.Split(',').Select((n, i) => i == 0 ? V(n) : Seq(Comma, Sp, V(n))).ToArray()), Colon, Sp, t, Comma, Sp, Par(b));
}
