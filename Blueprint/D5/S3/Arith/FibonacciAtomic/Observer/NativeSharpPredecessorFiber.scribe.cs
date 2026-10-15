using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer;
internal sealed class NativeSharpPredecessorFiberDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Observer/NativeSharpPredecessorFiber.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "NativeSharpPredecessorFiber", H("Sharp native predecessor fibers"), Blocks(
            Entry("right_birth", "Right-Child Birth on Every Actual Transition", "For every legal finite parent address q and every original source v, if its current right child is present, its predecessor right child is absent exactly when the current child is alpha. This theorem applies to all sources and addresses, independently of the comb witness family. Whole-row support repair uses it for either child together with equality of the two child-presence flags.", DescribeRole.Theorem),
            Entry("position", "Native child-cut sites", "For k=n+1, position i is hole n i followed by the true edge. The arbitrary-size right-comb context, its hole addresses and its complete address/suffix law are reused directly from FiniteHereditaryPatternRealization.B_T, hole, hole_locate and result. The unique hole/suffix law proves that this single finite public cut is prefix-free. No bound on n or source size is imposed.", DescribeRole.Definition),
            Entry("cut", "One fixed public cut", "The cut is the image of all Fin(n+1) indices under position. It is shared by every selector and every actual origin in the family.", DescribeRole.Definition),
            Entry("site", "Changing old constructors", "A selected old site is beta. Every other old site is the ordered pair of alpha and an arbitrary native tag. After one genuine native update the selected site is the pair of beta and alpha, while an unselected site is the pair of beta and the native image of its tag. The uniform installation identity retains the whole common exterior, stopping at the right child of each site. Its contextual induction uses the existing comb rather than reproving its geometry.", DescribeRole.Definition),
            Entry("origin", "Actual joint native witnesses", "For any injective tag family z:Fin(k) to FreeMagma Bool and selector a:Option(Fin(k)), fill the existing comb by site(z i,a=some i). None selects no site. Some i selects exactly i. These are k+1 complete actual origins of the same native register at public current epoch one; every comparison is between complete jointly attained sources. Injectivity of substitution and exclusion of alpha from its image are reused from SourceTransportCentralizer.source_transport_centralizer and IntrinsicSubstitutionCoordinates.no_alpha. Hence the k hidden current values are pairwise distinct for every selector. The source's specified orbit tags rho^(i+1) alpha are an exact specialization, not a restriction on the theorem.", DescribeRole.Definition),
            Entry("current", "The complete common current row", "Current is the entire canonical row of the none origin after one update. Equality is established through ActualCutPartitionDecoder.canonicalRow_record_iff, including the whole exterior and the ordered equality/disequality partition. Every child cut is reached. Old support is the full cut for none and the cut with position i erased for some i. The old selected beta is a concrete strict-prefix absence guard; canonicalRow_absent_guard preserves all other absent-cut guards.", DescribeRole.Definition),
            Entry("className", "Only occurring native class names", "Each site names its actual current class by classOrdinal at that site. The existing labels_canonical and classOrdinal_eq_iff identify the finite set of occurring names with the injective image of Fin(k). Raw first-occurrence ordinals need not be consecutive. Counts and supplementary labels use these occurring classes.", DescribeRole.Definition),
            Entry("ActualPredecessors", "The entire actual current-row fiber", "ActualPredecessors contains every finite FreeMagma Bool source v whose native image has the common entire current row. There is no restriction to the selected witness family, its tags, size, inverse depth or a finite list of sources. At each right cut, old absence is equivalent to a current alpha value. The complete singleton partition permits at most one such value. Thus old support is exactly the full cut or one site erased. NativePredecessorRowRecovery.native_predecessor_row_recovery identifies old-row equality with old-support equality under the common current row. Every possible old row is consequently attained by exactly one family selector. The number of origins in this fiber is not claimed finite. When k is at least two, two different selected sites have the same number of old reached holes and newborn holes, but different predecessor rows. Retaining only the newborn count therefore cannot recover the predecessor.", DescribeRole.Definition),
            Entry("Encodable", "Exact recovery with a supplement", "Encodable quantifies a supplementary configuration for each compatible actual origin and one deterministic decoder taking only that configuration; the fixed complete base is the public cut, current row, origin-continuity condition and epoch one. Correctness is demanded on the entire actual fiber. The supplement may be selected from already acquired information. This mathematical existence statement supplies no source query, acquisition optimum, runtime semantic-alpha oracle, physical authentication or effective feasibility oracle. A larger accessible source-dependent base can reduce the fiber and its minimum.", DescribeRole.Definition),
            Entry("Sharp", "All sharpness and capacity clauses", "For k=n+1, Sharp requires prefix freedom, equality of all k+1 complete current rows, exactly k occurring classes, the full/one-erased old supports, distinct whole predecessor rows, equality of their finite image with the whole attained old-row image, and exactly k+1 image values. For every configuration count m, exact recovery exists precisely when k+1 is at most m. For every fixed binary width b, it exists precisely when Nat.clog 2 (k+1) is at most b. This is the integer ceiling of the binary logarithm, characterized by Nat.clog_le_iff_le_pow and Nat.le_pow_clog.", DescribeRole.Definition),
            Entry("native_sharp_predecessor_fiber", "The full native sharp predecessor fiber", "The theorem holds for every n and every injective native tag family. In the displayed formula NativeTags(n) means Fin(n+1) to Source and oldRows(n,z) means the function a to canonicalRow(cut(n),origin(n,z,a)). The uniform installation identity handles changing old constructors under the same current child cut. The exact exterior and full partition then give the common canonical row before predecessor recovery or counting. NativeCutFibers.labels_canonical identifies occurring classes without consecutive-ordinal assumptions. The entire actual-fiber exhaustion and NativePredecessorRowRecovery supply sharp upper equality, not merely k+1 witnesses. Correct decoding implies an injection of the k+1 distinct old rows into configurations; FiniteIdentificationCapacityBound.finite_identification_capacity_bound supplies the lower bound. Conversely, choose the attained old-support selector and embed it into any sufficiently large finite configuration space. The decoder inverts that embedding and applies NativePredecessorRowRecovery.back to the public current row and the selected full or one-erased cut. It accesses no hidden native tag or newly acquired semantic value. Binary function-space cardinality and the pinned upper-logarithm equivalence supply both directions for bits. The same correct encoder satisfies FiniteIdentificationCapacityBound.cost_form: log base two of k+1 is at most the logarithm of its configuration capacity. Real.natCeil_logb_natCast identifies the integer minimum with the ceiling of the real binary logarithm. The configuration count excludes the public dictionary, cut addresses, current row, epoch, authentication, workspace, output and acquisition. These are source-specific deductions using existing context, finite identification and native recovery methods, with no literature-priority claim.", DescribeRole.Theorem)
        )));
    private static DocumentBlock Entry(string n, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("nativesharppredecessorfiber-" + n.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + n), H(title), Statement(n),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
    private static StatementSource Statement(string n) => n == "right_birth"
        ? BirthStatement()
        : n == "native_sharp_predecessor_fiber"
        ? StatementSource.FromAuthor(Disp(All("n", V("Nat"), All("z", Call("NativeTags", V("n")),
            Imp(Call("Injective", V("z")), Call("Sharp", V("n"), V("z"),
                Call("oldRows", V("n"), V("z"))))))))
        : StatementSource.WithoutFormula();
    private static StatementSource BirthStatement()
    {
        var q=V("q"); var v=V("v");
        var address=Call("append",q,Call("singleton",V("true")));
        var current=Call("subtree",address,Call("rho",v));
        var birth=IffOf(EqOf(Call("subtree",address,v),V("none")),
            EqOf(current,Call("some",Call("of",V("true")))));
        return StatementSource.FromAuthor(Disp(All("q",V("Address"),All("v",V("Source"),
            Imp(Call("isSome",current),birth)))));
    }
    private static Formula IffOf(Formula a,Formula b) => Seq(Par(a),Sp,Iff,Sp,Par(b));
    private static Formula EqOf(Formula a,Formula b) => Seq(a,Sp,Eq,Sp,b);
    private static Formula V(string n) => F.Id(n);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Call(string n, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(n))), [.. args]);
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));
    private static Formula All(string n, Formula t, Formula b) =>
        Seq(Forall, Sp, V(n), Colon, Sp, t, Comma, Sp, Par(b));
}
