using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.ExtremallyDisconnected;

internal sealed class PointPairSeparationDocument : IScribeDocumentDefinition
{
    private static Formula V(string name) => F.Id(name);
    private static Formula All(string name, Formula type) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp);
    private static Formula Fn(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula Inst(string name) =>
        Seq(OpenBracket, Call(name, V("E")), CloseBracket, Sp);
    private static Formula Eventually(Formula condition) =>
        Call("Eventually", V("atTop"), Grp(Seq(V("n"), Sp, Mapsto, Sp, condition)));
    private static Formula Test => Seq(
        Call("mem", Call("p", V("n")), V("U")), Sp, Leftrightarrow, Sp,
        Call("mem", Call("q", V("n")), V("U")));
    private static Formula Statement => Disp(new Formula.Aligned([
        Seq(All("u", V("UniverseLevel")), All("E", Seq(V("Type"), Underscore, Grp(V("u")))),
            Inst("TopologicalSpace"), Inst("T2Space"), Inst("ExtremallyDisconnected")),
        Seq(All("p", Fn(V("Nat"), V("E"))), All("q", Fn(V("Nat"), V("E")))),
        Seq(Grp(Seq(All("U", Call("Set", V("E"))), Call("IsClopen", V("U")),
            Sp, Rightarrow, Sp, Eventually(Test))), Sp, Rightarrow, Sp,
            Eventually(Seq(Call("p", V("n")), Sp, Eq, Sp, Call("q", V("n")))))
    ]));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Each clopen test has its own eventual cutoff; the pair sequences nevertheless become equal.",
        H("Eventual equality from clopen tests"),
        Blocks(Describe.Lean(
            DescribeId.Create("point-pair-eventual-equality"),
            DeclarationHandle.Create("D5/S3/Topology/ExtremallyDisconnected/PointPairSeparation.eventually_eq_of_eventually_mem_isClopen_iff"),
            H("Exact point-pair separation theorem"),
            StatementSource.FromAuthor(Statement),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "E is any Hausdorff extremally disconnected space, and p and q are arbitrary natural-number indexed point sequences. "
                    + "Eventually(atTop, R(n)) means there exists N such that R(n) holds for every n at least N. "
                    + "The premise quantifies over every ambient clopen U and allows N to depend on U. The conclusion is eventual equality. "
                    + "There is no compactness, uniform clopen cutoff, preselected shell family, or no-pairs axiom.")),
                Paragraph(Text(
                    "If equality is not eventual, the unequal original indices form an infinite pool. At each stage both endpoints of every pool pair lie in a clopen C. "
                    + "Pinned Mathlib's Hausdorff extremally disconnected instance supplies total separation, hence a clopen separating a chosen pair. "
                    + "Delete its finite exceptional initial segment and the indices through the chosen pair. Split the remaining infinite pool by clopen membership and retain an infinite side. "
                    + "Both endpoints remain on that side. Name the discarded endpoint x and the retained endpoint y; their orientation relative to p and q is allowed to vary. "
                    + "The resulting original indices k are strictly increasing, the clopen shells D are disjoint, and y(i) can enter only a later shell, uniquely if it enters any.")),
                Paragraph(Text(
                    "Define r(i) to be that unique shell index when it exists and i otherwise. The recursion b(0)=0 and b(n+1)=max(b(n),r(b(n)))+1 "
                    + "gives full rectangular avoidance: y(b(n)) misses D(b(m)) for every n and m. A no-shell companion automatically satisfies this assertion. "
                    + "For A contained in Nat put O(A)=union of D(i) over i in A and Q(A)=closure(O(A)). Extremal disconnectedness makes Q(A) clopen. "
                    + "Mathlib's disjoint-open-closure theorem makes Q(A) and Q(B) disjoint for disjoint index sets A and B. "
                    + "When S minus A is finite, Q(S) is contained in Q(A) union the finitely many error shells: that union is closed and contains O(S).")),
                Paragraph(Text(
                    "Starting with range b, split each infinite pool into disjoint infinite even and odd enumerated halves. Choose a half whose Q-set excludes the next enumerated companion y(b(n)). "
                    + "This does not require b(n) to belong to the current pool. Select a strictly increasing diagonal a(n) from the nth pool. "
                    + "Its infinite range S lies in range b and has only finitely many points outside each fixed pool, all among the initial diagonal values. "
                    + "Finite-error containment and rectangular avoidance imply that Q(S) excludes every y(b(n)), while it contains x(i) for all i in S. "
                    + "The one clopen Q(S) therefore separates infinitely many original pairs at k(i), contradicting its own eventual membership agreement in either orientation.")),
                Paragraph(Text(
                    "This is a direct formal dependency proof for the cited CH analytic uniform-separation consumer. The supplied unpublished ordinary argument is fallible prior research, "
                    + "not Lean evidence or a classical source attribution. Pinned Mathlib supplies the topological separation and closure facts and elementary infinite-set tools; "
                    + "the shell, sparse avoidance and diagonal construction are assembled here. Repository-derived provenance makes no claim of mathematical novelty. "
                    + "The actual continuous-dual norm transfer, compact lower-semicontinuous minimum argument, full signed dual-ball endpoint, and full CH construction are outside this module.")),
                Paragraph(Text(
                    "The escape registration is declared_unresolved, with IE-C050 source.selection_missing. "
                    + "Its typed dependent-family bridge, actual-positive law, variation, sensitivity and observational-dependence proof fields compile, "
                    + "but the raw sourceSelection field is absent (sourceSelection := none), so source reconstruction and binding have not been validated. "
                    + "The unfinished audit is tracked at https://github.com/the-omega-institute/trureturing/issues/20638. "
                    + "Compilation of these typed fields and the issue link do not establish declared_validated."))),
            DescribeRole.Theorem))));
}
