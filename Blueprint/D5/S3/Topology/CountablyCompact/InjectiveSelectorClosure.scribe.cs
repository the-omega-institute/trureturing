using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.CountablyCompact;

internal sealed class InjectiveSelectorClosureDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Topology/CountablyCompact/InjectiveSelectorClosure.";
    private static Formula V(string n) => FormulaDsl.Id(n);
    private static Formula All(string n, Formula t) => Seq(Forall, Sp, V(n), Colon, Sp, t, Comma, Sp);
    private static Formula Ex(string n, Formula t) => Seq(Exists, Sp, V(n), Colon, Sp, t, Comma, Sp);
    private static Formula Fn(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula S(string n) => Call("Set", V(n));
    private static Formula Card(Formula a) => Call("Card", a);
    private static Formula Small(Formula a) => Seq(Card(a), Sp, Le, Sp, V("c"));
    private static Formula Sub(Formula a, Formula b) => Seq(a, Sp, Subseteq, Sp, b);
    private static Formula And(params Formula[] terms) => Seq(terms.SelectMany((f, i) =>
        i == 0 ? new[] { f } : new[] { Sp, Land, Sp, f }).ToArray());
    private static Formula Imp(Formula a, Formula b) => Seq(Grp(a), Sp, Rightarrow, Sp, b);
    private static Formula Common => Seq(All("X", V("Type")), All("B", V("Type")),
        All("q", Fn(V("X"), V("B"))));
    private static Formula FreshSupply => Seq(All("i", V("I")), All("F", S("B")),
        Imp(Small(V("F")), Seq(Ex("x", V("X")), And(
            Seq(V("x"), Sp, InMacro, Sp, Call("A", V("i"))),
            Seq(Neg, Grp(Seq(Call("q", V("x")), Sp, InMacro, Sp, V("F"))))))));
    private static Formula FreshStatement => Disp(Seq(Common, All("I", V("Type")),
        All("A", Fn(V("I"), S("X"))), All("H", S("X")),
        Imp(And(Small(V("I")), Small(V("H")), FreshSupply),
            Seq(Ex("f", Fn(V("I"), V("X"))), And(
                Grp(Seq(All("i", V("I")), Call("f", V("i")), Sp, InMacro, Sp, Call("A", V("i")))),
                Call("Injective", Call("compose", V("q"), V("f"))),
                Seq(All("i", V("I")), Neg, Grp(Seq(Call("q", Call("f", V("i"))), Sp, InMacro, Sp,
                    Call("image", V("q"), V("H"))))))))));
    private static Formula ClosureStatement => Disp(Seq(Common,
        Call("TopologicalSpace", V("X")), Sp, Comma, Sp, Call("TOneSpace", V("X")), Sp, Comma, Sp,
        All("Good", S("X")), All("Szero", S("X")),
        Imp(And(Call("FreshClusterSupply", V("Good"), V("q")), Sub(V("Szero"), V("Good")),
                Small(V("Szero")), Call("InjOn", V("q"), V("Szero"))),
            Seq(Ex("S", S("X")), And(Sub(V("Szero"), V("S")), Sub(V("S"), V("Good")),
                Small(V("S")), Call("InjOn", V("q"), V("S")), Call("IsCountablyCompact", V("S")))))));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Fresh accumulation-point supply constructs a countably compact injective extension of every continuum-sized admissible seed.",
        H("Countably compact injective closing-off"), Blocks(
            Paragraph(Text("All object types X, B and I are in Type, and c denotes the continuum. The map q is arbitrary. "
                + "FreshClusterSupply(Good,q) means the following: for every embedding e from the natural numbers into X with range(e) contained in Good "
                + "and q composed with e injective, and every F contained in B of cardinal at most c, there is x in Good with "
                + "AccPt x (principal(range(e))) and q(x) outside F. AccPt and IsCountablyCompact have their ambient Mathlib meanings.")),
            Describe.Lean(DescribeId.Create("fresh-simultaneous-choice"), DeclarationHandle.Create(Owner + "exists_fresh_choice"),
                H("Simultaneous representatives with distinct values"), StatementSource.FromAuthor(FreshStatement), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any family of at most c tasks, each admitting a witness outside every at most c forbidden set of q-values, "
                    + "well-founded recursion along WellOrderingRel constructs one representative for each task. At task i, forbid q(H) and the image "
                    + "of all earlier representatives. Each prefix has cardinal at most that of the entire task type; its image together with q(H) "
                    + "has cardinal at most c. The recursion equation proves membership, pairwise distinct q-values and avoidance of q(H). "
                    + "No regularity of c, injectivity on H, or topology is required for this helper."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("countably-compact-injective-extension"),
                DeclarationHandle.Create(Owner + "exists_countablyCompact_injOn_extension"), H("Actual countably compact extension"),
                StatementSource.FromAuthor(ClosureStatement), AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Topology/ginsburgsaks1975ultrafilters"),
                    LibraryNoteRef.Create("D5/L/Topology/frolik1960countablycompact")), Blocks(
                    Paragraph(Text("X is an arbitrary T1 space. Starting with any Szero contained in Good, of cardinal at most c, and on which q is injective, "
                        + "the conclusion constructs S containing Szero, contained in Good, of cardinal at most c, with q injective on S and S countably compact. "
                        + "Empty and finite seeds are included. No continuity of q, first countability, sequential compactness, CH, MA, "
                        + "or regularity of the continuum is assumed.")),
                    Paragraph(Text("For one step from S, the task type is all embeddings from the natural numbers into S. Its cardinal is bounded by "
                        + "Card(S) to the power aleph0, hence by c. Fresh simultaneous choice adds an ambient accumulation point for each embedding, "
                        + "avoiding both q(S) and the values of earlier new points. The resulting extension is small, good and injective. "
                        + "The tasks at this step refer to S, so later steps process newly added points.")),
                    Paragraph(Text("Use omega1.ToType as the index type. The actual well-founded recursion defines stage(i) as Szero union all "
                        + "one-step extensions of stage(j) for j less than i. The recursion equation proves that zero is Szero, a successor is "
                        + "the one-step extension of its predecessor, and a nonzero limit is the union of its earlier stages. "
                        + "Induction using these equations proves containment in Good, the cardinal bound and injectivity; the stages form an increasing chain. "
                        + "The final union is small because aleph1 is at most c. For an infinite subset, select an embedding of the natural numbers into it. "
                        + "Ordinal.iSup_lt_omega_one bounds all appearance stages below omega1. The next stage supplies an ambient AccPt of the range, "
                        + "which remains an AccPt of the original larger subset. The native infinite-subset characterization proves IsCountablyCompact.")),
                    Paragraph(Text("The fixed-D source's Theorem 2.12 and preceding construction, printed pages 407-408, provide the classical "
                        + "omega1 closing-off method. For a completely regular space X, that construction closes under the D-limits of sequences "
                        + "inside beta X for one fixed free ultrafilter D. It is method background for the independent Mathlib implementation here, "
                        + "not the exact arbitrary T1 theorem with preservation of an arbitrary q-injective good set. Both exact Lean statements remain "
                        + "repository-derived. Example 5.2, printed page 413, explicitly credits Frolik and invokes 2^c closure points and disjoint added sets; "
                        + "it does not prove the independent-family cardinal theorem on that page.")),
                    Paragraph(Text("The acknowledged primary source's Lemma 2.8, printed pages 333-334, directly attests that for separable metrizable P, "
                        + "every infinite M contained in beta P with no accumulation point in P has 2^c accumulation points in beta P. "
                        + "Lemma 2.9, printed page 334, gives a countably compact R with P contained in R contained in beta P minus M and cardinal at most c "
                        + "for M contained in beta P minus P of cardinal strictly below 2^c. Its proof selects accumulation points outside M "
                        + "and closes off through omega1; each countably infinite subset lies in a bounded stage. Abundance, cardinal avoidance and omega1 closing-off "
                        + "are classical methods. The primary proof invokes Pospisil's cardinal theorem and credits Katetov for the simple proof of Lemma 2.8; "
                        + "these credits are attested by Frolik, without independent reading of their originals. The reading is of scanned pages, not extracted article text. "
                        + "Neither lemma states the exact arbitrary T1/q-injective good-set theorem or the Feldman-Wilce graph endpoint. "
                        + "This passage-level comparison makes no broad literature absence claim; both exact Lean statements retain repository-derived provenance.")),
                    Paragraph(Text("Feldman and Wilce, A Note on Compactness and Clique Size, arXiv:2608.13320v1, Question 1 on page 5 and the sufficient construction "
                        + "on page 10, provide the research target. The present theorem supplies the generic closure step; it does not assert that the paper "
                        + "already constructs its missing set Y. Application to that question still requires free-ultrafilter cardinal supply, "
                        + "fresh good accumulation points with distinct projected values, a section-dense injective seed, construction of Y, and the graph argument. "
                        + "The classical method, the exact abstract theorem, and original Question 1 are distinct claims; no novelty, unique status, "
                        + "original-problem completion or official acceptance is asserted."))),
                DescribeRole.Theorem))));
}
