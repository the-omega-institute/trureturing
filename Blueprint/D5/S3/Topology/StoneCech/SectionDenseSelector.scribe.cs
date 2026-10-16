using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.StoneCech;

internal sealed class SectionDenseSelectorDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Topology/StoneCech/SectionDenseSelector.";
    private static Formula V(string n) => FormulaDsl.Id(n);
    private static Formula All(string n, Formula t) => Seq(Forall, Sp, V(n), Colon, Sp, t, Comma, Sp);
    private static Formula Ex(string n, Formula t) => Seq(Exists, Sp, V(n), Colon, Sp, t, Comma, Sp);
    private static Formula Mem(Formula a, Formula b) => Seq(a, Sp, InMacro, Sp, b);
    private static Formula And(params Formula[] terms) => Seq(terms.SelectMany((f, i) =>
        i == 0 ? new[] { Grp(f) } : new[] { Sp, Land, Sp, Grp(f) }).ToArray());
    private static Formula Imp(Formula a, Formula b) => Seq(Grp(a), Sp, Rightarrow, Sp, Grp(b));
    private static Formula UfA => Call("Ultrafilter", V("A"));
    private static Formula Density => Seq(All("S", Call("Set", V("A"))),
        Imp(And(Call("Infinite", V("S")), Call("InjOn", V("q"), V("S"))),
            Seq(Ex("u", UfA), And(Mem(V("u"), V("Y")), Mem(V("S"), V("u"))))));
    private static Formula Statement => Disp(Seq(All("A", V("Type")), All("B", V("Type")),
        All("q", Seq(V("A"), Sp, To, Sp, V("B"))),
        Imp(Call("Countable", V("A")), Seq(Ex("Y", Call("Set", UfA)), And(
            Seq(V("Y"), Sp, Subseteq, Sp, Call("SectionGood", V("q"))),
            Seq(Call("Card", V("Y")), Sp, Le, Sp, V("c")),
            Call("InjOn", Call("map", V("q")), V("Y")),
            Call("IsCountablyCompact", V("Y")), Density)))));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A countable source permits simultaneous fresh section witnesses and countably compact injective closing-off.",
        H("Section-dense ultrafilter selectors"), Blocks(
            Paragraph(Text("Here q : A -> B is arbitrary and only the source A is countable. The codomain B has no countability assumption. "
                + "SectionGood(q) means free ultrafilters on A containing an actual injectivity set of q. In the formula Card is Cardinal.mk, "
                + "c is the continuum, and map(q) is Ultrafilter.map q. Infinite(S) means Set.Infinite S. Membership S in u is ultrafilter membership; "
                + "IsCountablyCompact Y is the native ambient predicate on the subset Y of Ultrafilter A.")),
            Describe.Lean(DescribeId.Create("countably-compact-section-dense-selector"),
                DeclarationHandle.Create(Owner + "exists_countablyCompact_sectionDense_selector"),
                H("Constructing the selector and its section density"), StatementSource.FromAuthor(Statement),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Topology/frolik1960countablycompact"),
                    LibraryNoteRef.Create("D5/L/Topology/ginsburgsaks1975ultrafilters"),
                    LibraryNoteRef.Create("D5/L/Topology/feldmanwilce2026compactnesscliques")), Blocks(
                    Paragraph(Text("The conclusion constructs a set Y of section-good ultrafilters, of cardinal at most c, on which Ultrafilter.map q "
                        + "is injective, and which is countably compact. For every infinite S contained in A on which q is injective, some u in Y contains S. "
                        + "There is no assumed section-dense seed or pre-existing selector, no finite-fibre assumption, and no assumed supply of fresh projected values.")),
                    Paragraph(Text("Index the seed tasks by I = {S : Set A // S.Infinite and InjOn q S}. "
                        + "Countability of A bounds Card(I) by Card(Set A)=2^Card(A) <= 2^aleph0=c. "
                        + "This is a bound on subsets of the source, not on subsets of B. A task asks for a free ultrafilter u containing its actual section S, "
                        + "with projected value outside a supplied forbidden set F of cardinal at most c.")),
                    Paragraph(Text("For each task choose an actual embedding e : Nat -> S -> A. Injectivity of q on S makes q composed with e injective. "
                        + "Push each free ultrafilter r on Nat forward by e. The resulting u=map e r is free, contains S and belongs to SectionGood(q). "
                        + "The map identity map q (map e r)=map(q composed with e) r and injectivity of filter pushforward along an embedding "
                        + "prove that these projected values are pairwise distinct. The free-ultrafilter cardinal supplier and Cantor's theorem "
                        + "therefore give a witness outside every such F. This proves the task supply rather than assuming it.")),
                    Paragraph(Text("Apply InjectiveSelectorClosure.exists_fresh_choice to Q=Ultrafilter.map q, these section tasks, and the empty old set. "
                        + "Its well-founded choice forbids all earlier projected values and chooses one witness per task with globally distinct projected values. "
                        + "The range is a seed of cardinal at most c, contained in SectionGood(q), Q-injective and already section-dense. "
                        + "Empty or finite source cases require no invented infinite section: the corresponding task family may be empty.")),
                    Paragraph(Text("The actual theorem SectionGoodFreshClusters.exists_sectionGood_fresh_accPt supplies "
                        + "FreshClusterSupply(SectionGood(q),Q). Feed this and the constructed seed to "
                        + "InjectiveSelectorClosure.exists_countablyCompact_injOn_extension. That existing omega1 closing-off "
                        + "adds fresh ambient punctured accumulation points while preserving section-goodness, Q-injectivity and the continuum bound. "
                        + "Every countable collection appears in a bounded stage and is processed later. The extension contains the seed, "
                        + "so its section-density witnesses survive. The outcome is native countable compactness, with no sequential compactness assertion.")),
                    Paragraph(Text("Frolik's Lemma 2.8 has the essential no-accumulation-in-P premise for an infinite subset of beta P, with P separable metrizable; "
                        + "Lemma 2.9 provides cardinal avoidance and omega1 closing-off. Ginsburg-Saks Theorem 2.12 closes a completely regular X inside beta X "
                        + "under sequence limits for one fixed free ultrafilter D. The canonical notes preserve those exact scopes. "
                        + "They attest classical methods, not this exact arbitrary-q selector with a constructed section-dense seed and distinct projected values. "
                        + "The finite-block candidate in Feldman-Wilce supplies the application target, as recorded in its canonical note. "
                        + "The present statement is repository-derived; this exposition makes no novelty, diversity or original-question completion claim."))),
                DescribeRole.Theorem))));
}
