using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.StoneCech;

internal sealed class SectionGoodFreshClustersDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Topology/StoneCech/SectionGoodFreshClusters.";
    private static Formula V(string n) => FormulaDsl.Id(n);
    private static Formula All(string n, Formula t) => Seq(Forall, Sp, V(n), Colon, Sp, t, Comma, Sp);
    private static Formula Ex(string n, Formula t) => Seq(Exists, Sp, V(n), Colon, Sp, t, Comma, Sp);
    private static Formula Fn(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula Uf(string n) => Call("Ultrafilter", V(n));
    private static Formula Mem(Formula a, Formula b) => Seq(a, Sp, InMacro, Sp, b);
    private static Formula And(params Formula[] terms) => Seq(terms.SelectMany((f, i) =>
        i == 0 ? new[] { Grp(f) } : new[] { Sp, Land, Sp, Grp(f) }).ToArray());
    private static Formula Imp(Formula a, Formula b) => Seq(Grp(a), Sp, Rightarrow, Sp, Grp(b));
    private static Formula Q => Call("map", V("q"));
    private static Formula Good => Call("SectionGood", V("q"));
    private static Formula Statement => Disp(Seq(
        All("A", V("Type")), All("B", V("Type")), All("q", Fn(V("A"), V("B"))),
        All("e", Call("Embedding", V("Nat"), Uf("A"))), All("F", Call("Set", Uf("B"))),
        Imp(And(
                Seq(Call("range", V("e")), Sp, Subseteq, Sp, Good),
                Call("Injective", Call("compose", Q, V("e"))),
                Seq(Call("Card", V("F")), Sp, Le, Sp, V("c"))),
            Seq(Ex("u", Uf("A")), And(
                Mem(V("u"), Good),
                Call("AccPt", V("u"), Call("principal", Call("range", V("e")))),
                Seq(Neg, Grp(Mem(Call("apply", Q, V("u")), V("F")))))))));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual sections and disjoint supports encode index ultrafilters in distinct projected accumulation values.",
        H("Fresh projected accumulation on actual sections"), Blocks(
            Paragraph(Text("A and B are arbitrary types in Type, with their canonical ultrafilter Stone topologies; q : A -> B is arbitrary. "
                + "SectionGood(q) is exactly {u : Ultrafilter A | (u : Filter A) <= cofinite and there exists S in u with InjOn q S}. "
                + "Thus u is free and contains an actual set on which q is injective, a partial section of q. "
                + "In the formula, map(q) denotes Ultrafilter.map q, apply denotes function evaluation, Card is Cardinal.mk, c is the continuum, "
                + "Embedding(Nat,Ultrafilter A) is Nat embedded injectively in Ultrafilter A, and principal(range(e)) is the principal filter of that range. "
                + "AccPt is Mathlib's punctured accumulation predicate: each neighborhood meets the range away from the proposed accumulation point.")),
            Describe.Lean(DescribeId.Create("section-good-fresh-projected-accumulation"),
                DeclarationHandle.Create(Owner + "exists_sectionGood_fresh_accPt"),
                H("A section-good accumulation point outside prescribed projected values"),
                StatementSource.FromAuthor(Statement),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Topology/frolik1960countablycompact"),
                    LibraryNoteRef.Create("D5/L/Topology/feldmanwilce2026compactnesscliques")), Blocks(
                    Paragraph(Text("The hypotheses are an embedding e with section-good range, injectivity of n |-> Ultrafilter.map q (e n), "
                        + "and an arbitrary forbidden set F of ultrafilters on B with cardinal at most c. The conclusion is one u in SectionGood(q), "
                        + "an AccPt of the original range(e), whose projected value is outside F. Neither A nor B is assumed countable; "
                        + "no fibre of q is assumed finite and no selector or section-dense seed is assumed.")),
                    Paragraph(Text("The support construction takes P to be the actual image subspace range(n |-> map q (e n)). "
                        + "Its injective parametrization makes P infinite. The topological disjoint-open-set lemma is applied to P, producing pairwise disjoint "
                        + "relative open sets and chosen points p(n) in them. Lift these opens to ambient opens O(n) of Ultrafilter B, then choose basic "
                        + "membership clopens C(n)-hat inside O(n), with C(n) in p(n). Relative disjointness implies C(m) is absent from p(n) for m unequal to n; "
                        + "it does not by itself make the ambient C(n) disjoint. Define D(n) = C(n) minus the union of C(m) for m < n. "
                        + "Only finitely many complements are intersected, so D(n) still belongs to p(n), and these literal subsets of B are pairwise disjoint. "
                        + "An injective index map k realizes p(n) as map q (e(k(n))).")),
                    Paragraph(Text("Write v(n)=e(k(n)) and choose its given section witness T(n) in v(n). Splice them by "
                        + "S = union over n of T(n) intersect q-inverse(D(n)). Each piece belongs to v(n), so S belongs to every v(n). "
                        + "If two points of S have the same q-value, disjoint supports force their pieces to have the same index; "
                        + "injectivity on that T(n) then makes the points equal. This constructs the actual common injectivity set S.")),
                    Paragraph(Text("For every index ultrafilter r on Nat, including principal r, define L(r)=joinM(map v r). "
                        + "The membership law of this actual ultrafilter monad is H in L(r) iff {n | H in v(n)} in r. "
                        + "Every v(n) is free and contains S, so L(r) is free and contains the same injectivity set. "
                        + "For every index subset J, disjointness gives union(i in J) D(i) in map q (v(n)) iff n in J. Consequently "
                        + "union(i in J) D(i) in map q (L(r)) iff J in r. This readout for all J recovers r from the projected limit, "
                        + "so r |-> map q (L(r)) is injective. Distinct ultrafilters on A alone would not justify this projected injectivity.")),
                    Paragraph(Text("Restrict now to free index ultrafilters. The join is their topological ultrafilter limit of v. "
                        + "Since v is injective, the pushforward of a free index ultrafilter contains cofinite sets of Ultrafilter A; "
                        + "in particular its neighborhood witnesses can omit L(r). This gives the punctured AccPt of range(v), "
                        + "and monotonicity transfers it to range(e). FreeUltrafilterCardinality.continuum_power_le_mk_freeUltrafilter_nat "
                        + "supplies at least 2^c free index ultrafilters. If every projected limit lay in F, the readout would inject this supply into F, "
                        + "giving 2^c <= c, contrary to Cantor. Thus one free r gives the required fresh projected accumulation value.")),
                    Paragraph(Text("The cited Frolik note attributes classical abundance and cardinal avoidance precisely: Lemma 2.8 assumes a separable "
                        + "metrizable P and an infinite subset of beta P with no accumulation point in P; Lemma 2.9 constructs a small countably compact extension "
                        + "avoiding a remainder set of cardinal below 2^c. Its Pospisil and Katetov credits do not attribute this arbitrary-q section-splicing "
                        + "and projected readout theorem to those authors. The exact statement and proof composition here are repository-derived. "
                        + "The Feldman-Wilce note identifies the finite-block motivation; this source exposition makes no original-question resolution, "
                        + "literature exclusion or priority claim."))), DescribeRole.Theorem))));
}
