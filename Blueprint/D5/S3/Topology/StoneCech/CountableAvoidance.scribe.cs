using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.StoneCech;

internal sealed class CountableAvoidanceDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Topology/StoneCech/CountableAvoidance.";
    private static Formula V(string s) => F.Id(s);
    private static Formula All(string s, Formula t) => Seq(Forall, Sp, V(s), Colon, Sp, t, Comma, Sp);
    private static Formula Ex(string s, Formula t) => Seq(Exists, Sp, V(s), Colon, Sp, t, Comma, Sp);
    private static Formula Fn(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula And(Formula a, Formula b) => Seq(a, Sp, Land, Sp, b);
    private static Formula Imp(Formula a, Formula b) => Seq(Grp(a), Sp, Rightarrow, Sp, Grp(b));
    private static Formula At(string s, Formula n) => Call(s, n);
    private static Formula Beta => Call("Ultrafilter", V("Nat"));
    private static Formula Free(Formula p) => Seq(Call("toFilter", p), Sp, Le, Sp, V("cofinite"));
    private static Formula Avoidance()
    {
        var assumption = Seq(All("n", V("Nat")), Free(At("p", V("n"))));
        var missed = Seq(All("n", V("Nat")), Neg, Sp, Call("mem", V("A"), At("p", V("n"))));
        var conclusion = Seq(Ex("A", Call("Set", V("Nat"))), And(Call("Infinite", V("A")), missed));
        return Disp(Seq(All("p", Fn(V("Nat"), Beta)), Imp(assumption, conclusion)));
    }
    private static Formula Reindex()
    {
        var free = Seq(OpenBrace, V("p"), Sp, Colon, Sp, Beta, Sp, Mid, Sp, Free(V("p")), CloseBrace);
        var conclusion = Seq(Ex("j", Fn(V("Nat"), V("Nat"))),
            And(Call("StrictMono", V("j")), Call("Injective", Call("compose", V("h"), Call("map", V("j"))))));
        return Disp(Seq(All("Y", V("Type")), All("h", Fn(Beta, V("Y"))),
            Imp(Call("Injective", Call("compose", V("h"), V("pure"))),
                Imp(Call("InjOn", V("h"), free), conclusion))));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Countable forbidden free ultrafilters can be avoided by one infinite subsequence.",
        H("Countable avoidance and full Stone–Čech injection"),
        Blocks(
            Describe.Lean(DescribeId.Create("infinite-ultrafilter-avoidance"),
                DeclarationHandle.Create(Owner + "exists_infinite_notMem"),
                H("An infinite set missed by every forbidden free ultrafilter"),
                StatementSource.FromAuthor(Avoidance()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every countable family p(n) of ultrafilters on Nat extending the cofinite filter, there is an infinite set A belonging to none of them. "
                    + "Start with Nat. Split each infinite pool into two disjoint infinite sets and choose a half absent from the next p(n). "
                    + "A diagonal infinite set is contained in each fixed later pool up to finitely many points. A free ultrafilter ignores those finite errors. "
                    + "The construction directly reuses PointPairSeparation.split_pool and diagonal_pool and requires no continuum or almost-disjoint-family hypothesis."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("ultrafilter-map-continuous"),
                DeclarationHandle.Create(Owner + "continuous_map"), H("Continuous reindexing"),
                StatementSource.FromAuthor(Disp(Seq(All("A", V("Type")), All("B", V("Type")),
                    All("j", Fn(V("A"), V("B"))), Call("Continuous", Call("map", V("j")))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The inverse image of the membership clopen for S is the membership clopen for the literal inverse image j inverse S."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("full-injection-after-thinning"),
                DeclarationHandle.Create(Owner + "exists_strictMono_injective_reindex"),
                H("Removing all principal/free collisions"), StatementSource.FromAuthor(Reindex()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Y is arbitrary and h need not be continuous. Assume h is injective on principal ultrafilters and separately injective on all free ultrafilters. "
                    + "For each principal value there is at most one colliding free point. Choose that point when it exists and a fixed free ultrafilter otherwise. "
                    + "Avoid this countable family by an infinite set A. On the clopen of ultrafilters containing A, principal/principal and free/free pairs retain injection, "
                    + "and both orientations of a principal/free pair are impossible. An increasing enumeration j of A therefore makes h composed with map j injective on the entire ultrafilter space."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "ultrafilterHomeomorph identifies Ultrafilter A with StoneCech A for every discrete space A. "
                + "Its forward map extends stoneCechUnit and its inverse extends pure; the two identities follow from agreement on the respective dense principal sets. "
                + "This identifies the reindexed full domain with the ordinary Stone–Čech compactification. These facts do not by themselves construct a signed measure sequence or a CH compactum.")))));
}
