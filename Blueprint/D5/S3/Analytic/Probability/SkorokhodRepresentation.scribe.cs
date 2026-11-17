using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Probability;

internal sealed class SkorokhodRepresentationDocument : IScribeDocumentDefinition
{
    private static Formula V(string n) => F.Id(n);
    private static Formula Real => Seq(Mathbb, Grp(V("R")));
    private static Formula Nat => Seq(Mathbb, Grp(V("N")));
    private static Formula Fn(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula All(string n, Formula t) =>
        Seq(Forall, Sp, V(n), Colon, Sp, t, Comma, Sp);
    private static Formula At(string f, params Formula[] xs) => Call(f, xs);
    private static Formula Law(Formula x) => At("measure", x);
    private static Formula Map(Formula f) => At("map", f, V("lambda"));
    private static Formula Tends(Formula f, Formula x) =>
        At("Tendsto", f, At("atTop"), At("nhds", x));

    private static Formula Statement() => Disp(new Formula.Aligned([
        Seq(Forall, Sp, V("u"), Comma, Sp, All("X", At("Type", V("u"))),
            At("PolishBorel", V("X")), Sp, Rightarrow),
        Seq(All("mu", Fn(Nat, At("ProbabilityMeasure", V("X")))),
            All("mu0", At("ProbabilityMeasure", V("X"))),
            Tends(V("mu"), V("mu0")), Sp, Rightarrow),
        Seq(Exists, Sp, V("Y"), Colon, Sp, Fn(Nat, Fn(Real, V("X"))), Comma, Sp,
            Exists, Sp, V("Y0"), Colon, Sp, Fn(Real, V("X")), Comma),
        Seq(Open, All("n", Nat), At("Measurable", At("Y", V("n"))), Close,
            Sp, Land, Sp, At("Measurable", V("Y0")), Sp, Land),
        Seq(Open, All("n", Nat), Map(At("Y", V("n"))), Sp, Eq, Sp,
            Law(At("mu", V("n"))), Close, Sp, Land),
        Seq(Map(V("Y0")), Sp, Eq, Sp, Law(V("mu0")), Sp, Land),
        Seq(At("AE", V("lambda")), Sp, V("t"), Colon, Sp, Real, Comma, Sp,
            Tends(Seq(V("n"), Sp, Mapsto, Sp, At("Y", V("n"), V("t"))),
                At("Y0", V("t"))))
    ]));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Weak convergence of Polish Borel probability laws admits a full-sequence almost-sure realization on one fixed unit interval.",
        H("Skorokhod representation on a fixed unit interval"),
        Blocks(
            Paragraph(Text("PolishBorel(X) denotes a topological space equipped with PolishSpace X, MeasurableSpace X and BorelSpace X. The carrier X may belong to any universe. ProbabilityMeasure X has its native topology of weak convergence. The notation measure(rho) denotes the underlying measure of a probability law. Throughout, lambda is the same measure volume.restrict(Set.Icc(0,1)) on the real line, and map(f,lambda) denotes its pushforward by f. AE(lambda) means lambda-almost everywhere.")),
            Describe.Lean(DescribeId.Create("skorokhod-representation-full-native"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/SkorokhodRepresentation.skorokhod_representation"),
                H("Exact laws and almost-sure convergence of the full sequence"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromLiterature(
                    LibraryNoteRef.Create("D5/L/Geometry/atlas2026strassencoupling")),
                Blocks(
                    Paragraph(Text("The limit law supplies nonemptiness of X. A countable family of arbitrarily small balls with limit-law-null frontiers gives each point a Boolean address. Coordinates are continuous away from the union of those frontiers, and convergence of addresses forces convergence in X. Composing with the inverse of the canonical Cantor-set homeomorphism and subtype inclusion gives a measurable real embedding that is continuous almost everywhere for the limit law and reflects sequence convergence.")),
                    Paragraph(Text("For each pushed-forward real law, use the adopted generalized inverse quantile. Portmanteau convergence on continuity sets gives convergence of the distribution functions at all limit-law-null singletons. At every interior continuity point of the limiting raw quantile, the quantile sequence converges. The limiting quantile has only countably many interior discontinuities. The endpoint and countable exceptional sets have Lebesgue measure zero.")),
                    Paragraph(Text("The raw quantiles are almost everywhere measurable on the open unit interval. Equality of the open-interval and closed-interval restricted Lebesgue measures transfers this property to lambda. Globally measurable representatives preserve the exact pushforward laws by almost-everywhere equality. Intersect the representative-equality events for every natural index and the limit, all corresponding embedding-range events, and quantile convergence into one conull event. A measurable extension of the embedding inverse produces the copies; convergence reflection gives their full-sequence almost-sure convergence.")),
                    Paragraph(Text("The copies have the specified individual laws. The statement asserts no preservation of original cross-index dependence, filtration, adaptedness, independence or conditional laws, and gives no convergence of original variables, algorithm or rate. It assumes no compact or finite support, moments, densities, atomlessness, subsequence, supplied joint law or supplied realization.")),
                    Paragraph(Text("The proof source is facebookresearch/atlas-lean, revision a60759060b5616df0d5775b42da4d337719feb32, MathlibExt/Probability/SkorokhodRepresentation.lean. It retains the Meta Platforms copyright and the complete supplier license, including its intended-use preface, at docs/reports/lovasz-suppliers/atlas-LICENSE.txt. This is an adaptation of a known classical theorem and an existing external formalization; no mathematical originality or first-formalization claim is made."))),
                DescribeRole.Theorem))));
}
