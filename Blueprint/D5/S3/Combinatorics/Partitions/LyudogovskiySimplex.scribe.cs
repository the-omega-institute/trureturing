using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class LyudogovskiySimplexDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Partitions/LyudogovskiySimplex.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/FiniteGeometry/lyudogovskiy2026simplex");

    public DocumentDefinition Create()
    {
        var r = V("r");
        var n = V("n");
        var p = V("p");
        var q = V("q");
        var t = Add(C("triangular", r), D(1));
        var tau = C("threshold", r);
        var first = And(Eq(C("layer", r, tau), C("firstFamily", r, tau)),
            And(Eq(C("layer", r, t), C("firstFamily", r, t)),
                Eq(C("card", C("firstFamily", r, tau)), Add(r, D(1)))));
        var threshold = And(All("r", V("Nat"), And(Eq(tau, t),
            C("IsLeast", C("positiveNonemptyLevels", r), t))),
            All("n", V("Nat"), Imp(Lt(D(0), n),
                Eq(C("maxDimension", n), C("max", C("triangularRanksBelow", n))))));
        var extension = And(C("subset", C("cells", C("staircase", r)), C("cells", C("ofPartition", p))),
            Eq(C("card", C("sdiff", C("cells", C("ofPartition", p)), C("cells", C("staircase", r)))), D(1)));
        return DocumentDefinition.Create(ScribeNode.Create(
            "Actual integer-partition unit transfers determine finite clique maxima and exact local layers.",
            H("Unit transfers and local simplex layers"), Blocks(
                Paragraph(Text("Nat denotes the nonnegative integers. Partition(n) is the multiset of positive parts with sum n. Every occurrence is retained. A unit transfer removes one unit from one part occurrence and adds it to a distinct occurrence or to a virtual zero row; zero remainders disappear. The resulting partition must differ from the original. YoungDiagram.ofPartition sorts the parts and draws each row as an initial interval of cells. All cliques, maxima and layer cardinalities below use the actual finite partition carrier.")),
                Node("cliques", "All finite cliques", All("n", V("Nat"),
                    All("s", C("Finset", C("Partition", n)), Iff(In(V("s"), C("cliques", n)),
                        C("IsClique", C("graph", n), V("s"))))),
                    "The collection includes singletons and the empty clique."),
                Node("localDimension", "The largest clique through a vertex", OnVertex(
                    Eq(C("localDimension", p), C("max", C("cliqueDimensionsContaining", n, p)))),
                    "cliqueDimensionsContaining(n,p) contains card(s)-1 for every clique s containing p. The singleton clique ensures this collection is nonempty."),
                Node("layer", "An exact level", All("r", V("Nat"), OnVertex(
                    Iff(In(p, C("layer", r, n)), Eq(C("localDimension", p), r))))),
                Node("maxDimension", "Maximum local dimension", All("n", V("Nat"),
                    Eq(C("maxDimension", n), C("max", C("localDimensions", n)))),
                    "localDimensions(n) is the finite collection of localDimension(p) over all integer partitions p of n. Every n has a partition, so this maximum is attained."),
                Node("threshold", "Least positive occurrence", All("r", V("Nat"),
                    Eq(tau, C("sInf", C("positiveNonemptyLevels", r)))),
                    "positiveNonemptyLevels(r) contains precisely the positive n with a nonempty exact layer(r,n). The natural-number infimum is zero when this set is empty; the full threshold claim explicitly requires existence and leastness."),
                Node("triangular", "Triangular sizes", All("r", V("Nat"),
                    Eq(C("triangular", r), C("natDiv", Mul(r, Add(r, D(1))), D(2))))),
                Node("staircase", "The staircase ideal", All("r", V("Nat"), All("i", V("Nat"),
                    All("j", V("Nat"), Iff(In(C("pair", V("i"), V("j")), C("staircase", r)),
                        Lt(Add(V("i"), V("j")), r))))),
                    "The ideal is empty at r=0 and has row lengths r,r-1,...,1 for positive r."),
                Node("firstFamily", "All addable one-cell extensions", All("r", V("Nat"),
                    OnVertex(Iff(In(p, C("firstFamily", r, n)), extension)))),
                Node("ThresholdClaim", "The full threshold question", Iff(C("ThresholdClaim"), threshold),
                    "triangularRanksBelow(n) is the finite set of r<=n for which triangular(r)+1<=n. The cutoff omits no feasible natural rank: r<=triangular(r), so triangular(r)+1<=n implies r<n. This proposition specifies the entire threshold and maximum problem; its definition supplies no proof of that proposition."),
                Node("FirstOccurrenceClaim", "The full first-family question", Iff(C("FirstOccurrenceClaim"),
                    All("r", V("Nat"), Imp(Le(D(2), r), first))),
                    "Both equalities concern full finite vertex sets. The cardinality requires r+1 distinct members. This proposition includes r=2 and has no upper bound on r; its definition supplies no proof."),
                Describe.Lean(DescribeId.Create("lyudogovskiy-threshold-result"),
                    DeclarationHandle.Create(Prefix + "threshold_result"), H("The complete threshold formula"),
                    StatementSource.FromAuthor(Disp(threshold)), AssessedProvenance.FromRepo(Source),
                    Blocks(Paragraph(Text("For every r, the positive size triangular(r)+1 has a nonempty exact layer and is its least positive occurrence. Separately, every positive n has the displayed maximum. The proof bounds every actual clique through the star/top alternatives, constructs r+1 genuine extensions of an enlarged staircase at every feasible size, and uses finite attainment. No assumption that the local-dimension spectrum is contiguous is used."))), DescribeRole.Theorem,
                    new OpenProblemResolutionClaim(
                        ProblemSlugRef.Create("lyudogovskiy-2026-simplex-threshold"), ResolutionKind.Proved)),
                Describe.Lean(DescribeId.Create("lyudogovskiy-first-occurrence-result"),
                    DeclarationHandle.Create(Prefix + "first_occurrence_result"), H("The entire first-occurrence family"),
                    StatementSource.FromAuthor(Disp(All("r", V("Nat"), Imp(Le(D(2), r), first)))),
                    AssessedProvenance.FromRepo(Source),
                    Blocks(Paragraph(Text("For every r at least two, a clique of dimension r at the first size cannot be a top: its containing diagram would require triangular(r+1) cells but has only triangular(r)+2. A star predecessor contains the size-triangular(r) staircase and therefore equals it. Conversely every addable staircase extension lies in the full r+1-member star; the sharp maximum forces exact local dimension r. Distinct addable cells give distinct partitions. The threshold identity connects this full set equality to the literal threshold argument."))), DescribeRole.Theorem,
                    new OpenProblemResolutionClaim(
                        ProblemSlugRef.Create("lyudogovskiy-2026-first-occurrence-family"), ResolutionKind.Proved)))));

    }

    private static Formula OnVertex(Formula b) => All("n", V("Nat"), All("p", C("Partition", V("n")), b));
    private static DocumentBlock Node(string name, string title, Formula formula, string prose = "") =>
        Describe.Lean(DescribeId.Create("lyudogovskiy-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(prose.Length == 0 ? title + "." : prose))), DescribeRole.Definition);
    private static Formula V(string s) => F.Id(s);
    private static Formula C(string s, params Formula[] a) => new Formula.Apply(Seq(Operatorname, Grp(V(s))), [.. a]);
    private static Formula All(string n, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), t, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula In(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
}
