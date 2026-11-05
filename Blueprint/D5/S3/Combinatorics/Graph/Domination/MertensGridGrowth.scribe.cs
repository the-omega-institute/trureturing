using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Domination;

internal sealed class MertensGridGrowthDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Domination/MertensGridGrowth.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Ordinary grid and cylinder domination growth", H("Ordinary grid and cylinder domination growth"), Blocks(
            Node("counts", "Actual labelled subsets", "count", "The count is the cardinality of the existing ordinary dominating-set family domSets. Every distinct subset is counted once, including nonminimal subsets; no symmetry quotient is taken. The grid and cylinder use Mathlib pathGraph, cycleGraph and Cartesian graph product on Fin m times Fin n. Thus the source domination polynomial at z=1 is exactly this count.", DescribeRole.Definition),
            Node("target", "Complete joint target", "JointGrowth", "The target has one existential real mu in [1,2]. For every positive epsilon one natural N at least three works for both actual counts and every pair m,n at least N. No aspect ratio is bounded. The function growth a m n is the real power a raised to one divided by the natural product m*n.", DescribeRole.Definition),
            Node("seam", "Finite seam repair", "finite_seam_bound", "For m at least three and every natural n, g(m,n) is at most c(m,n), which is at most g(m,n) times 4 to the power n. The lower inequality uses pathGraph_le_cycleGraph. The upper inequality fills both endpoint columns. The pair of the repaired grid subset and the original boundary intersection determines the cylinder subset, giving an injection into the grid family times the boundary powerset. The boundary has exactly 2n vertices. The proof includes m=3 and n=1, and additionally allows n=0 in this finite lemma.", DescribeRole.Theorem),
            Node("tiling", "Block choices and selected padding", "tiling_count", "For arbitrary natural a,b,M,N, disjoint translated a-by-b blocks inject independent dominating-subset choices into the M-by-N grid. All leftover vertices are selected. Restriction to each embedded block recovers its original choice. The generic block_count proof permits additional cross-block edges and requires no independence of the resulting graph. The number of blocks is the product of the natural quotients M/a and N/b (quotient denotes Nat.div in the displayed formula); zero-sized blocks cause no unproved cutoff.", DescribeRole.Theorem),
            Node("joint", "Equal unrestricted joint limits", "result", "Let L be the supremum of log g(a,b)/(ab), with zero-area rates defined by division by zero as zero, and let mu=exp L. The all-vertex subset and powerset bound give 0<=L<=log 2. For each fixed positive block, the tiling inequality gives its normalized log rate times the two covered proportions as a lower bound on every large grid rate. Each covered proportion tends to one because the uncovered remainder divided by the side length tends to zero. A supremum argument therefore gives the joint grid limit L. The finite seam inequality puts the cylinder log rate between the grid log rate and that rate plus log 4 divided by m, uniformly in n. Joint squeezing gives the same L. Continuity of exp yields the required real-power limits with one common N for all sufficiently large m,n.", DescribeRole.Theorem,
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("mertens-2024-grid-cylinder-joint-growth"), ResolutionKind.Proved)),
            Paragraph(Text("Source: Stephan Mertens, Journal of Integer Sequences 27 (2024), Article 24.7.6, definitions on pp. 1–2, joint growth discussion (15)–(17), and the conjecture after (22) on p. 19. The journal and arXiv v1 have different pagination. The argument proves grid-limit existence and does not assume it. It establishes neither a numerical value of mu nor a convergence rate for the grid itself. This is a formal settlement claim subject to independent source, proof-shape, registration and admission review; bounded literature checks do not establish worldwide priority."))), []));

    private static DocumentBlock Node(string id, string title, string name, string prose, DescribeRole role,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            Presentation(name), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role, resolution);

    private static StatementSource Presentation(string name)
    {
        Formula m=V("m"), n=V("n"), a=V("a"), b=V("b"), bigM=V("M"), bigN=V("N");
        Formula G(Formula x, Formula y) => Call("count", Call("grid", x,y));
        Formula C(Formula x, Formula y) => Call("count", Call("cylinder", x,y));
        Formula? f = name switch
        {
            "finite_seam_bound" => All("m", Nat, All("n", Nat, Imp(Le(D(3),m),
                And(Le(G(m,n),C(m,n)), Le(C(m,n),Mul(G(m,n),new Formula.Power(D(4),n))))))),
            "tiling_count" => All("a",Nat,All("b",Nat,All("M",Nat,All("N",Nat,
                Le(new Formula.Power(G(a,b),Mul(Call("quotient",bigM,a),Call("quotient",bigN,b))),G(bigM,bigN)))))),
            "result" => Joint(),
            _ => null
        };
        return f is null ? StatementSource.WithoutFormula() : StatementSource.FromAuthor(Disp(f));
    }
    private static Formula Joint()
    {
        Formula mu=V("mu"), eps=V("epsilon"), n0=V("N"), m=V("m"), n=V("n");
        Formula E(string graph) => Lt(new Formula.Absolute(new Formula.Binary(
            Call("growth",Call("count",Call(graph,m,n)),m,n),FormulaBinaryOperator.Subtract,mu)),eps);
        return Some("mu",Real,And(And(Le(D(1),mu),Le(mu,D(2))),All("epsilon",Real,
            Imp(Lt(D(0),eps),Some("N",Nat,And(Le(D(3),n0),All("m",Nat,All("n",Nat,
                Imp(Le(n0,m),Imp(Le(n0,n),And(E("grid"),E("cylinder"))))))))))));
    }
    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) => new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Par(Formula a) => Seq(Open,a,Close);
    private static Formula All(string name,Formula type,Formula body) => Seq(Forall,Sp,Par(Seq(V(name),Colon,type)),Comma,Sp,body);
    private static Formula Some(string name,Formula type,Formula body) => Seq(Exists,Sp,Par(Seq(V(name),Colon,type)),Comma,Sp,body);
    private static Formula Le(Formula a,Formula b) => new Formula.Relation(a,FormulaRelationOperator.LessThanOrEqual,b);
    private static Formula Lt(Formula a,Formula b) => new Formula.Relation(a,FormulaRelationOperator.LessThan,b);
    private static Formula And(Formula a,Formula b) => new Formula.Logic(Par(a),FormulaLogicOperator.And,Par(b));
    private static Formula Imp(Formula a,Formula b) => new Formula.Logic(Par(a),FormulaLogicOperator.Implies,Par(b));
    private static Formula Mul(Formula a,Formula b) => new Formula.Binary(a,FormulaBinaryOperator.Multiply,b);
    private static Formula Nat => Seq(Mathbb,Grp(V("N")));
    private static Formula Real => Seq(Mathbb,Grp(V("R")));
}
