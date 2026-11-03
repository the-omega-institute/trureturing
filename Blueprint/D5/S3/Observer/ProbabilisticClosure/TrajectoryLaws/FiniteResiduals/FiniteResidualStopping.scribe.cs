using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws.FiniteResiduals;

internal sealed class FiniteResidualStoppingDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteResiduals/FiniteResidualStopping.";

    public DocumentDefinition Create()
    {
        Formula s = F.Id("S"), y = F.Id("Y"), k = F.Id("K"), n = F.Id("n");
        Formula x = F.Id("x"), xp = F.Id("xp"), w = F.Id("w"), e = F.Id("E");
        Formula nat = F.Id("Nat"), words = Call("List", y);
        Formula trace = Call("TraceEq", k, n, x, xp);
        Formula residual = Call("residual", k, n, x, xp);
        Formula sound = Context(All("n", nat, All("x", s, All("xp", s,
            Seq(residual, Rightarrow, trace)))));
        Formula stopping = Context(All("n", nat, All("x", s, All("xp", s,
            Seq(trace, Leftrightarrow, Call("StoppingEq", k, n, x, xp))))));
        Formula mass = Call("archiveProb", k, e, x, w);
        Formula law = Context(All("n", nat, All("E", Call("Experiment", y, n), All("x", s,
            Seq(Open, All("w", words, Seq(D(0), Leq, mass)), Close, Land, Sp,
                Open, All("w", words, Seq(n, Lt, Call("length", w), Rightarrow, mass, Eq, D(0))), Close,
                Land, Sp, Sum("w", Call("leaves", e), mass), Eq, D(1))))));
        return DocumentDefinition.Create(ScribeNode.Create(
            "Joint residual signatures preserve actual finite words; stopped execution has exactly the same observational equivalence.",
            H("Finite residuals and actual stopping archives"), Blocks(
                Paragraph(Text("S and Y are arbitrary finite types. K is the existing FiniteMarkovKernel from S to Y times S: every joint row is nonnegative and sums to one. There is one interface, one everywhere legal action, and no failure terminal. K is time homogeneous. No positivity, full support, rationality, determinism or nonemptiness assumption is added. Empty finite types are included wherever such a normalized kernel exists.")),
                Paragraph(Text("Current observation is constant. Thus residual(K,0,x,xp) is True, exactly equality of the current readout. For a relation R, classMass(K,R,x,y,c) sums K(x,(y,r)) over r related to c. The successor residual retains the preceding relation and requires equality of these joint label/class masses for every label and every class representative. Repeated representatives merely repeat the same equation. Each residual is an equivalence relation. This is the decreasing recursive joint-class chain, independently defined from actual word laws.")),
                Paragraph(Text("wordProb(K,x,[]) is one. wordProb(K,x,y::w) sums K(x,(y,r))*wordProb(K,r,w) over all actual successors. TraceEq(K,n,x,xp) means equality of these probabilities for every word of length at most n. Experiment(Y,n) is a finite tree: stop is allowed at any remaining depth; step chooses its continuation solely from the next actual label. Every finite deterministic prefix-dependent stopping policy has this tree representation, and every such tree is allowed. There is no action choice beyond the unique action and no hidden-state test, class test, law-table access, reset, copying or postselection.")),
                Node("finite-residual-sound", "residual_sound", "Soundness at every horizon", sound,
                    "Induct on n. At zero only the empty word occurs. For y::w, the induction hypothesis makes r mapped to wordProb(K,r,w) constant on each preceding residual class. Partition the finite successor sum into those classes. Equality of the joint label/class masses makes their weighted sums equal. This grouping is a mathematical integration identity and does not reveal the successor class to the policy."),
                Paragraph(Text("archiveProb executes the tree chronologically. At stop it gives mass one to the empty suffix. At step its empty suffix has mass zero, and the mass of y::w sums the original joint kernel times the independently executed continuation chosen by y. accepts(E,w) says that w ends at a leaf of this tree, with no earlier stop. Induction on the tree proves archiveProb(K,E,x,w)=wordProb(K,x,w) when accepts(E,w), and zero otherwise. An accepted word has length at most the depth. This proves the word/archive correspondence rather than identifying the two laws by definition.")),
                Node("finite-trace-stopping", "trace_iff_stopping", "Exact operational stopping characterization", stopping,
                    "StoppingEq quantifies over every k at most n, every Experiment(Y,k), and every complete archive word. For the forward direction, use the independently proved accepted-prefix formula and its length bound. For the reverse direction, use the legal tree that continues exactly length(w) steps and then stops. These arguments include immediate stopping, the empty word, horizon zero and branches of zero probability. A suffix discarded by stopping is summed out; no observer operation on that suffix is introduced."),
                Node("finite-archive-probability-law", "archive_probability_law", "The executed archives are probability laws", law,
                    "leaves(E) is the finite set of complete archive words at which E stops. The first conjunct is pointwise nonnegativity, the second excludes words longer than n, and the last sums the archive probabilities over leaves(E). For step, the prefix sets y::leaves(E(y)) are pairwise disjoint. Their total mass is the sum over y and r of K(x,(y,r)) times the continuation mass one. Row normalization gives one. At stop, the sole leaf is the empty word."),
                Paragraph(Text("If a constant c is recorded only initially, the complete record is (c,w), with inverse given by the word projection. If it is recorded initially and at every node, the record is (c,map(y mapped to (y,c),w)), again with inverse given by projecting the labels. Both encodings are injective on actual archives, including the empty archive, and pushing any of the finite laws through them preserves and reflects equality. Prefix decisions pull back through these same encodings, so neither convention supplies additional control. This is a finite single-action result; it makes no unrestricted stochastic decoder or semantic-factorization assertion.")))));
    }

    private static DocumentBlock.Describe Node(string id, string name, string title, Formula statement, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
    private static Formula Context(Formula body) => All("S", F.Id("Type"), All("Y", F.Id("Type"),
        Seq(OpenBracket, Call("Fintype", F.Id("S")), CloseBracket, Sp,
            OpenBracket, Call("Fintype", F.Id("Y")), CloseBracket, Sp,
            All("K", Call("FiniteMarkovKernel", F.Id("S"), Call("Prod", F.Id("Y"), F.Id("S"))), body))));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, F.Id(name), Colon, type, Comma, Sp, Open, body, Close);
    private static Formula Sum(string name, Formula set, Formula body) =>
        Seq(F.Sum, Underscore, Grp(F.Id(name), InMacro, Sp, set), body);
    private static Formula Seq(params Formula[] xs) => F.Seq(xs);
    private static Formula Call(string name, params Formula[] xs) =>
        Seq(Operatorname, Grp(F.Id(name)), Open, Join(xs), Close);
    private static Formula Join(Formula[] xs)
    {
        if (xs.Length == 0) return F.Id("Unit");
        var parts = new Formula[xs.Length * 2 - 1];
        for (var i = 0; i < xs.Length; i++) { parts[2 * i] = xs[i]; if (i > 0) parts[2 * i - 1] = Comma; }
        return Seq(parts);
    }
}
