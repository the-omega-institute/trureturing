using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ProbabilisticClosure.TrajectoryLaws;

internal sealed class FiniteFairBitExitLawsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Observer/ProbabilisticClosure/TrajectoryLaws/FiniteFairBitExitLaws.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "FiniteFairBitExitLaws", H("Actual primitive exit laws and reachable escape"), Blocks(
            Paragraph(Text("An internal state belongs to a finite carrier S. A decoded instruction is deterministic or requests one fresh fair bit. Its successor either remains internal or carries one full exit label in a finite carrier O. The analytical terminal copies are absorbing and consume no further bits. They are proof coordinates; the internal matrix T is indexed only by S. All actual charged runtime state remains in S until the event cut.")),
            Paragraph(Text("A labelled primitive may supply its next physical state together with an optional event. Mapping its result to S plus O gives a cut at that event. The physical edge trace continues after selection. The cut equals the first actual edge observation in the physical prefix, even if a later primitive erases the value. An immediate outcome is an explicit entrance in O. A semantic selection cut and original invocation completion are different events.")),
            ExactNode("exits_exit"),
            ExactNode("path_exit"),
            ExactNode("step_mass"),
            ExactNode("exits_partition"),
            Node("cut", "primitive_event_cut", "First actual primitive observation", CutStatement()),
            Paragraph(Text("Execution reuses the sequential variable-request run and its iid tape measure. Deterministic steps retain the entire suffix; fair steps split the head and unused suffix using FreshServiceRestart. Equality of every finite state prefix with the original instruction trajectory extends to the whole path measure by uniqueness of finite projective limits. Thus the event laws below are laws on the existing Kernel.trajMeasure, rather than a separately assumed Markov process.")),
            Paragraph(Text("First exit at time n means an exit label occurs at n and every earlier analytical state is internal. These events are measurable and pairwise disjoint across both time and complete label. The internal endpoint mass is T to the n-th power. Survival is its row sum, and exit at n plus one has mass T to the n-th power times R. Time zero gives mass one exactly at an immediate exit label. Empty internal carriers and coincident fair successors obey the same formulas.")),
            Node("finite", "finite_exit_laws", "Finite first-exit and survival identities", FiniteStatement()),
            Paragraph(Text("Reachability starts at every internal permitted entrance in one common graph. An edge is traversable precisely when its actual decoded probability is positive. The nonexit event satisfies the first-step weighted equation. If its mass is zero at one state, every successor of positive weight also has zero nonexit mass. Induction transfers the literal permitted-entry almost-sure exit premise throughout the common reachable graph; a positively reachable trap therefore contradicts that premise.")),
            Node("transfer", "reachable_as_exit", "Almost-sure exit on the common reachable graph", TransferStatement()),
            Paragraph(Text("Survival events decrease to nonexit. Continuity from above makes their masses converge to zero at each reachable state. Finiteness gives one positive length L for which every reachable survival mass is at most one half. Unreachable columns of every power of T are zero for reachable rows. The finite semigroup identity then bounds survival at nL by two to the negative n-th power. Disconnected traps are retained outside this graph; no time cap or irreducibility hypothesis is used.")),
            Node("escape", "reachable_escape", "One common positive escape block", EscapeStatement()),
            Paragraph(Text("The union of complete first-exit labels is exactly the complement of nonexit. Its disjoint masses add to one at every permitted entrance and every reachable internal state. This normalization is a property of the actual execution events. It is not supplied as an arbitrary probability vector.")),
            Node("normalize", "normalized_reachable_exits", "Actual normalized exit law", NormalizeStatement()),
            Paragraph(Text("First-step decomposition of each eventual label event gives Z equals R plus TZ, without assuming transience, invertibility, or a renewal equation. For a service that exits almost surely on its reachable graph, this same Z is its normalized complete exit law. Complete returned snapshots may be labels for update services; actual first semantic observations may be labels for selection services.")),
            Node("renewal", "actual_renewal", "Actual event renewal equation", RenewalStatement()),
            Paragraph(Text("Applying these results to the original charged digital class still requires paid code fetching, complete field encoding, installation peak, lawful native entrances, primitive boundary semantics and the original event-tag refinement. A semantic cut does not by itself identify the original full-return output marginal. That identity requires the original exactly-one-letter protocol and almost-sure physical return. The two original same-update and positive-history compatibility clauses remain distinct. Integer determinant certificates and the four native-service common denominator are additional results.")))));

    private static DocumentBlock.Describe ExactNode(string name) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-')), DeclarationHandle.Create(Prefix + name), H(name),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("This existing source lemma is reused directly by the operational certificate."))),
            DescribeRole.Theorem);

    private static DocumentBlock.Describe Node(string id, string name, string title, Formula statement) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The statement concerns the displayed finite primitive execution and its actual fair-tape event masses."))),
            DescribeRole.Theorem);

    private static Formula CutStatement() => Family(App("Instruction", App("Prod",N("S"),App("Option",N("O")))),
        All("s",N("S")), All("omega",Arrow(Nat,N("Bool"))), All("n",Nat), All("o",N("O")),
        App("path",App("cut",N("d")),Inl("s"),N("omega"),N("n")), Sp, Eq, Sp, Inr("o"), Sp, Iff, Sp,
        Exists, Sp,N("k"), Sp,Lt, Sp,N("n"),Sp,Comma,Sp,
        App("edgeEvent",N("d"),N("s"),N("omega"),N("k")), Sp,Eq,Sp,App("some",N("o")), Sp,Land,Sp,
        Forall,Sp,N("j"),Sp,Lt,Sp,N("k"),Sp,Comma,Sp,
        App("edgeEvent",N("d"),N("s"),N("omega"),N("j")),Sp,Eq,Sp,N("none"));

    private static Formula FiniteStatement()
    {
        var hit = App("hit",N("d"),N("a"),N("n"),N("o"));
        var trajectory = App("trajectoryHit",N("n"),N("o"));
        var internalEvent = App("Set.setOf",Lambda("omega",Seq(
            App("path",N("d"),Inl("s"),N("omega"),N("n")),Sp,Eq,Sp,Inl("t"))));
        var timeLabel = App("Prod",Nat,N("O"));
        var hitI = App("hit",N("d"),N("a"),App("fst",N("i")),App("snd",N("i")));
        var hitJ = App("hit",N("d"),N("a"),App("fst",N("j")),App("snd",N("j")));
        return Family(Instruction(),All("a",SumType()),
            App("Measure.map",App("path",N("d"),N("a")),N("tapeLaw")),Sp,Eq,Sp,
            App("instructionLaw",App("stopped",N("d")),N("a")),Sp,Land,Sp,
            Open,All("n",Nat),All("o",N("O")),App("MeasurableSet",trajectory),Sp,Land,Sp,
            Call(App("instructionLaw",App("stopped",N("d")),N("a")),trajectory),Sp,Eq,Sp,Mass(hit),Close,Sp,Land,Sp,
            Open,All("n",Nat),All("o",N("O")),App("MeasurableSet",hit),Close,Sp,Land,Sp,
            Open,All("i",timeLabel),All("j",timeLabel),NotEqual(N("i"),N("j")),Sp,To,Sp,App("Disjoint",hitI,hitJ),Close,Sp,Land,Sp,
            Open,All("s",N("S")),All("t",N("S")),All("n",Nat),Mass(internalEvent),Sp,Eq,Sp,
            Call(Pow(App("T",N("d")),N("n")),N("s"),N("t")),Close,Sp,Land,Sp,
            Open,All("s",N("S")),All("n",Nat),Surv(N("n")),Sp,Eq,Sp,
            SumOver("t",N("S"),Call(Pow(App("T",N("d")),N("n")),N("s"),N("t"))),Close,Sp,Land,Sp,
            Open,All("s",N("S")),All("o",N("O")),All("n",Nat),
            Mass(App("hit",N("d"),Inl("s"),Seq(N("n"),Plus,D(1)),N("o"))),Sp,Eq,Sp,
            Call(Seq(Open,Pow(App("T",N("d")),N("n")),Sp,Times,Sp,App("R",N("d")),Close),N("s"),N("o")),Close,Sp,Land,Sp,
            Open,All("o",N("O")),Mass(App("hit",N("d"),N("a"),D(0),N("o"))),Sp,Eq,Sp,
            N("if"),Sp,N("a"),Sp,Eq,Sp,Inr("o"),Sp,N("then"),Sp,D(1),Sp,N("else"),Sp,D(0),Close);
    }

    private static Formula TransferStatement() => Family(Instruction(),All("E",App("Set",SumType())),
        EntryPremise(),Sp,To,Sp,All("s",N("S")),Reach("s"),Sp,To,Sp,
        Mass(App("never",N("d"),Inl("s"))),Sp,Eq,Sp,D(0));

    private static Formula EscapeStatement() => Family(Instruction(),All("E",App("Set",SumType())),
        EntryPremise(),Sp,To,Sp,Exists,Sp,N("L"),Sp,Colon,Sp,Nat,Sp,Comma,Sp,
        D(0),Sp,Lt,Sp,N("L"),Sp,Land,Sp,
        Open,All("s",N("S")),Reach("s"),Sp,To,Sp,Surv(N("L")),Sp,Le,Sp,new Formula.Fraction(D(1),D(2)),Close,Sp,Land,Sp,
        Open,All("s",N("S")),Reach("s"),Sp,To,Sp,All("n",Nat),Surv(Seq(N("n"),Times,N("L"))),Sp,Le,Sp,
        Pow(new Formula.Fraction(D(1),D(2)),N("n")),Close,Sp,Land,Sp,
        Open,All("s",N("S")),Reach("s"),Sp,To,Sp,
        App("Tendsto",App("survival",N("d"),N("s")),N("atTop"),App("nhds",D(0))),Close,Sp,Land,Sp,
        Open,All("s",N("S")),All("t",N("S")),Reach("s"),Sp,To,Sp,App("Not",Reach("t")),Sp,To,Sp,
        All("n",Nat),Call(Pow(App("T",N("d")),N("n")),N("s"),N("t")),Sp,Eq,Sp,D(0),Close);

    private static Formula NormalizeStatement() => Family(Instruction(),All("E",App("Set",SumType())),
        EntryPremise(),Sp,To,Sp,
        Open,Forall,Sp,N("a"),Sp,InMacro,Sp,N("E"),Sp,Comma,Sp,
        SumOver("o",N("O"),Mass(App("exits",N("d"),N("a"),N("o")))),Sp,Eq,Sp,D(1),Close,Sp,Land,Sp,
        Open,All("s",N("S")),Reach("s"),Sp,To,Sp,
        SumOver("o",N("O"),App("Z",N("d"),N("s"),N("o"))),Sp,Eq,Sp,D(1),Close);

    private static Formula RenewalStatement() => Family(Instruction(),App("Z",N("d")),Sp,Eq,Sp,
        App("R",N("d")),Sp,Plus,Sp,App("T",N("d")),Sp,Times,Sp,App("Z",N("d")));

    private static Formula EntryPremise() => Seq(Open,Forall,Sp,N("a"),Sp,InMacro,Sp,N("E"),Sp,Comma,Sp,
        Mass(App("never",N("d"),N("a"))),Sp,Eq,Sp,D(0),Close);
    private static Formula Family(Formula instruction, params Formula[] body) => Seq(
        All("S",N("Type")),All("O",N("Type")),
        Bracket(App("Fintype",N("S"))),Bracket(App("Fintype",N("O"))),
        Bracket(App("MeasurableSpace",N("S"))),Bracket(App("MeasurableSingletonClass",N("S"))),
        Bracket(App("MeasurableSpace",N("O"))),Bracket(App("MeasurableSingletonClass",N("O"))),
        All("d",Arrow(N("S"),instruction)),Seq(body));
    private static Formula Instruction() => App("Instruction",SumType());
    private static Formula SumType() => App("Sum",N("S"),N("O"));
    private static Formula Inl(string x) => App("Sum.inl",N(x));
    private static Formula Inr(string x) => App("Sum.inr",N(x));
    private static Formula Reach(string x) => App("Reachable",N("d"),N("E"),N(x));
    private static Formula Surv(Formula n) => App("survival",N("d"),N("s"),n);
    private static Formula Mass(Formula e) => Call(N("tapeLaw"),e);
    private static Formula Bracket(Formula f) => Seq(OpenBracket,f,CloseBracket,Sp);
    private static Formula Arrow(Formula a, Formula b) => Seq(a,Sp,To,Sp,b);
    private static Formula All(string name, Formula type) => Seq(Forall,Sp,Open,N(name),Sp,Colon,Sp,type,Close,Sp,Comma,Sp);
    private static Formula Lambda(string name, Formula body) => Seq(N("fun"),Sp,N(name),Sp,Mapsto,Sp,body);
    private static Formula SumOver(string name, Formula type, Formula body) => Seq(Sum,Underscore,Grp(Seq(N(name),Colon,type)),Sp,body);
    private static Formula Nat => Seq(Mathbb,Grp(F.Id("N")));
    private static Formula Pow(Formula b, Formula e) => Seq(b,Caret,Grp(e));
    private static Formula App(string name, params Formula[] args) => Call(N(name),args);
    private static Formula Call(Formula head, params Formula[] args)
    {
        var terms = new System.Collections.Generic.List<Formula> { head,Sp,Open };
        for (var i=0; i<args.Length; i++)
        {
            if (i>0) terms.Add(Seq(Sp,Comma,Sp));
            terms.Add(args[i]);
        }
        terms.Add(Close);
        return F.Seq(terms.ToArray());
    }
    private static Formula N(string name)
    {
        var terms = new System.Collections.Generic.List<Formula>();
        var parts=name.Split('.');
        for (var i=0; i<parts.Length; i++)
        {
            if (i>0) terms.Add(Dot);
            terms.Add(Seq(Operatorname,Grp(F.Id(parts[i]))));
        }
        return F.Seq(terms.ToArray());
    }
    private static Formula Seq(params Formula[] items) => F.Seq(items);
}
