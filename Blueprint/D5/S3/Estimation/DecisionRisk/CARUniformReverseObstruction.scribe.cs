using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.DecisionRisk;

internal sealed class CARUniformReverseObstructionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every state count at least four, two CAR experiments with identical pair readouts "
            + "have exact asymmetric deficiencies and a common whole-seed public realization.",
        H("Uniform CAR reverse obstruction"),
        Blocks(Describe.Lean(
            DescribeId.Create("car-uniform-reverse-obstruction"),
            DeclarationHandle.Create("D5/S3/Estimation/DecisionRisk/CARUniformReverseObstruction.result"),
            H("Exact deficiencies, attained risks, and a common public seed"),
            StatementSource.FromAuthor(Display(TheoremFormula())),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("The quantifier ranges over every natural n at least four. The state "
                    + "space is Fin n and the observation alphabet consists of every nonempty subset of "
                    + "that space. Letters of zero profile weight and letters not containing the current "
                    + "state remain present. All denominators below are real; n and n minus one are positive.")),
                new DocumentBlock.DisplayFormula(Display(Profiles())),
                Paragraph(Text("The four cardinality classes used by the profiles are distinct. For "
                    + "each state there are n minus one containing pairs and n minus one containing "
                    + "complements of singletons. For two different states there is one containing pair "
                    + "and n minus two containing complements of singletons. These counts give "
                    + "nonnegative unit rows and the common off-diagonal pair value b. On the diagonal "
                    + "both pair readouts equal one. Every signed pair difference and the star budget vanish.")),
                new DocumentBlock.DisplayFormula(Display(PairFormula())),
                Paragraph(Text("A simulation kernel is one nonnegative matrix with unit row sums, "
                    + "used for every state. The deficiency infimum ranges over all such matrices on "
                    + "the full alphabet. It imposes no support restriction. The notation d(X,Y) means "
                    + "simulation from X to Y; the Lean function finiteDeficiency takes Y first and X second. "
                    + "Total variation is half the sum of absolute differences.")),
                new DocumentBlock.DisplayFormula(Display(DeficiencyDefinition())),
                Paragraph(Text("The forward kernel sends a singleton uniformly to its containing "
                    + "pairs and sends the full block uniformly to all complements of singletons. The "
                    + "reverse kernel sends a pair to the full block with probability x and to each of "
                    + "its two singletons with probability (1 minus x)/2; it sends every complement of "
                    + "a singleton to the full block. Every other input row is the identity row. Thus "
                    + "both kernels are defined on every letter, including unused letters.")),
                new DocumentBlock.DisplayFormula(Display(KernelFormula())),
                Paragraph(Text("In the forward output each containing pair has mass (1 minus b)/(n "
                    + "minus one), and every complement of a singleton has mass c. Compared with V, the "
                    + "total deficit on containing pairs is c and the unique noncontaining complement "
                    + "has excess c. The reverse output has full-block mass b, singleton mass rho at "
                    + "the true state, and rho/(n minus one) at each other state. Its total deficit and "
                    + "excess are both rho. These computations give the exact error at every state.")),
                new DocumentBlock.DisplayFormula(Display(ErrorFormula())),
                Paragraph(Text("The prior is uniform. In the identification-or-rejection task an "
                    + "incorrect identification costs one, a correct identification costs zero, and "
                    + "rejection costs one half. In the list task an action is a subset of cardinality "
                    + "exactly two and the loss is one precisely when the state is outside that subset. "
                    + "Both losses lie between zero and one.")),
                new DocumentBlock.DisplayFormula(Display(LossFormula())),
                Paragraph(Text("For a block of size k, identifying a member has total loss k minus "
                    + "one, rejection has total loss k/2, and a two-element list has total loss at least "
                    + "the natural truncated difference k minus two. Identify the unique member on "
                    + "singletons and reject on larger blocks to attain the first minimum. For the "
                    + "second minimum choose two members when possible; on a singleton include its "
                    + "member and one different state. These choices depend only on the input block.")),
                new DocumentBlock.DisplayFormula(Display(BlockMinima())),
                Paragraph(Text("Interchanging finite sums expresses the cost as a nonnegative "
                    + "profile-weighted sum of block costs. Each randomized decision is a convex "
                    + "combination of the action costs and hence is bounded below by the block minimum. "
                    + "For each task, the same deterministic block decision attains the minimum for "
                    + "both profiles. The resulting equalities are true Bayes infima over all randomized "
                    + "decision kernels, with an attaining decision and a lower bound for every competitor.")),
                new DocumentBlock.DisplayFormula(Display(CostFormula())),
                new DocumentBlock.DisplayFormula(Display(RiskFormula())),
                Paragraph(Text("The list-risk difference bounds the forward deficiency below by "
                    + "epsilon, and the rejection-risk difference bounds the reverse deficiency below "
                    + "by rho, by bounded-loss risk transport. The explicit common kernels attain those "
                    + "bounds. Thus the equalities concern unrestricted deficiencies, rather than an "
                    + "optimization within the displayed kernel families.")),
                new DocumentBlock.DisplayFormula(Display(ExactFormula())),
                Paragraph(Text("Consequently any coefficient bounding reverse deficiency by forward "
                    + "deficiency for every CAR pair with equal pair readouts must be at least n minus "
                    + "three halves. This is a necessary coefficient bound. Whether that coefficient "
                    + "is sufficient for all such pairs is not asserted. For every n at least four the "
                    + "present pair strictly violates the candidate n/2 bound even with its original "
                    + "minimum-with-one truncation.")),
                new DocumentBlock.DisplayFormula(Display(ObstructionFormula())),
                Paragraph(Text("For the public realization mix each profile with complete revelation "
                    + "at t = 2/n. There is one probability distribution p on Option(Block) times "
                    + "Option(Block), independent of the state, and two actual partition-valued maps "
                    + "P and Q. Each observation includes the entire common seed and its partition "
                    + "block containing the state. The whole-seed requirement includes both coordinates "
                    + "of the seed at either end.")),
                new DocumentBlock.DisplayFormula(Display(PublicDefinition())),
                Paragraph(Text("The partition marginals can be described explicitly. For w prime, "
                    + "choose the full-block partition with mass 2/[3(n minus one)] and the discrete "
                    + "partition with the remaining mass. For v prime, each pair-block partition has "
                    + "mass 4/[3n(n minus one)], each complement-of-singleton partition has mass "
                    + "2/[3n(n minus one)], and the discrete partition has mass (n minus three)/[3(n "
                    + "minus one)]. A block partition consists of that block and singleton parts "
                    + "outside it. The binomial count of pairs and the n complements give total mass one.")),
                new DocumentBlock.DisplayFormula(Display(PartitionWeights())),
                Paragraph(Text("One construction takes independent partition selectors on the two "
                    + "Option coordinates and exposes their product seed. At n = 4, the v-prime "
                    + "selector assigns mass 1/9 to each of six pair partitions, 1/18 to each of four "
                    + "triple partitions, and 1/9 to the discrete partition; the w-prime selector gives "
                    + "2/9 to the full partition and 7/9 to the discrete partition. The theorem obtains "
                    + "actual maps and a common distribution from the CAR revelation-scaling existence "
                    + "result. It does not identify those existential witnesses with a prescribed encoding "
                    + "of this product construction.")),
                Paragraph(Text("For each end, forgetting the seed is a stochastic kernel to its "
                    + "mixed block experiment. In the reverse direction, condition the seed distribution "
                    + "on occurrence of the input block when its profile weight is positive, and use a "
                    + "fixed probability row when the weight is zero. This supplies all four exact "
                    + "normalization kernels, with the same entire seed in both reverse outputs. The "
                    + "formulas below apply once with T = P and u prime = w prime, and once with T = Q "
                    + "and u prime = v prime; o star is any fixed public output letter.")),
                new DocumentBlock.DisplayFormula(Display(NormalizationFormula())),
                Paragraph(Text("Exact normalization in both directions transports deficiency by "
                    + "composition of kernels and contraction of total variation. Revelation scaling "
                    + "multiplies both original directed deficiencies by t. The public pair difference "
                    + "is t times the original pair difference, so it and the public star budget are "
                    + "zero. The actual public experiments therefore have the following exact "
                    + "deficiencies and ratio, and retain the strict truncated obstruction.")),
                new DocumentBlock.DisplayFormula(Display(PublicConclusion())))))));

    private static Formula TheoremFormula() => All(V("n"), Call("Nat"),
        Implies(LeF(D(4), V("n")), And(
            Profiles(),
            All(V("B"), V("Bset"), AndInline(LeF(D(0), Call("w", V("B"))), LeF(D(0), Call("v", V("B"))))),
            All(V("i"), V("A"), AndInline(Eqn(SumOver(V("B"), Call("W", V("i"), V("B"))), D(1)),
                Eqn(SumOver(V("B"), Call("V", V("i"), V("B"))), D(1)))),
            All(CommaList(V("i"), V("j")), V("A"), PairFormula()),
            Some(CommaList(V("F"), V("G")), Call("Kernel", V("Bset"), V("Bset")),
                And(All(CommaList(V("B"), V("C")), V("Bset"), KernelFormula()), ErrorFormula(),
                    BlockMinima(), Attainment(), RiskFormula(), ExactFormula(), ObstructionFormula(), PublicWitness())))));

    private static Formula PublicWitness() => Some(V("p"), Arrow(V("Seed"), Real()),
        Some(CommaList(V("P"), V("Q")), Arrow(V("Seed"), Call("Partition", V("A"))), And(
            All(V("s"), V("Seed"), LeF(D(0), Call("p", V("s")))), Eqn(SumOver(V("s"), Call("p", V("s"))), D(1)),
            All(V("B"), V("Bset"), AndInline(
                Eqn(SumOver(V("s"), Mul(Call("p", V("s")), Indicator(Member(V("B"), Call("parts", Call("P", V("s"))))))), Call("wprime", V("B"))),
                Eqn(SumOver(V("s"), Mul(Call("p", V("s")), Indicator(Member(V("B"), Call("parts", Call("Q", V("s"))))))), Call("vprime", V("B"))))),
            ExactPublicKernels(V("P"), V("wprime")), ExactPublicKernels(V("Q"), V("vprime")), PublicConclusion())));

    private static Formula ExactPublicKernels(Formula partition, Formula profile) =>
        Some(V("H"), Call("Kernel", Product(V("Seed"), V("Bset")), V("Bset")),
            Some(V("J"), Call("Kernel", V("Bset"), Product(V("Seed"), V("Bset"))),
                All(V("i"), V("A"), AndInline(
                    Eqn(Call("output", V("H"), Call("E", partition, V("i"))), Call("row", profile, V("i"))),
                    Eqn(Call("output", V("J"), Call("row", profile, V("i"))), Call("E", partition, V("i")))))));

    private static Formula Profiles() => Lines(
        Eqn(V("A"), Call("Fin", V("n"))), Eqn(V("Bset"), Call("NonemptySubsets", V("A"))),
        Eqn(V("b"), Div(V("n"), Mul(D(3), Sub(V("n"), D(1))))),
        Eqn(V("a"), Div(D(2), Mul(D(3), Sub(V("n"), D(1))))),
        Eqn(V("c"), Div(D(1), Mul(D(3), Sub(V("n"), D(1))))),
        Eqn(V("x"), Div(D(1), Mul(D(2), Sub(V("n"), D(1))))),
        Eqn(Call("w", V("B")), Add(Mul(Sub(D(1), V("b")), Indicator(Eqn(Card(V("B")), D(1)))),
            Mul(V("b"), Indicator(Eqn(Card(V("B")), V("n")))))),
        Eqn(Call("v", V("B")), Add(Mul(V("a"), Indicator(Eqn(Card(V("B")), D(2)))),
            Mul(V("c"), Indicator(Eqn(Card(V("B")), Sub(V("n"), D(1))))))),
        Eqn(Call("row", V("u"), V("i"), V("B")), Mul(Indicator(Member(V("i"), V("B"))), Call("u", V("B")))),
        Eqn(V("W"), Call("row", V("w"))), Eqn(V("V"), Call("row", V("v"))));

    private static Formula PairFormula() => Lines(
        Eqn(Call("r", V("u"), V("i"), V("j")), SumOver(Member(V("B"), V("Bset")),
            Mul(Indicator(AndInline(Member(V("i"), V("B")), Member(V("j"), V("B")))), Call("u", V("B"))))),
        Implies(Call("neq", V("i"), V("j")), AndInline(Eqn(Call("r", V("w"), V("i"), V("j")), V("b")),
            Eqn(Call("r", V("v"), V("i"), V("j")), V("b")))),
        Eqn(Call("Delta", V("i"), V("j")), Sub(Call("r", V("v"), V("i"), V("j")), Call("r", V("w"), V("i"), V("j")))),
        Eqn(Call("Delta", V("i"), V("j")), D(0)),
        Eqn(V("R"), Mul(Div(D(1), D(2)), Call("max", V("i"),
            SumOver(Call("neq", V("j"), V("i")), Call("max", Call("Delta", V("i"), V("j")), D(0)))))), Eqn(V("R"), D(0)));

    private static Formula DeficiencyDefinition() => Lines(
        Eqn(Call("TV", V("p"), V("q")), Mul(Div(D(1), D(2)), SumOver(V("B"), Abs(Sub(Call("p", V("B")), Call("q", V("B"))))))),
        Eqn(Call("d", V("X"), V("Y")), Call("inf", Typed(V("K"), Call("Kernel", V("Bset"), V("Bset"))),
            Call("max", V("i"), Call("TV", Call("Y", V("i")), Call("output", V("K"), Call("X", V("i"))))))),
        Eqn(Call("d", V("X"), V("Y")), Call("finiteDeficiency", V("Y"), V("X"))));

    private static Formula KernelFormula() => Lines(
        Eqn(Call("F", V("B"), V("C")), Ite(Eqn(Card(V("B")), D(1)),
            Div(Indicator(AndInline(Eqn(Card(V("C")), D(2)), Call("subset", V("B"), V("C")))), Sub(V("n"), D(1))),
            Ite(Eqn(Card(V("B")), V("n")), Div(Indicator(Eqn(Card(V("C")), Sub(V("n"), D(1)))), V("n")), Indicator(Eqn(V("B"), V("C")))))),
        Eqn(Call("G", V("B"), V("C")), Ite(Eqn(Card(V("B")), D(2)),
            Add(Mul(V("x"), Indicator(Eqn(V("C"), V("A")))), Mul(Div(Sub(D(1), V("x")), D(2)),
                Indicator(AndInline(Eqn(Card(V("C")), D(1)), Call("subset", V("C"), V("B")))))),
            Ite(Eqn(Card(V("B")), Sub(V("n"), D(1))), Indicator(Eqn(V("C"), V("A"))), Indicator(Eqn(V("B"), V("C")))))));

    private static Formula ErrorFormula() => AndInline(
        Eqn(V("epsilon"), Div(D(1), Mul(D(3), Sub(V("n"), D(1))))),
        Eqn(V("rho"), Div(Sub(Mul(D(2), V("n")), D(3)), Mul(D(6), Sub(V("n"), D(1))))),
        All(V("i"), V("A"), AndInline(
            Eqn(Call("TV", Call("V", V("i")), Call("output", V("F"), Call("W", V("i")))), V("epsilon")),
            Eqn(Call("TV", Call("W", V("i")), Call("output", V("G"), Call("V", V("i")))), V("rho")))));

    private static Formula LossFormula() => Lines(
        Eqn(Call("pi", V("i")), Div(D(1), V("n"))),
        Eqn(V("Drej"), Call("Option", V("A"))), Eqn(Call("lrej", V("i"), Call("none")), Div(D(1), D(2))),
        Eqn(Call("lrej", V("i"), Call("some", V("j"))), Indicator(Call("neq", V("i"), V("j")))),
        Eqn(V("Dlist"), Call("SubsetsOfCardinality", V("A"), D(2))),
        Eqn(Call("llist", V("i"), V("D")), Indicator(Call("not", Member(V("i"), V("D"))))));

    private static Formula BlockMinima() => AndInline(
        Eqn(Call("mrej", V("B")), Call("min", Call("natSub", Card(V("B")), D(1)), Div(Card(V("B")), D(2)))),
        Eqn(Call("mlist", V("B")), Call("natSub", Card(V("B")), D(2))),
        All(V("j"), Call("set", V("rej"), V("list")), All(V("B"), V("Bset"), AndInline(
            All(V("d"), Call("Actions", V("j")), LeF(Div(Call("m", V("j"), V("B")), V("n")),
                Div(SumOver(Member(V("i"), V("B")), Call("loss", V("j"), V("i"), V("d"))), V("n")))),
            Some(V("d"), Call("Actions", V("j")), Eqn(
                Div(SumOver(Member(V("i"), V("B")), Call("loss", V("j"), V("i"), V("d"))), V("n")),
                Div(Call("m", V("j"), V("B")), V("n"))))))));

    private static Formula CostFormula() => Lines(
        Eqn(Call("Cost", V("u"), V("l"), V("D")), Mul(Div(D(1), V("n")),
            SumOver(V("B"), Mul(Call("u", V("B")), SumOver(V("d"), Mul(Call("D", V("B"), V("d")),
                SumOver(Member(V("i"), V("B")), Call("l", V("i"), V("d"))))))))), Attainment());

    private static Formula Attainment() => All(V("j"), Call("set", V("rej"), V("list")),
        Some(V("Dstar"), Call("Kernel", V("Bset"), Call("Actions", V("j"))),
            All(V("u"), Call("set", V("w"), V("v")), AndInline(
                Eqn(Call("Risk", V("j"), Call("row", V("u"))), Call("Cost", V("u"), Call("loss", V("j")), V("Dstar"))),
                All(V("D"), Call("Kernel", V("Bset"), Call("Actions", V("j"))),
                    LeF(Call("Cost", V("u"), Call("loss", V("j")), V("Dstar")),
                        Call("Cost", V("u"), Call("loss", V("j")), V("D"))))))));

    private static Formula RiskFormula() => AndInline(
        Eqn(Call("Risk", V("rej"), V("W")), Div(V("n"), Mul(D(6), Sub(V("n"), D(1))))),
        Eqn(Call("Risk", V("rej"), V("V")), Div(D(1), D(2))),
        Eqn(Call("Risk", V("list"), V("W")), Div(Sub(V("n"), D(2)), Mul(D(3), Sub(V("n"), D(1))))),
        Eqn(Call("Risk", V("list"), V("V")), Div(Sub(V("n"), D(3)), Mul(D(3), Sub(V("n"), D(1))))));

    private static Formula ExactFormula() => AndInline(
        Eqn(Call("d", V("W"), V("V")), V("epsilon")), Eqn(Call("d", V("V"), V("W")), V("rho")),
        Eqn(Div(V("rho"), V("epsilon")), Sub(V("n"), Div(D(3), D(2)))));

    private static Formula ObstructionFormula() => AndInline(
        All(V("C"), Real(), Implies(LeF(V("rho"), Mul(V("C"), V("epsilon"))), LeF(Sub(V("n"), Div(D(3), D(2))), V("C")))),
        Eqn(Call("min", D(1), Add(V("R"), Mul(Div(V("n"), D(2)), V("epsilon")))),
            Div(V("n"), Mul(D(6), Sub(V("n"), D(1))))),
        LtF(Call("min", D(1), Add(V("R"), Mul(Div(V("n"), D(2)), V("epsilon")))), V("rho")));

    private static Formula PublicDefinition() => Lines(
        Eqn(V("t"), Div(D(2), V("n"))), LtF(D(0), V("t")), LeF(V("t"), D(1)),
        Eqn(Call("I", V("B")), Indicator(Eqn(Card(V("B")), D(1)))),
        Eqn(V("wprime"), Add(Mul(Sub(D(1), V("t")), V("I")), Mul(V("t"), V("w")))),
        Eqn(V("vprime"), Add(Mul(Sub(D(1), V("t")), V("I")), Mul(V("t"), V("v")))),
        Eqn(V("Seed"), Product(Call("Option", V("Bset")), Call("Option", V("Bset")))),
        Eqn(Call("E", V("T"), V("i"), Pair(V("s"), V("B"))),
            Mul(Call("p", V("s")), Indicator(Eqn(Call("part", Call("T", V("s")), V("i")), V("B"))))),
        Eqn(SumOver(V("s"), Mul(Call("p", V("s")), Indicator(Member(V("B"), Call("parts", Call("T", V("s"))))))), Call("uprime", V("B"))));

    private static Formula PartitionWeights() => Lines(
        Eqn(Call("qw", Call("some", V("A"))), Div(D(2), Mul(D(3), Sub(V("n"), D(1))))),
        Eqn(Call("qw", Call("none")), Sub(D(1), Div(D(2), Mul(D(3), Sub(V("n"), D(1)))))),
        Implies(Call("neq", V("B"), V("A")), Eqn(Call("qw", Call("some", V("B"))), D(0))),
        Eqn(Call("qv", Call("some", V("B"))), Ite(Eqn(Card(V("B")), D(2)),
            Div(D(4), Mul(D(3), V("n"), Sub(V("n"), D(1)))), Ite(Eqn(Card(V("B")), Sub(V("n"), D(1))),
                Div(D(2), Mul(D(3), V("n"), Sub(V("n"), D(1)))), D(0)))),
        Eqn(Call("qv", Call("none")), Div(Sub(V("n"), D(3)), Mul(D(3), Sub(V("n"), D(1))))),
        Eqn(Call("p", Pair(V("s1"), V("s2"))), Mul(Call("qw", V("s1")), Call("qv", V("s2")))));

    private static Formula NormalizationFormula() => Lines(
        Eqn(Call("H", Pair(V("s"), V("C")), V("B")), Indicator(Eqn(V("C"), V("B")))),
        Eqn(Call("J", V("B"), Pair(V("s"), V("C"))), Ite(Eqn(Call("uprime", V("B")), D(0)),
            Indicator(Eqn(Pair(V("s"), V("C")), V("ostar"))),
            Ite(AndInline(Eqn(V("C"), V("B")), Member(V("B"), Call("parts", Call("T", V("s"))))),
                Div(Call("p", V("s")), Call("uprime", V("B"))), D(0)))),
        All(V("i"), V("A"), AndInline(
            Eqn(Call("output", V("H"), Call("E", V("T"), V("i"))), Call("row", V("uprime"), V("i"))),
            Eqn(Call("output", V("J"), Call("row", V("uprime"), V("i"))), Call("E", V("T"), V("i"))))));

    private static Formula PublicConclusion() => AndInline(
        All(CommaList(V("i"), V("j")), V("A"), AndInline(
            Eqn(Call("Deltaprime", V("i"), V("j")),
                Sub(Call("r", V("vprime"), V("i"), V("j")), Call("r", V("wprime"), V("i"), V("j")))),
            Eqn(Call("Deltaprime", V("i"), V("j")), D(0)))),
        Eqn(V("Rprime"), Mul(Div(D(1), D(2)), Call("max", V("i"),
            SumOver(Call("neq", V("j"), V("i")), Call("max", Call("Deltaprime", V("i"), V("j")), D(0)))))),
        Eqn(V("Rprime"), D(0)),
        Eqn(Call("d", V("EP"), V("EQ")), Mul(V("t"), V("epsilon"))),
        Eqn(Call("d", V("EP"), V("EQ")), Div(D(2), Mul(D(3), V("n"), Sub(V("n"), D(1))))),
        Eqn(Call("d", V("EQ"), V("EP")), Mul(V("t"), V("rho"))),
        Eqn(Call("d", V("EQ"), V("EP")), Div(Sub(Mul(D(2), V("n")), D(3)), Mul(D(3), V("n"), Sub(V("n"), D(1))))),
        Eqn(Div(Mul(V("t"), V("rho")), Mul(V("t"), V("epsilon"))), Sub(V("n"), Div(D(3), D(2)))),
        LtF(Call("min", D(1), Add(V("Rprime"), Mul(Div(V("n"), D(2)), V("t"), V("epsilon")))), Mul(V("t"), V("rho"))));

    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula Card(Formula value) => Call("card", value);
    private static Formula Indicator(Formula value) => Call("indicator", value);
    private static Formula Typed(Formula value, Formula type) => Seq(value, Colon, Sp, type);
    private static Formula All(Formula value, Formula type, Formula body) => Seq(Forall, Sp, Typed(value, type), Comma, Sp, body);
    private static Formula Some(Formula value, Formula type, Formula body) => Seq(Exists, Sp, Typed(value, type), Comma, Sp, body);
    private static Formula Arrow(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula Product(Formula a, Formula b) => Seq(a, Sp, Times, Sp, b);
    private static Formula Pair(Formula a, Formula b) => Paren(CommaList(a, b));
    private static Formula Real() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Ite(Formula condition, Formula yes, Formula no) => Call("ite", condition, yes, no);
    private static Formula Member(Formula a, Formula b) => Seq(a, Sp, InMacro, Sp, b);
    private static Formula Eqn(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula LeF(Formula a, Formula b) => Seq(a, Sp, Leq, Sp, b);
    private static Formula LtF(Formula a, Formula b) => Seq(a, Sp, Lt, Sp, b);
    private static Formula Div(Formula a, Formula b) => Seq(Frac, Grp(a), Grp(b));
    private static Formula Abs(Formula value) => Seq(Lvert, Sp, value, Sp, Rvert);
    private static Formula Paren(Formula value) => Seq(Open, value, Close);
    private static Formula SumOver(Formula index, Formula body) => Seq(new Formula.Subscript(Sum, Grp(index)), Sp, Grp(body));
    private static Formula Display(Formula body) => Disp(Seq(Begin, Grp(F.Id("gathered")), body, End, Grp(F.Id("gathered"))));
    private static Formula Add(params Formula[] terms) => Infix(Plus, terms);
    private static Formula Sub(params Formula[] terms) => Paren(Infix(Minus, terms));
    private static Formula Mul(params Formula[] terms) => Infix(Cdot, terms);
    private static Formula CommaList(params Formula[] terms) => Infix(Comma, terms);
    private static Formula AndInline(params Formula[] clauses) => Paren(Infix(Land, clauses));
    private static Formula Infix(Formula op, Formula[] terms)
    {
        var items = new List<Formula>();
        for (var i = 0; i < terms.Length; i++)
        {
            if (i > 0) items.AddRange([Sp, op, Sp]);
            items.Add(terms[i]);
        }
        return Seq([.. items]);
    }
    private static Formula Lines(params Formula[] clauses) => Infix(Seq(RowBreak, Grp()), clauses);
    private static Formula And(params Formula[] clauses) => Paren(Infix(Seq(Land, RowBreak, Grp()), clauses.Select(Paren).ToArray()));
    private static Formula Implies(params Formula[] clauses) => Infix(Seq(Rightarrow, RowBreak, Grp()), clauses.Select(Paren).ToArray());
}
