using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.DecisionRisk;

internal sealed class CARFourStateReverseObstructionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Estimation/DecisionRisk/CARFourStateReverseObstruction.";
    private const string Car = "D5/S3/Estimation/DecisionRisk/CARApproximateRecovery.";
    private const string Risk = "D5/S3/Estimation/SequentialDecisionRisk/FiniteDeficiencyRiskTransfer.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A four-state CAR pair has equal pair collisions and directed deficiencies 1/9 and 5/18; "
            + "an actual common public partition seed preserves the counterexample after halving.",
        H("Four-state obstruction to the coefficient-two reverse bound"),
        Blocks(
            Paragraph(Text("Let A = Fin 4 = {0,1,2,3}. The observation alphabet B consists of all fifteen "
                + "nonempty subsets: {0}, {1}, {2}, {3}, {0,1}, {0,2}, {0,3}, {1,2}, {1,3}, {2,3}, "
                + "{0,1,2}, {0,1,3}, {0,2,3}, {1,2,3}, and A. Zero-weight letters remain present. "),
                Ref(Car + "row"), Text(" assigns u(B) when i belongs to B and zero otherwise. "),
                Ref(Car + "pair"), Text(" sums u(B) over the blocks containing both states.")),
            new DocumentBlock.DisplayFormula(Profiles()),
            Paragraph(Ref(Risk + "finiteDeficiency"), Text(" takes the target first and source second. "
                + "Write d(u,z) for toReal(finiteDeficiency(row(z),row(u))). It is the infimum of "
                + "the maximum statewise half-L1 error over every stochastic kernel on the full alphabet. "
                + "All fifteen input rows are probability rows. One kernel acts at every state, with no "
                + "support or block-containment restriction. Kernels can output zero-weight letters "
                + "and blocks not containing the state. ENNReal.ofReal, denoted ofReal below, embeds "
                + "nonnegative real values into the extended nonnegative reals.")),
            new DocumentBlock.DisplayFormula(Domains()),
            Describe.Lean(
                DescribeId.Create("car-four-state-reverse-obstruction"),
                DeclarationHandle.Create(Prefix + "result"),
                H("A complete certificate refutes the proposed reverse inequality"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The formal conclusion is Not claim, where claim is the implication "
                        + "from the entire Certificate displayed below to the coefficient-two upper bound. "
                        + "The proof constructs that certificate and its strict violation; none of its "
                        + "Bayes values, deficiencies, or public realizations is an assumed input. "
                        + "Classically the negative implication entails the certificate itself. "
                        + "There is one public theorem, result, and no separately asserted positive companion.")),
                    new DocumentBlock.DisplayFormula(CertificateFormula()),
                    Paragraph(Text("Every weight is nonnegative. Each w row sums to 5/9 + 4/9 = 1; "
                        + "each v row sums to 3(2/9) + 3(1/9) = 1. For distinct i,j, the only common "
                        + "w block is A, while v has their pair and two triples, giving 4/9 on both sides. "
                        + "Consequently every signed pair difference is zero and R(w,v) = 0.")),
                    Paragraph(Text("The common forward kernel H sends each singleton uniformly to its "
                        + "three containing pairs, and sends A uniformly to the four triples. Its other "
                        + "rows are identity rows. For state i it produces 5/27 on each containing pair, "
                        + "a deficit of 1/27 against 2/9, and 1/9 on every triple. The three containing "
                        + "triples match the target; the unique triple omitting i has excess 1/9. "
                        + "Hence the half-L1 error of this single H is 1/9 at every state.")),
                    new DocumentBlock.DisplayFormula(Kernels()),
                    Paragraph(Text("The common reverse kernel J sends a pair to A with probability 1/6 "
                        + "and to each endpoint singleton with probability 5/12; every triple goes to A. "
                        + "Its other rows are identity rows. At state i the output gives 5/18 to {i}, "
                        + "5/54 to each of the other three singletons, and 4/9 to A. The target gives "
                        + "5/9 to {i}, zero to the other singletons, and 4/9 to A. The error is 5/18. "
                        + "Both kernels are stochastic on all letters, including unused input letters.")),
                    Paragraph(Text("For the matching lower bounds use the uniform prior pi(i)=1/4 and "
                        + "two genuine bounded decision tasks. Bayes risk optimizes over all stochastic "
                        + "decision kernels from blocks to actions, using the same decision rule at "
                        + "every state. For each block, every randomized row is a convex combination "
                        + "of its action costs and is at least their minimum. Choosing a minimizing "
                        + "action at each block forms one deterministic decision kernel attaining "
                        + "all block minima simultaneously. The certificate exposes one such common "
                        + "deterministic kernel for each task, together with its block minima, its costs "
                        + "under both w and v, and optimality against every randomized decision kernel "
                        + "under both profiles. Thus the displayed values are unrestricted "
                        + "Bayes optima, including at zero-weight blocks.")),
                    new DocumentBlock.DisplayFormula(BayesFormula()),
                    Paragraph(Text("The identification-or-rejection task has actions 0,1,2,3 and reject. "
                        + "Correct identification costs zero, an incorrect label costs one, and reject "
                        + "costs one half at every state. For block sizes 1,2,3,4, the weighted minima "
                        + "are respectively 0,1/4,3/8,1/2. A singleton chooses its label; a pair can "
                        + "choose an endpoint or reject; triples and the full block choose reject. "
                        + "Its Bayes risks are 2/9 under w and 1/2 under v, a reverse gap of 5/18.")),
                    Paragraph(Text("The list task has the six pairs as actions, in the order {0,1}, "
                        + "{0,2}, {0,3}, {1,2}, {1,3}, {2,3}. Its loss is one precisely when the "
                        + "state lies outside the chosen pair. The minima by block size are "
                        + "0,0,1/4,1/2. Choose a containing pair for a singleton, the block itself "
                        + "for a pair, a two-element subblock for a triple, and any pair for A. "
                        + "The risks are 2/9 under w and 1/9 under v, a forward gap of 1/9.")),
                    new DocumentBlock.DisplayFormula(TaskValues()),
                    Paragraph(Ref(Risk + "deficiency_risk_bound"), Text(" transports a bounded loss "
                        + "through every common simulation kernel. Source Bayes risk is no larger "
                        + "than target Bayes risk plus maximum state TV. The list task therefore "
                        + "bounds every forward kernel below by 1/9; the rejection task bounds "
                        + "every reverse kernel below by 5/18. Taking the infimum and combining with "
                        + "H and J proves both exact deficiencies. This argument uses bounded risk "
                        + "transfer and attained finite decision minima, without a duality assumption.")),
                    new DocumentBlock.DisplayFormula(Bounds()),
                    Paragraph(Text("At this pair the proposed coefficient-two right side is 2/9, "
                        + "and the reverse deficiency exceeds it by 1/18. If any real c bounds "
                        + "the reverse deficiency by c times the forward deficiency here, c is "
                        + "at least 5/2. Therefore every universally valid coefficient on four-state "
                        + "equal-pair CAR experiments is at least 5/2. Sufficiency of 5/2 is not proved.")),
                    new DocumentBlock.DisplayFormula(MixedProfiles()),
                    Paragraph(Ref("D5/S3/Estimation/DecisionRisk/CARRevelationScaling.result"),
                        Text(" applies at t=1/2 in [0,2/4]. Mixing with complete revelation gives "
                            + "w'=mix(w), v'=mix(v), pair collisions 2/9, R(w',v')=0, and exact "
                            + "deficiencies 1/18 and 5/36. The coefficient-two violation is 1/36.")),
                    Paragraph(Text("For an explicit ordinary-partition law, let P0 be the discrete "
                        + "partition and PA the one-part partition. The w' law gives P0 mass 7/9 "
                        + "and PA mass 2/9. The v' law gives P0 mass 1/9, each of the six partitions "
                        + "consisting of a pair and two remaining singletons mass 1/9, and each of "
                        + "the four partitions consisting of a triple and its complementary singleton "
                        + "mass 1/18. Its mass is 1/9+6/9+4/18=1; a given singleton has mass "
                        + "1/9+3/9+1/18=1/2. These are ordinary partitions of the same state space.")),
                    Paragraph(Text("The Lean seed is Seed=Option(B) times Option(B), with the "
                        + "product of the two selector laws constructed by revelation scaling. "
                        + "A none selector gives P0, and some(B) gives B with every outside state "
                        + "as a singleton. The law p is nonnegative, sums to one, and is independent "
                        + "of the state. P reads the first selector and Q the second. Both actual "
                        + "observations reveal the entire same seed s and the part P_s(i) or Q_s(i). "
                        + "The public experiment E(p,T)(i,(s,B)) is p(s) when T_s.part(i)=B and zero otherwise.")),
                    new DocumentBlock.DisplayFormula(PublicFormula()),
                    Paragraph(Text("For each T=P,Q, forgetting the seed is a deterministic common "
                        + "kernel F. If the induced block weight h(B) is positive, reconstruct the "
                        + "whole seed with probability p(s) indicator(B is a part of T_s)/h(B), "
                        + "keeping B in the output. This law does not depend on the unknown state. "
                        + "At a zero-weight input block, use any fixed output point mass, which "
                        + "completes a stochastic row. Nonnegativity ensures that p(s)=0 whenever "
                        + "h(B)=0 and B is a part of T_s. Since T_s.part(i)=B exactly when "
                        + "B is a part and i belongs to B, both channel identities hold at every state.")),
                    new DocumentBlock.DisplayFormula(EquivalenceKernels()),
                    Paragraph(Text("Precompose and postcompose any simulation kernel with these "
                        + "four exact equivalence kernels. Stochastic composition and TV contraction "
                        + "give both inequalities between each public deficiency and its block "
                        + "deficiency, hence equality. The public forward value is 1/18, the public "
                        + "reverse value is 5/36, and their coefficient-two gap is 1/36. "
                        + "The certificate supplies an actual common state-independent full-seed "
                        + "realization and its equivalence kernels, not merely the marginal profiles.")),
                    Paragraph(Text("This refutes universal sufficiency of n/2 at n=4, including "
                        + "ordinary public partition experiments. It preserves the original half-L1 "
                        + "normalization, maximum over states, all fifteen letters, and unrestricted "
                        + "common kernels. It does not settle the optimal four-state coefficient or "
                        + "the optimal replacement bound for general n at least four."))),
                DescribeRole.Theorem))));

    private static Formula I(string s) => F.Id(s);
    private static Formula Q(int n, int d) => Div(Num(n), Num(d));
    private static Formula Row(Formula u) => Call("row", u);
    private static Formula FD(Formula target, Formula source) => Call("finiteDeficiency", target, source);
    private static Formula DR(Formula source, Formula target) => FD(Row(target), Row(source));
    private static Formula OR(Formula x) => Call("ofReal", x);
    private static Formula TR(Formula x) => Call("toReal", x);
    private static Formula R(Formula u, Formula z) => Call("star", u, z);
    private static Formula Mix(Formula u) => Call("mix", u);
    private static Formula RiskOf(Formula l, Formula u) => Call("finiteBayesRisk", I("pi"), l, Row(u));
    private static Formula Bound(Formula u, Formula z) => OR(Call("min", D(1), Add(R(u,z), Mul(D(2),TR(DR(u,z))))));
    private static Formula Profiles() => Display(Lines(
        Eqn(Call("w", I("B")), Ite(Eqn(Call("card", I("B")), D(1)), Q(5,9), Ite(Eqn(Call("card", I("B")),D(4)),Q(4,9),D(0)))),
        Eqn(Call("v", I("B")), Ite(Eqn(Call("card", I("B")),D(2)),Q(2,9),Ite(Eqn(Call("card",I("B")),D(3)),Q(1,9),D(0)))),
        Eqn(Call("row",I("u"),I("i"),I("B")),Ite(Member(I("i"),I("B")),Call("u",I("B")),D(0))),
        Eqn(Call("pair",I("u"),I("i"),I("j")),SumOver(Typed(I("B"),Call("Block",I("A"))),Ite(And(Member(I("i"),I("B")),Member(I("j"),I("B"))),Call("u",I("B")),D(0)))),
        Eqn(R(I("u"),I("z")),Mul(Q(1,2),Call("max",I("i"),I("A"),SumOver(Seq(I("j"),Sp,Neq,Sp,I("i")),Call("max",Sub(Call("pair",I("z"),I("i"),I("j")),Call("pair",I("u"),I("i"),I("j"))),D(0))))))));
    private static Formula Domains() => Display(Lines(
        Eqn(Call("TV",I("p"),I("q")),Mul(Q(1,2),SumOver(I("C"),Abs(Sub(Call("p",I("C")),Call("q",I("C"))))))),
        Eqn(Call("channelOutput",I("K"),I("p"),I("C")),SumOver(I("B"),Mul(Call("p",I("B")),Call("K",I("B"),I("C"))))),
        Eqn(FD(I("Y"),I("X")),Call("iInf",Lambda(Typed(I("K"),Call("FiniteMarkovKernel",I("B"),I("B"))),OR(Call("max",I("i"),I("A"),Call("TV",Call("Y",I("i")),Call("channelOutput",Call("val",I("K")),Call("X",I("i")))))))))));
    private static Formula TheoremFormula() => Display(Call("Not",Implies(I("Certificate"),LeF(DR(I("v"),I("w")),Bound(I("w"),I("v"))))));
    private static Formula CertificateFormula()
    {
        Formula w=I("w"),v=I("v"),i=I("i"),j=I("j"),b=I("B"),c=I("c"),H=I("H"),J=I("J");
        Formula Stochastic(Formula k)=>Call("IsRowStochastic",k);
        Formula RowSum(Formula u)=>All(i,I("A"),Eqn(SumOver(Typed(b,Call("Block",I("A"))),Call("row",u,i,b)),D(1)));
        Formula Error(Formula k,Formula u,Formula z,Formula e)=>All(i,I("A"),Eqn(Call("TV",Call("row",z,i),Call("channelOutput",k,Call("row",u,i))),e));
        return Display(Eqn(I("Certificate"),And(
            All(b,Call("Block",I("A")),And(LeF(D(0),Call("w",b)),LeF(D(0),Call("v",b)))),RowSum(w),RowSum(v),Stochastic(H),Stochastic(J),
            Error(H,w,v,Q(1,9)),Error(J,v,w,Q(5,18)),
            All(i,I("A"),All(j,I("A"),Implies(Seq(i,Sp,Neq,Sp,j),And(Eqn(Call("pair",w,i,j),Q(4,9)),Eqn(Call("pair",v,i,j),Q(4,9)))))),
            Eqn(R(w,v),D(0)),Eqn(RiskOf(I("rejectLoss"),w),OR(Q(2,9))),Eqn(RiskOf(I("rejectLoss"),v),OR(Q(1,2))),
            Eqn(RiskOf(I("listLoss"),w),OR(Q(2,9))),Eqn(RiskOf(I("listLoss"),v),OR(Q(1,9))),
            Attainment(I("rejectLoss"),I("rejectMin"),5,Q(2,9),Q(1,2)),
            Attainment(I("listLoss"),I("listMin"),6,Q(2,9),Q(1,9)),
            Eqn(DR(w,v),OR(Q(1,9))),Eqn(DR(v,w),OR(Q(5,18))),LtF(Bound(w,v),DR(v,w)),
            Eqn(Sub(TR(DR(v,w)),Call("min",D(1),Add(R(w,v),Mul(D(2),TR(DR(w,v)))))),Q(1,18)),
            All(c,Real(),Implies(LeF(DR(v,w),OR(Mul(c,TR(DR(w,v))))),LeF(Q(5,2),c))),
            All(i,I("A"),All(j,I("A"),Implies(Seq(i,Sp,Neq,Sp,j),And(
                Eqn(Call("pair",Mix(w),i,j),Q(2,9)),Eqn(Call("pair",Mix(v),i,j),Q(2,9)))))),
            Eqn(R(Mix(w),Mix(v)),D(0)),Eqn(DR(Mix(w),Mix(v)),OR(Q(1,18))),Eqn(DR(Mix(v),Mix(w)),OR(Q(5,36))),
            Eqn(Sub(TR(DR(Mix(v),Mix(w))),Call("min",D(1),Add(R(Mix(w),Mix(v)),Mul(D(2),TR(DR(Mix(w),Mix(v))))))),Q(1,36)),PublicClause())));
    }
    private static Formula Attainment(Formula loss,Formula minimum,int n,Formula cw,Formula cv)
    {
        Formula b=I("B"),a=I("a"),i=I("i"),f=I("f"),d=I("delta"),k=I("k");
        Formula blocks=Call("Block",I("A")),actions=Call("Fin",Num(n)),kernel=Call("FiniteMarkovKernel",blocks,actions);
        Formula BlockCost(Formula action)=>SumOver(Typed(i,I("A")),Mul(Call("pi",i),Ite(Member(i,b),D(1),D(0)),Apply(loss,i,action)));
        Formula Cost(Formula u,Formula decision)=>Call("finiteBayesCost",I("pi"),loss,Row(u),Call("val",decision));
        return Some(f,Arrow(blocks,actions),Some(d,kernel,And(
            All(b,blocks,All(a,actions,Eqn(Apply(Call("val",d),b,a),Ite(Eqn(Apply(f,b),a),D(1),D(0))))),
            All(b,blocks,Eqn(Apply(minimum,b),BlockCost(Apply(f,b)))),
            All(b,blocks,All(a,actions,LeF(Apply(minimum,b),BlockCost(a)))),
            Eqn(Cost(I("w"),d),cw),Eqn(Cost(I("v"),d),cv),
            All(k,kernel,And(LeF(Cost(I("w"),d),Cost(I("w"),k)),LeF(Cost(I("v"),d),Cost(I("v"),k)))))));
    }
    private static Formula Kernels() => Display(Lines(
        Eqn(Call("H",I("B"),I("C")),Ite(Eqn(Call("card",I("B")),D(1)),Ite(And(Eqn(Call("card",I("C")),D(2)),Call("subset",I("B"),I("C"))),Q(1,3),D(0)),Ite(Eqn(Call("card",I("B")),D(4)),Ite(Eqn(Call("card",I("C")),D(3)),Q(1,4),D(0)),Ite(Eqn(I("B"),I("C")),D(1),D(0))))),
        Eqn(Call("J",I("C"),I("B")),Ite(Eqn(Call("card",I("C")),D(2)),Ite(Eqn(Call("card",I("B")),D(4)),Q(1,6),Ite(And(Eqn(Call("card",I("B")),D(1)),Call("subset",I("B"),I("C"))),Q(5,12),D(0))),Ite(Eqn(Call("card",I("C")),D(3)),Ite(Eqn(Call("card",I("B")),D(4)),D(1),D(0)),Ite(Eqn(I("B"),I("C")),D(1),D(0)))))));
    private static Formula BayesFormula()=>Display(Lines(
        Eqn(Call("pi",I("i")),Q(1,4)),
        Eqn(Call("cost",I("u"),I("l"),I("delta")),SumOver(I("B"),Mul(Call("u",I("B")),SumOver(Typed(I("a"),I("D")),Mul(Call("delta",I("B"),I("a")),SumOver(Member(I("i"),I("B")),Mul(Q(1,4),Call("l",I("i"),I("a"))))))))),
        Eqn(Call("h",I("l"),I("B")),Call("min",I("a"),I("D"),SumOver(Member(I("i"),I("B")),Mul(Q(1,4),Call("l",I("i"),I("a")))))),
        Eqn(RiskOf(I("l"),I("u")),OR(SumOver(I("B"),Mul(Call("u",I("B")),Call("h",I("l"),I("B"))))))));
    private static Formula TaskValues()=>Display(Lines(
        Eqn(Call("rejectLoss",I("i"),I("a")),Ite(Eqn(I("a"),D(4)),Q(1,2),Ite(Eqn(I("i"),I("a")),D(0),D(1)))),
        Eqn(Call("listLoss",I("i"),I("L")),Ite(Member(I("i"),I("L")),D(0),D(1))),
        Eqn(Call("rejectMin",I("B")),Ite(Eqn(Call("card",I("B")),D(1)),D(0),Ite(Eqn(Call("card",I("B")),D(2)),Q(1,4),Ite(Eqn(Call("card",I("B")),D(3)),Q(3,8),Q(1,2))))),
        Eqn(Call("listMin",I("B")),Ite(LeF(Call("card",I("B")),D(2)),D(0),Ite(Eqn(Call("card",I("B")),D(3)),Q(1,4),Q(1,2))))));
    private static Formula Bounds()=>Display(Lines(
        All(I("K"),Call("FiniteMarkovKernel",I("B"),I("B")),And(
            LeF(Q(1,9),Call("uniformSimulationError",Row(I("v")),Row(I("w")),I("K"))),
            LeF(Q(5,18),Call("uniformSimulationError",Row(I("w")),Row(I("v")),I("K"))))),
        Eqn(Sub(Q(5,18),Mul(D(2),Q(1,9))),Q(1,18)),LtF(D(0),Q(1,18)),
        Eqn(Sub(Q(5,36),Mul(D(2),Q(1,18))),Q(1,36)),LtF(D(0),Q(1,36))));
    private static Formula MixedProfiles()=>Display(Lines(
        Eqn(Call("mix",I("u"),I("B")),Add(Mul(Q(1,2),Ite(Eqn(Call("card",I("B")),D(1)),D(1),D(0))),Mul(Q(1,2),Call("u",I("B"))))),
        Eqn(Call("mix",I("w"),I("B")),Ite(Eqn(Call("card",I("B")),D(1)),Q(7,9),Ite(Eqn(Call("card",I("B")),D(4)),Q(2,9),D(0)))),
        Eqn(Call("mix",I("v"),I("B")),Ite(Eqn(Call("card",I("B")),D(1)),Q(1,2),Ite(Eqn(Call("card",I("B")),D(2)),Q(1,9),Ite(Eqn(Call("card",I("B")),D(3)),Q(1,18),D(0))))),
        All(I("i"),I("A"),All(I("j"),I("A"),Implies(Seq(I("i"),Sp,Neq,Sp,I("j")),And(Eqn(Call("pair",Mix(I("w")),I("i"),I("j")),Q(2,9)),Eqn(Call("pair",Mix(I("v")),I("i"),I("j")),Q(2,9))))))));
    private static Formula Pub(Formula t)=>Call("E",I("p"),t);
    private static Formula PublicClause()
    {
        Formula s=I("s"),b=I("B"),i=I("i"),p=I("p"),P=I("P"),Qp=I("Q");
        Formula Profile(Formula t,Formula u)=>All(b,Call("Block",I("A")),Eqn(SumOver(Typed(s,I("Seed")),Ite(Member(b,Call("parts",Apply(t,s))),Apply(p,s),D(0))),Call("mix",u,b)));
        Formula Channels(Formula t,Formula u)=>Some(I("F"),Call("FiniteMarkovKernel",Product(I("Seed"),Call("Block",I("A"))),Call("Block",I("A"))),Some(I("G"),Call("FiniteMarkovKernel",Call("Block",I("A")),Product(I("Seed"),Call("Block",I("A")))),And(
            All(i,I("A"),Eqn(Call("channelOutput",Call("val",I("F")),Apply(Pub(t),i)),Call("row",Mix(u),i))),
            All(i,I("A"),Eqn(Call("channelOutput",Call("val",I("G")),Call("row",Mix(u),i)),Apply(Pub(t),i))))));
        return Some(p,Arrow(I("Seed"),Real()),Some(P,Arrow(I("Seed"),Call("Finpartition",I("A"))),Some(Qp,Arrow(I("Seed"),Call("Finpartition",I("A"))),And(
            All(s,I("Seed"),LeF(D(0),Apply(p,s))),Eqn(SumOver(Typed(s,I("Seed")),Apply(p,s)),D(1)),Profile(P,I("w")),Profile(Qp,I("v")),Channels(P,I("w")),Channels(Qp,I("v")),
            Eqn(FD(Pub(Qp),Pub(P)),OR(Q(1,18))),Eqn(FD(Pub(P),Pub(Qp)),OR(Q(5,36))),
            LtF(OR(Call("min",D(1),Add(R(Mix(I("w")),Mix(I("v"))),Mul(D(2),TR(FD(Pub(Qp),Pub(P))))))),FD(Pub(P),Pub(Qp))),
            Eqn(Sub(TR(FD(Pub(P),Pub(Qp))),Call("min",D(1),Add(R(Mix(I("w")),Mix(I("v"))),Mul(D(2),TR(FD(Pub(Qp),Pub(P))))))),Q(1,36))))));
    }
    private static Formula PublicFormula()=>Display(Lines(
        Eqn(I("Seed"),Product(Call("Option",Call("Block",I("A"))),Call("Option",Call("Block",I("A"))))),
        Eqn(Call("p",Paren(Seq(I("a"),Comma,I("b")))),Mul(Call("q",I("w"),I("a")),Call("q",I("v"),I("b")))),
        Eqn(Call("E",I("p"),I("T"),I("i"),Paren(Seq(I("s"),Comma,I("B")))),Ite(Eqn(Call("part",Call("T",I("s")),I("i")),I("B")),Call("p",I("s")),D(0)))));
    private static Formula EquivalenceKernels()=>Display(Lines(
        Eqn(Call("F",Paren(Seq(I("s"),Comma,I("C"))),I("B")),Ite(Eqn(I("C"),I("B")),D(1),D(0))),
        Eqn(Call("G",I("B"),Paren(Seq(I("s"),Comma,I("C")))),Ite(Eqn(Call("h",I("B")),D(0)),Ite(Eqn(Paren(Seq(I("s"),Comma,I("C"))),I("ostar")),D(1),D(0)),Ite(And(Eqn(I("B"),I("C")),Member(I("B"),Call("parts",Call("T",I("s"))))),Div(Call("p",I("s")),Call("h",I("B"))),D(0))))));

    private static Formula Apply(Formula f,params Formula[] args)=>new Formula.Apply(f,[..args]);
    private static Formula Typed(Formula value, Formula type) => Seq(value, Colon, Sp, type);
    private static Formula All(Formula x,Formula t,Formula b)=>Seq(Forall,Sp,Typed(x,t),Comma,Sp,b);
    private static Formula Some(Formula x,Formula t,Formula b)=>Seq(Exists,Sp,Typed(x,t),Comma,Sp,b);
    private static Formula Arrow(Formula a,Formula b)=>Seq(a,Sp,To,Sp,b);
    private static Formula Product(Formula a,Formula b)=>Seq(a,Sp,Times,Sp,b);
    private static Formula Lambda(Formula a,Formula b)=>Paren(Seq(a,Sp,Mapsto,Sp,b));
    private static Formula Real()=>Seq(Mathbb,Grp(I("R")));
    private static Formula Ite(Formula c,Formula y,Formula n)=>Call("ite",c,y,n);
    private static Formula Member(Formula a,Formula b)=>Seq(a,Sp,InMacro,Sp,b);
    private static Formula Eqn(Formula a,Formula b)=>Seq(a,Sp,Eq,Sp,b);
    private static Formula LeF(Formula a,Formula b)=>Seq(a,Sp,Leq,Sp,b);
    private static Formula LtF(Formula a,Formula b)=>Seq(a,Sp,Lt,Sp,b);
    private static Formula Div(Formula a,Formula b)=>Seq(Frac,Grp(a),Grp(b));
    private static Formula Abs(Formula a)=>Seq(Lvert,Sp,a,Sp,Rvert);
    private static Formula Paren(Formula a)=>Seq(Open,a,Close);
    private static Formula SumOver(Formula i,Formula b)=>Seq(new Formula.Subscript(Sum,Grp(i)),Sp,Grp(b));
    private static Formula Display(Formula b)=>Disp(Seq(Begin,Grp(I("gathered")),b,End,Grp(I("gathered"))));
    private static Formula Add(params Formula[] xs)=>Infix(Plus,xs);
    private static Formula Sub(params Formula[] xs)=>Infix(Minus,xs);
    private static Formula Mul(params Formula[] xs)=>Infix(Cdot,xs);
    private static Formula And(params Formula[] xs)=>Paren(Infix(Seq(Land,RowBreak,Grp()),xs));
    private static Formula Implies(Formula a,Formula b)=>Infix(Rightarrow,[Paren(a),Paren(b)]);
    private static Formula Lines(params Formula[] xs)=>Infix(Seq(RowBreak,Grp()),xs);
    private static Formula Infix(Formula op,Formula[] xs)
    {
        var items=new List<Formula>();
        for(var i=0;i<xs.Length;i++) { if(i>0) items.AddRange([Sp,op,Sp]); items.Add(xs[i]); }
        return Seq([..items]);
    }
}
