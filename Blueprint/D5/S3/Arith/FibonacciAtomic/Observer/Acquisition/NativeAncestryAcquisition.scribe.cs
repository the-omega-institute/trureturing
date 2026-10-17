using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer.Acquisition;

internal sealed class NativeAncestryAcquisitionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Observer/Acquisition/NativeAncestryAcquisition.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Literal replies reveal independent three-leaf bracket choices one support at a time.",
        H("Native ancestry acquisition"), Blocks(
            Paragraph(Text("The native family replaces any subset of the original three-leaf B subtrees by D. "
                + "The two fillings have the same ordered leaf labels and different brackets. "
                + "Addresses are arbitrary finite left and right words, including the root and absent nodes. "
                + "A raw history retains every query, its actual four-valued reply and its chronological position.")),
            Def("support", "Six changed literal addresses",
                "The support at p consists of pL, pR, pLL, pLR, pRL and pRR. At every one of these addresses the B and D replies differ, even after identifying branch with absent. All other replies agree."),
            Thm("outside_support_invariance", "Equality away from changed supports", OutsideFormula(),
                "For every finite source, simultaneously changing any collection of its original B positions preserves the reply at each address outside the supports of the changed positions. There is no depth bound on the source or the query. The proof follows the actual tree, with the six local differences handled at a B root."),
            Def("hit", "The positions tested by a record",
                "A position is hit exactly when one of its six support addresses occurs in the history. Repeated queries and queries outside every support add no positions."),
            Def("Consistent", "Agreement with the whole raw record",
                "A choice is consistent when every recorded query has exactly the recorded reply in its actual native source."),
            Def("compatible", "The complete compatible subset family",
                "Filter the full powerset of original positions by consistency with the raw history."),
            Def("compatibleSources", "The compatible actual trees",
                "Map every compatible subset to its actual simultaneously filled source. The native cube injectivity distinguishes all of these sources."),
            Def("posterior", "Uniform-prior conditioning",
                "Every original subset has prior weight one divided by two to the number of original positions. On the compatible family, divide this common weight by its total over that family. A truthful history makes that total positive."),
            Thm("native_record_face", "An exact face and its conditional entropy", FaceFormula(),
                "For generation n at least three, let P be the original positions and K equal fib(n minus two). A truthful history fixes precisely the choices on H, the hit set. The compatible subsets are an interval from A intersect H to its union with P minus H, so there are exactly two to the power K minus the size of H. Conditioning the uniform law on all subsets gives the uniform law on this face. Its Shannon entropy divided by log two is K minus the size of H. Whenever this history is a successful run of a fixed source-independent deterministic policy, execute_transfer gives the same terminal history and answer on every compatible source. A first hit fixes one previously free bit; repetitions and unrelated queries leave the face unchanged. This prior is distinct from the half-canonical, half-singleton prior used for classification."),
            Def("CubeRun", "A source-independent terminating policy",
                "One history policy is shared by all subsets of the original positions. Each subset has a finite actual execute run from the empty history, with its recorded terminal trace and Boolean answer. True denotes the canonical source."),
            Def("Correct", "Canonical versus defect correctness",
                "The terminal answer is true exactly for the empty defect subset, on the entire native family."),
            Thm("optimal_canonical_queries", "Exact worst-case first-address cost", CanonicalFormula(),
                "Every correct policy must hit all K supports on the empty defect subset: an unhit singleton defect otherwise replays the same terminal run with the opposite correct answer. Distinct supports are disjoint and therefore require distinct paid literal addresses. Querying pL once for every original p gives a correct policy on every subset, always pays K addresses, and attains the lower bound. This scan factors through the coarse history that identifies branch and absent replies. Only first-use literal source reads are counted; address generation, address length, program and memory costs are separate quantities."),
            Def("success", "The half-canonical, half-singleton score",
                "The empty subset has weight one half. Every singleton defect has weight one divided by twice K. The score is the resulting average correct-classification probability for a fixed policy."),
            Def("reward", "Correct classification on one input",
                "The reward is one exactly when the terminal Boolean answer matches whether the defect subset is empty, and zero otherwise."),
            Thm("optimal_single_defect_success", "Exact success under a hard support budget", BayesFormula(),
                "For any nonnegative integer q at most K, impose at most q hit supports on every cube input and every fixed random seed. Along the canonical run, every unhit singleton has the same answer. If that answer is canonical, only hit singleton defects can add success; if it is defect, the entire singleton contribution is at most one half. Thus success is at most one half plus q divided by twice K. A fixed scan of any q distinct original positions attains equality, including q zero, q K and K one. Integrating over any source-independent probability law preserves the upper bound for measurable terminal scores. If every candidate has expected correct reward at least one minus delta, with delta less than one half, then q is at least one minus twice delta times K."))));

    private static DocumentBlock Def(string name, string title, string prose) => Describe.Lean(
        DescribeId.Create("ancestry-acquisition-" + name.ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
    private static DocumentBlock Thm(string name, string title, Formula formula, string prose) => Describe.Lean(
        DescribeId.Create("ancestry-acquisition-" + name.Replace("_", "-").ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
    private static Formula Frac(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula V(string n) => F.Id(n);
    private static Formula Op(string n) => Seq(Operatorname, Grp(V(n)));
    private static Formula Call(string n, params Formula[] args) => new Formula.Apply(Op(n), [.. args]);
    private static Formula Par(Formula a) => Seq(Open, a, Close);
    private static Formula All(string n, Formula type, Formula body) => Seq(Forall, Sp, V(n), Colon, Sp, type, Comma, Sp, Par(body));
    private static Formula Some(string n, Formula type, Formula body) => Seq(Exists, Sp, V(n), Colon, Sp, type, Comma, Sp, Par(body));
    private static Formula EqOf(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));
    private static Formula IffOf(Formula a, Formula b) => Seq(Par(a), Sp, Iff, Sp, Par(b));
    private static Formula And(params Formula[] xs) => Seq(xs.Select((x, i) => i == 0 ? Par(x) : Seq(Sp, Land, Sp, Par(x))).ToArray());
    private static Formula Le(Formula a, Formula b) => Seq(a, Sp, Leq, Sp, b);
    private static Formula Mem(Formula a, Formula b) => Seq(a, Sp, InMacro, Sp, b);
    private static Formula Arr(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula Card(Formula a) => Call("card", a);
    private static Formula Subset(Formula a, Formula b) => Call("Subset", a, b);
    private static Formula Inter(Formula a, Formula b) => Call("inter", a, b);
    private static Formula NatSub(Formula a, Formula b) => Call("natSub", a, b);
    private static Formula Positions(Formula t) => Call("positions", t);
    private static Formula Variant(Formula t, Formula a) => Call("variant", t, a);
    private static Formula Cost(Formula r, Formula a) => Card(Call("paid", Call("trace", r, a)));
    private static Formula Budget(Formula t, Formula q, Formula r) => All("A", Call("Finset", Op("Address")),
        Imp(Subset(V("A"), Positions(t)), Le(Card(Call("hit", t, Call("trace", r, V("A")))), q)));
    private static Formula Bound(Formula q, Formula k) => Seq(Frac(D(1), D(2)), Plus, Frac(q, Seq(D(2), Times, k)));
    private static Formula OnGeneration(Formula body) => All("n", Op("Nat"), Imp(Le(D(3), V("n")), body));

    private static Formula OutsideFormula()
    {
        Formula t = V("t"), a = V("A"), b = V("B"), q = V("q"), p = V("p");
        Formula outside = All("p", Op("Address"), Imp(Mem(p, Call("symmDiff", a, b)),
            Seq(Neg, Sp, Par(Mem(q, Call("support", p))))));
        return Disp(All("t", Op("Source"), All("A", Call("Finset", Op("Address")),
            All("B", Call("Finset", Op("Address")), Imp(Subset(a, Positions(t)), Imp(Subset(b, Positions(t)),
                All("q", Op("Address"), Imp(outside,
                    EqOf(Call("readout", q, Variant(t, a)), Call("readout", q, Variant(t, b)))))))))));
    }

    private static Formula FaceFormula()
    {
        Formula t = Call("T", V("n")), a = V("A"), b = V("B"), h = V("h");
        Formula hit = Call("hit", t, h), family = Call("compatible", t, h);
        Formula free = NatSub(Call("fib", NatSub(V("n"), D(2))), Card(hit));
        Formula face = All("B", Call("Finset", Op("Address")), Imp(Subset(b, Positions(t)),
            IffOf(Call("Consistent", t, b, h), EqOf(Inter(b, hit), Inter(a, hit)))));
        Formula uniform = All("B", family, EqOf(Call("posterior", t, h, b), Frac(D(1), Card(family))));
        Formula entropy = EqOf(Frac(Call("shannonEntropy", Call("posterior", t, h)), Call("log", D(2))), free);
        return Disp(OnGeneration(All("A", Call("Finset", Op("Address")), Imp(Subset(a, Positions(t)),
            All("h", Op("RawHistory"), Imp(Call("Consistent", t, a, h),
                And(face, EqOf(Card(family), new Formula.Power(D(2), free)),
                    EqOf(Card(Call("compatibleSources", t, h)), new Formula.Power(D(2), free)), uniform, entropy)))))));
    }

    private static Formula CanonicalFormula()
    {
        Formula t = Call("T", V("n")), k = Call("fib", NatSub(V("n"), D(2))), r = V("R");
        Formula lower = All("R", Call("CubeRun", t), Imp(Call("Correct", t, r), Le(k, Cost(r, Emptyset))));
        Formula upper = Some("R", Call("CubeRun", t), And(Call("Correct", t, r),
            Call("FactorsThrough", Call("policy", r), Op("kappaHist")),
            All("A", Call("Finset", Op("Address")), Imp(Subset(V("A"), Positions(t)), Le(Cost(r, V("A")), k))),
            EqOf(Cost(r, Emptyset), k)));
        return Disp(OnGeneration(And(lower, upper)));
    }

    private static Formula BayesFormula()
    {
        Formula t = Call("T", V("n")), k = Call("fib", NatSub(V("n"), D(2))), q = V("q"), r = V("R");
        Formula lower = All("R", Call("CubeRun", t), Imp(Budget(t, q, r), Le(Call("success", t, r), Bound(q, k))));
        Formula attaining = Some("R", Call("CubeRun", t), And(Budget(t, q, r), EqOf(Call("success", t, r), Bound(q, k))));
        Formula seedBudget = All("s", V("O"), Budget(t, q, Call("R", V("s"))));
        Formula average = All("O", Op("Type"), Imp(Call("MeasurableSpace", V("O")),
            All("m", Call("ProbabilityMeasure", V("O")), All("R", Arr(V("O"), Call("CubeRun", t)),
                Imp(Call("Measurable", Call("seedScore", t, r)),
                    Imp(seedBudget,
                        Le(Call("integralScore", V("m"), t, r), Bound(q, k))))))));
        Formula accuracy = All("A", Call("Finset", Op("Address")), Imp(Subset(V("A"), Positions(t)),
            Le(Seq(D(1), Minus, V("d")), Call("integralReward", V("m"), r, V("A")))));
        Formula decisions = All("A", Call("Finset", Op("Address")), Imp(Subset(V("A"), Positions(t)),
            Call("Measurable", Call("seedAnswer", r, V("A")))));
        Formula error = All("O", Op("Type"), Imp(Call("MeasurableSpace", V("O")),
            All("m", Call("ProbabilityMeasure", V("O")), All("R", Arr(V("O"), Call("CubeRun", t)),
                All("d", Op("Real"), Imp(Seq(V("d"), Sp, Lt, Sp, Frac(D(1), D(2))),
                    Imp(decisions, Imp(seedBudget, Imp(accuracy,
                        Le(Seq(Par(Seq(D(1), Minus, D(2), Times, Sp, V("d"))), Times, k), q))))))))));
        return Disp(OnGeneration(All("q", Op("Nat"), Imp(Le(q, k), And(lower, attaining, average, error)))));
    }
}
