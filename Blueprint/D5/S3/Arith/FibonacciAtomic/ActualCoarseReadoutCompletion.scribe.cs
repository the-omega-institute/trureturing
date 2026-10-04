using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class ActualCoarseReadoutCompletionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/ActualCoarseReadoutCompletion.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every finite coarse route has a globally correct actual-tree completion with complete leaf verification, existence-controlled acquisition and an exact address cache.",
        H("Common Completion of Finite Coarse Routes"),
        Blocks(
            Paragraph(Text("Source, Address, Reply, Positive, Strategy, readout, leaves, paid and terminal are the original actual-tree objects. Positive means membership in the third Fibonacci substitution image. The existing coarse quotient kappa preserves the two leaf labels and merges branch with absent into none. CoarseObservable requires equality of policy actions on every pair of raw histories with equal coarse histories, including unreachable histories.")),
            Def("encodeHistory", "Reply representatives", "encodeHistory maps each coarse report to the same address and a raw representative: some(true) to alpha, some(false) to beta, and none to branch. This is a section for policy evaluation. It gives no existence certificate for an arbitrary address. Write N(h)=encodeHistory(kappa_hist(h))."),
            Def("compileRaw", "Finite route compilation", "The route p is the existing finite dependent PassiveProtocol over Address with response Option Bool. A decoder maps its complete coarse chronological history to an optional prototype index. compileRaw(F,decode,p,g) compiles each query through kappa and accumulates the coarse routing history g. A selected stop starts verifyController(F(i),leaves(F(i))); an unselected stop starts fallback. Neither phase receives the preceding route as its own logical history."),
            Def("cachedExecute", "Exact address caching", "cachedExecute takes a native raw policy, fuel, logical history, cache and input. A logical request is always recorded. If its exact address occurs in the cache, the stored reply is reused. Otherwise the actual readout is obtained and appended. The cache begins empty, contains only reports acquired in the same run, and stores neither inferred prefixes nor prototype knowledge. Repeated logical requests consume logical fuel but do not add paid addresses."),
            Describe.Lean(DescribeId.Create("actual-coarse-readout-completion-contract"),
                DeclarationHandle.Create(Prefix + "completion_contract"),
                H("All-source completion and exact prototype fees"),
                StatementSource.FromAuthor(ContractFormula()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("In the formula RH is the native raw history type. R(p,U) is runPassiveProtocol(q,W -> leafLabel(W,q),p,U), K is kappa_hist, N is the representative map defined above, and C is compileRaw(F,decode,p,empty). V(i) is verifyController(F(i),leaves(F(i))). CP and CO denote controllerPolicy and controllerOutcome. empty is the empty list, concat is chronological list concatenation, report(q,y) is the dependent address-response pair, and one(x) is a singleton list. leafTrace(V) maps every address in leaves(V) to its actual labelled reply. A(g) is the finite set of addresses in a coarse history g, and L(V) is the existing leafAddresses(V). E(pi,n,U) is execute(readout,pi.policy,n,empty,U); CE(pi,n,U) is cachedExecute(pi.policy,n,empty,empty,U). T(pi,U) is terminal(pi,U). Truth(U,cache) means every stored reply equals the actual readout at its exact address, and ND(cache) means the cache address list has no duplicate.")),
                    Paragraph(Text("Phase(U,h,s) states that K(h)=R(p,U) implies pi.policy(concat(h,s)) equals CP(V(i),N(s)) when decode(K(h))=some(i), and acquisitionPolicy(N(s)) when it is none. Failed(V,pre,rest,q,y,s) states that leaves(V)=concat(pre,cons(q,rest)) and kappa(y) differs from leafLabel(V,q) imply CP(verifyController(V,leaves(V)),N(concat(concat(leafTrace(pre,V),one(report(q,y))),s)))=acquisitionPolicy(N(s)). Here leafTrace(pre,V) records exactly the matching reports on the listed prefix pre. These equalities hold for every future logical suffix s, so both phases start with fresh logical histories.")),
                    Paragraph(Text("Acq(U,h,q) states that h is a prefix of acquisitionTrace(empty,U) and acquisitionPolicy(N(h))=inl(q) imply three conclusions: an actual subtree exists at q; kappa(readout(q,U))=none then forces this subtree to be a branch; and every nonroot q is concat(v,one(d)) for a parent v and direction d whose actual branch report occurs in h. The parent condition supplies existence from a preceding real request. A cached none alone supplies no such evidence.")),
                    Paragraph(Text("Prototype(pi,i) applies only when decode(R(p,F(i)))=some(i). It gives K(T(pi,F(i)).history)=concat(R(p,F(i)),K(leafTrace(F(i)))) and paid(T(pi,F(i)).history)=union(A(R(p,F(i))),L(F(i))). No prototype fee formula is asserted when the route chooses another index or abandons routing.")),
                    Paragraph(Text("The full result quantifies every finite coarse route, every decoder and every positive prototype family, including the empty family. Correctness and finite termination quantify all Source inputs without a size, positivity or family-membership promise. The known raw phase theorem supplies leaf-verifier correctness and finite raw execution. Reachable acquisition prefixes fix the quotient representatives; the frontier invariant establishes actual subtree existence and previously reported parents. The compiled coarse route therefore has the same actual execution as the raw controller. Cache hits reproduce real reports, while misses append one new address, making the final cache truthful and its paid set exactly the logical request set. The prototype trace identity adds the complete leaf phase to precisely the selected route."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Def(string name, string title, string prose) => Describe.Lean(
        DescribeId.Create("actual-coarse-completion-" + name.ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
    private static Formula V(string s) => F.Id(s);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, Par(body));
    private static Formula Some(string name, Formula type, Formula body) => Seq(Exists, Sp, V(name), Colon, Sp, type, Comma, Sp, Par(body));
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));
    private static Formula And(params Formula[] xs) => Seq(xs.Select((x, i) => i == 0 ? Par(x) : Seq(Sp, Land, Sp, Par(x))).ToArray());
    private static Formula Eq(Formula a, Formula b) => Seq(a, Sp, F.Eq, Sp, b);
    private static Formula Iff(Formula a, Formula b) => Seq(Par(a), Sp, F.Iff, Sp, Par(b));

    private static Formula ContractFormula()
    {
        Formula pi = V("pi"), m = V("m"), family = V("F"), p = V("p"), decode = V("decode");
        Formula u = V("U"), n = V("n"), t = V("t"), b = V("b"), cache = V("cache");
        Formula rh = V("RH"), source = Call("Source"), i = V("i");
        Formula pair = Call("pair", t, b);
        Formula execution = All("U", source, Some("n", V("Nat"), Some("t", rh,
            Some("b", V("Bool"), Some("cache", rh, And(
                Eq(Call("E", pi, n, u), Call("some", pair)),
                Eq(Call("CE", pi, n, u), Call("some", Call("pair", pair, cache))),
                Eq(pair, Call("T", pi, u)),
                Iff(Eq(b, V("true")), Call("Positive", u)),
                Call("ND", cache), Call("Truth", u, cache),
                Eq(Call("paid", cache), Call("paid", t))))))));
        Formula phases = All("U", source, All("h", rh, All("s", rh,
            Call("Phase", u, V("h"), V("s")))));
        Formula failure = All("V", source, All("pre", Call("List", Call("Address")),
            All("rest", Call("List", Call("Address")), All("q", Call("Address"),
            All("y", Call("Reply"), All("s", rh,
            Call("Failed", V("V"), V("pre"), V("rest"), V("q"), V("y"), V("s"))))))));
        Formula acquisition = All("U", source, All("h", rh, All("q", Call("Address"),
            Call("Acq", u, V("h"), V("q")))));
        Formula conclusion = Some("pi", Call("Strategy"), And(
            Eq(Call("policy", pi), Call("compose", Call("CP", V("C")), V("N"))),
            Call("CoarseObservable", Call("policy", pi)), execution, phases, failure, acquisition,
            All("i", Call("Fin", m), Call("Prototype", pi, i))));
        return All("m", V("Nat"), All("F", Call("Function", Call("Fin", m), source),
            Imp(All("i", Call("Fin", m), Call("Positive", Call("F", i))),
                All("p", Call("PassiveProtocol", Call("Address"), Call("Option", V("Bool"))),
                    All("decode", Call("Function", V("CH"), Call("Option", Call("Fin", m))), conclusion)))));
    }
}
