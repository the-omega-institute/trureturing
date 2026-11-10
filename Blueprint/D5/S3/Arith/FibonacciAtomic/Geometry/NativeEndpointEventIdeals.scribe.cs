using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Geometry;

internal sealed class NativeEndpointEventIdealsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Geometry/NativeEndpointEventIdeals.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Membership-defined native event ideals supply actual guarded execution adequacy.",
        H("Native endpoint event ideals"), Blocks(
        Paragraph(Text("Source is the unchanged Bool free magma, alpha is true and beta is false. Events consist of one split at each target branch and one promotion at each root or right-born position whose target subtree is not alpha. EventLe uses address prefix ancestry and promotion before split at one address. Ideal is supported lower closure. cutTerm is defined solely by membership: without a local split it is the initial or promoted leaf; after splitting it recursively combines the two child cuts. Created records strict ancestor creating splits. The original NativeGuardedLeafRepair.run, Call.shift, ActualLeafHistoryRigidity.subtree and ActualImageAddressCertificate.replace are retained. NativePostClockInverse supplies only its original address/kind/replacement/edited definitions; no clock inverse or serial-clock data is used.")),
        Paragraph(Text("Original Lean suppliers: "),
            Ref("D5/S3/Arith/FibonacciAtomic/GenealogicalFiberTransport"), Text(" (Source); "),
            Ref("D5/S3/Arith/FibonacciAtomic/ActualLeafHistoryRigidity"), Text(" (subtree); "),
            Ref("D5/S3/Arith/FibonacciAtomic/ActualImageAddressCertificate"), Text(" (replace); "),
            Ref("D5/S3/Arith/FibonacciAtomic/Geometry/NativeMaterialRootRecognition"), Text(" (D); "),
            Ref("D5/S3/Arith/FibonacciAtomic/Geometry/NativeGuardedLeafRepair"), Text(" (Call.shift, run, D_mul, run_preserves_D); "),
            Ref("D5/S3/Arith/FibonacciAtomic/Observer/OriginalVector/NativePostClockInverse"), Text(" (address, kind, replacement, edited only); "),
            Ref("D5/S3/ConceptDynamics/PartialIdentification/EnabledPathSwapConnectivity"), Text(" (Enabled, Exec, ExtensionList, result).")),
        Paragraph(Text("Mathematical notation. Bool is {false,true}; Source is the free ordered binary-tree algebra on Bool, with leaf constructor of : Bool → Source and branch constructor mul : Source × Source → Source. Write alpha = of(true), beta = of(false). Address = List(Bool), [] is the empty address, and ++ is list concatenation. Call is the disjoint union of promote(p) and split(p), for p : Address. shift(c,p) prefixes p to the address of c, retaining its constructor. List(X) is the type of finite lists over X; Set(X) is its power set. some and none are the constructors of Option(X); ite(P,x,y) is x if proposition P holds (or Boolean P is true), and y otherwise. All quantifiers in the displays range over the indicated full types.")),
        Paragraph(Text("Native operations. subtree : Address × Source → Option(Source) follows false to the left child and true to the right child; the empty address returns the whole term, and descent across a leaf returns none. replace(t,p,v) replaces the subtree at p by v and leaves a crossed leaf unchanged. The address of promote(p) or split(p) is p; phase(promote(p)) = 0 and phase(split(p)) = 1. The relation c ≤ d means that address(c) is a prefix of address(d) and that equal addresses imply phase(c) ≤ phase(d); c < d means c ≤ d and not d ≤ c. Event(b,t) is the subtype of Calls in events(b,t), with this induced order; val forgets only the membership proof. erase(l) = l.map(val), retaining the order and every Call label.")),
        Paragraph(Text("Endpoint definitions. For b,a : Bool, events(b,of(a)) is {promote([])} exactly when b = true and a = false, and is empty otherwise. For b : Bool and l,r : Source, events(b,mul(l,r)) is the union of {split([])}, the conditional set ({promote([])} when b = true and empty otherwise), the shifts by [false] of events(false,l), and the shifts by [true] of events(true,r). For b,c : Bool and p : Address, birthAt(b,[]) = b and birthAt(b,c::p) = birthAt(c,p). For I : Set(Call) and p : Address, sectionAt(I,p) = {c : Call | shift(c,p) belongs to I}. Created(I,[]) is true, and Created(I,b::p) means split([]) belongs to I and Created(sectionAt(I,[b]),p).")),
        Paragraph(Text("Membership cuts. For b,a : Bool and I : Set(Call), cutTerm(b,of(a),I) is of(a) unless b = true and a = false; in that case it is beta if promote([]) belongs to I, and alpha otherwise. For b : Bool, l,r : Source and I : Set(Call), cutTerm(b,mul(l,r),I) is mul(cutTerm(false,l,sectionAt(I,[false])),cutTerm(true,r,sectionAt(I,[true]))) if split([]) belongs to I; otherwise it is beta when b = false or promote([]) belongs to I, and alpha otherwise. No execution or lower-set hypothesis enters these definitions.")),
        Paragraph(Text("Predicates and execution. D(t) means no left-child address in t is an alpha leaf: for every p : Address, the original readout(p++[false],t) does not return its alpha readout constructor. Born(b,t) means D(t) and (b = false implies t is not alpha). Ideal(b,t,I) means I is a subset of events(b,t) and, for all c in events(b,t) and d in I, c ≤ d implies c belongs to I. Guard(promote(p),u) means subtree(p,u) = some(alpha); Guard(split(p),u) means subtree(p,u) = some(beta). Enabled(b,t,I,e) means e is not in I and every d in events(b,t) with d < e belongs to I. edited(u,promote(p)) = replace(u,p,beta), and edited(u,split(p)) = replace(u,p,mul(beta,alpha)). run(u,[]) = some(u); run(u,e::w) = run(edited(u,e),w) if Guard(e,u), and none otherwise. insert(e,I) = I union {e}.")),
        Paragraph(Text("Finite-order notation. For b : Bool, t : Source and K : Set(Event(b,t)), raw(b,t,K) = {val(e) | e belongs to K}. IsLowerSet(K) means every event below a member of K also belongs to K. Exec(K,[],J) means K = J; Exec(K,e::l,J) means e is fresh, every strict predecessor of e is in K, and Exec(insert(e,K),l,J). ExtensionList(K,J,l) means l has no repetitions, its members are exactly J minus K, and for every earlier a and later b in l, not b ≤ a. These are the original EnabledPathSwapConnectivity predicates on Event(b,t). The symbol univ denotes the whole indicated Event type, including when it is empty. All occurrences of events as sets use the underlying set of the finite inventory.")),
        R("root_before", "Creating root split precedence", "The root split strictly precedes every call shifted into either child. This consumed order helper is used by lower-set enabling and the exact AA17.2 edge proof."),
        R("shift_lt", "Strict order under one child shift", "Shifting two original calls into the same child preserves and reflects their strict prefix/phase comparison. This consumed normalization helper transports the causal edge proof and native enabling."),
        R("lt_promote_root", "No predecessor of the root promotion", "No original call strictly precedes the root promotion in the prefix/phase order. The helper supplies the root promotion case of enabling and exact causal closure."),
        R("lt_split_root", "Only predecessor of the root split", "An original call strictly precedes the root split if and only if it is the root promotion. Endpoint support separately decides whether that promotion actually belongs to the finite event set."),
        R("lt_shift", "Predecessors of a shifted event", "Every strict predecessor of a call shifted into child b is a root promotion, a root split, or the same child shift of a strict predecessor. Conversely each listed case strictly precedes that shifted event. Endpoint support and lower closure remove any absent root promotion in the native application."),
        R("shift_mem", "Event support under a child shift", "A shifted call belongs to the endpoint event set of a branch exactly when its unshifted call belongs to the corresponding child event set with that child birth type. This consumed helper connects the recursive local edge proof to the same original event inventory."),
        R("subtree_partial", "Actual addressed subtrees of membership cuts", "For every target subtree at address p, the actual subtree of the membership-defined cut is absent exactly when some strict ancestor creating split is absent. Otherwise it is the local membership cut of that target subtree, with birth type determined by the final address bit. This statement requires no execution or ideal hypothesis."),
        R("guard_ancestor", "Native guard and creating ancestors", "For every non-alpha target subtree, promotion is guarded exactly when all strict ancestor splits have occurred, its position was born alpha, its promotion is absent and its local split is absent when the target is a branch. Splitting is guarded exactly when all creating ancestors have occurred, the position was born beta or its promotion has occurred, and its branch split is absent. These equivalences use the unchanged subtree operation and actual alpha/beta constructors. They are the structural witness used in the subsequent guard and transition proofs."),
        R("partial_empty", "Initial birth leaf", "For a target in the original no-left-alpha domain compatible with its specified birth type, the empty membership cut is precisely that birth leaf. Born beta cannot have alpha as target."),
        R("partial_insert", "Actual native transition", "For every supported lower set, every endpoint event whose actual leaf guard holds changes the cut by the original edited replacement, giving exactly the membership cut with that event inserted. The split case proves both child cuts are still their birth leaves; the descendant case descends through an already present creating split."),
        R("guard_enabled", "Actual guards are finite-order enabling", "For every compatible target, supported lower set and endpoint event, the actual native leaf guard is equivalent to freshness and membership of every strict causal predecessor. The proof locates the actual non-alpha target subtree of each event, characterizes enabling by creating-ancestor and local membership conditions, and applies guard_ancestor at that event address. This consumes the full addressed-subtree correspondence, with no simulation or reachability premise."),
        R("cut_events", "History-independent inventory", "Reading the endpoint-defined event inventory of a membership cut returns exactly its supported lower set. Root events and shifted child events are separated by their actual addresses. This invariant makes distinct lower sets have distinct partial endpoints."),
        R("cut_full", "Full endpoint reconstruction", "The cut containing every endpoint label reconstructs the original target term. The proof recursively reconstructs both children after the root split; it does not select a serial history."),
        R("execution_adequacy", "Native executions between arbitrary ideals", "For all two lower sets and every list of endpoint labels, abstract enabled execution between those sets is equivalent to successful original run between their membership cuts. The reverse induction maintains the reached ideal at every prefix. Each step obtains its guard from the preceding equivalence and uses the actual replacement theorem; equality of terminal cuts is reflected by the event inventory invariant."),
        R("linear_extension_histories", "Exact labelled extension histories", "For every original D target and every list of its labelled endpoint events, successful original run from alpha to that target is equivalent to being an extension list from the empty ideal to the full ideal. Only after native adequacy is established does the proof invoke EnabledPathSwapConnectivity.result for the generic finite-poset correspondence."),
        R("all_histories", "No hidden membership premise on histories", "Every raw successful Call word from alpha to a D target has a lift to exactly its endpoint-labelled linear extension, and conversely every such lift is an actual successful word. A separate source-operation induction proves that every actual successful call adds its own fresh event to the native inventory. Thus membership in the endpoint label set is proved from the raw run, never assumed as a history premise.") ,
        Paragraph(Text("The owning source clauses are Unified Joint Law Bridge Proposition 5.3 legal generation and causal inverse, Proposition 5.6 causal versus serial history, and Atomic Generation Acquisition AA17.2 enabled-event adequacy. These theorems do not establish the actual seven-coordinate group laws, mixed selected partitions, controller measurability, eight-event signed probability law or common full-tree submass. The complete seven/eight target remains open. The all-assignment promised-comb application is NativePromiseCausalBoundary.result.")))));
    private static DocumentBlock R(string name, string title, string text) =>
        Describe.Lean(DescribeId.Create("native-endpoint-event-" + name.Replace("_", "-")),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Statement(name)),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(text))), DescribeRole.Theorem);

    private static Formula V(string name) => F.Id(name);
    private static Formula P(Formula f) => Seq(Open, f, Close);
    private static Formula C(string name, params Formula[] args) =>
        args.Length == 0 ? Seq(Operatorname, Grp(V(name)))
            : new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula Q(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, P(body));
    private static Formula Ex(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, V(name), Colon, Sp, type, Comma, Sp, P(body));
    private static Formula Bind(string[] names, Formula[] types, Formula body)
    {
        for (var i = names.Length - 1; i >= 0; --i) body = Q(names[i], types[i], body);
        return body;
    }
    private static Formula BindFlat(string[] names, Formula[] types, Formula body)
    {
        for (var i = names.Length - 1; i >= 0; --i)
            body = Seq(Forall, Sp, V(names[i]), Colon, Sp, types[i], Comma, Sp, body);
        return body;
    }
    private static Formula Rel(Formula x, Formula op, Formula y) => Seq(x, Sp, op, Sp, y);
    private static Formula Eqn(Formula x, Formula y) => Rel(x, F.Eq, y);
    private static Formula Im(Formula x, Formula y) => Rel(P(x), Rightarrow, P(y));
    private static Formula Iffn(Formula x, Formula y) => Rel(P(x), Iff, P(y));
    private static Formula And(Formula x, Formula y) => Rel(P(x), Land, P(y));
    private static Formula Or(Formula x, Formula y) => Rel(P(x), Lor, P(y));
    private static Formula Not(Formula x) => Seq(Neg, Sp, P(x));
    private static Formula Mem(Formula x, Formula y) => Rel(x, InMacro, y);
    private static Formula Ands(params Formula[] fs)
    {
        var f = fs[^1];
        for (var i = fs.Length - 2; i >= 0; --i) f = And(fs[i], f);
        return f;
    }
    private static Formula Bool => C("Bool");
    private static Formula Source => C("Source");
    private static Formula Call => C("Call");
    private static Formula Set(Formula type) => C("Set", type);
    private static Formula List(Formula type) => C("List", type);
    private static Formula Nil => Seq(OpenBracket, CloseBracket);
    private static Formula One(Formula b) => Seq(OpenBracket, b, CloseBracket);
    private static Formula Promote(Formula p) => C("promote", p);
    private static Formula Split(Formula p) => C("split", p);
    private static Formula Shift(Formula c, Formula p) => C("shift", c, p);
    private static Formula Cut(Formula b, Formula t, Formula i) => C("cutTerm", b, t, i);
    private static Formula Events(Formula b, Formula t) => C("events", b, t);
    private static Formula Event(Formula b, Formula t) => C("Event", b, t);
    private static Formula Born(Formula b, Formula t) => C("Born", b, t);
    private static Formula Ideal(Formula b, Formula t, Formula i) => C("Ideal", b, t, i);
    private static Formula Erase(Formula l) => C("erase", l);
    private static Formula Run(Formula t, Formula w) => C("run", t, w);
    private static Formula Some(Formula t) => C("some", t);
    private static Formula AlphaLeaf => C("of", C("true"));
    private static Formula Extension(Formula l) => C("ExtensionList", Emptyset, C("univ"), l);

    private static Formula Statement(string name)
    {
        var b = V("b"); var c = V("c"); var d = V("d"); var e = V("e");
        var f = V("f"); var t = V("t"); var p = V("p"); var v = V("v");
        var i = V("I"); var l = V("l"); var r = V("r"); var w = V("w");
        var k = V("K"); var j = V("J");
        var cut = Cut(b, t, i);
        var subtree = Eqn(C("subtree", p, t), Some(v));
        var noSplit = Bind(["l", "r"], [Source, Source],
            Im(Eqn(v, C("mul", l, r)), Not(Mem(Split(p), i))));
        return name switch
        {
            "root_before" => Bind(["b", "c"], [Bool, Call],
                Rel(Split(Nil), Lt, Shift(c, One(b)))),
            "shift_lt" => Bind(["b", "c", "d"], [Bool, Call, Call],
                Iffn(Rel(Shift(c, One(b)), Lt, Shift(d, One(b))), Rel(c, Lt, d))),
            "lt_promote_root" => Q("c", Call, Not(Rel(c, Lt, Promote(Nil)))),
            "lt_split_root" => Q("c", Call,
                Iffn(Rel(c, Lt, Split(Nil)), Eqn(c, Promote(Nil)))),
            "lt_shift" => Bind(["b", "c", "d"], [Bool, Call, Call],
                Iffn(Rel(d, Lt, Shift(c, One(b))), Or(Eqn(d, Promote(Nil)),
                    Or(Eqn(d, Split(Nil)), Ex("f", Call,
                        And(Eqn(d, Shift(f, One(b))), Rel(f, Lt, c))))))),
            "shift_mem" => Bind(["b", "c", "l", "r", "e"],
                [Bool, Bool, Source, Source, Call],
                Iffn(Mem(Shift(e, One(c)), Events(b, C("mul", l, r))),
                    Mem(e, Events(c, C("ite", c, r, l))))),
            "subtree_partial" => Bind(["t", "p", "v"], [Source, C("Address"), Source],
                Im(subtree, Bind(["b", "I"], [Bool, Set(Call)],
                    Eqn(C("subtree", p, cut), C("ite", C("Created", i, p),
                        Some(Cut(C("birthAt", b, p), v, C("sectionAt", i, p))), C("none")))))),
            "guard_ancestor" => new Formula.Aligned([
                Seq(Amp, BindFlat(["t", "p", "v"], [Source, C("Address"), Source],
                    Seq(P(subtree), Sp, Rightarrow, Sp, Open))),
                Seq(Amp, P(Rel(v, Neq, AlphaLeaf)), Sp, Rightarrow, Sp, Open,
                    BindFlat(["b", "I"], [Bool, Set(Call)], Open)),
                Seq(Amp, P(Iffn(C("Guard", Promote(p), cut),
                    Ands(C("Created", i, p), Eqn(C("birthAt", b, p), C("true")),
                        Not(Mem(Promote(p), i)), noSplit)))),
                Seq(Amp, Land, Sp, P(Iffn(C("Guard", Split(p), cut),
                    Ands(C("Created", i, p),
                        Or(Eqn(C("birthAt", b, p), C("false")), Mem(Promote(p), i)),
                        noSplit))), Close, Close, Close)]),
            "partial_empty" => Bind(["b", "t"], [Bool, Source],
                Im(Born(b, t), Eqn(Cut(b, t, Emptyset), C("of", b)))),
            "partial_insert" => Bind(["b", "t", "I"], [Bool, Source, Set(Call)],
                Im(Born(b, t), Im(Ideal(b, t, i), Q("e", Call, Im(Mem(e, Events(b, t)),
                    Im(C("Guard", e, cut), Eqn(C("edited", cut, e),
                        Cut(b, t, C("insert", e, i))))))))),
            "guard_enabled" => Bind(["b", "t", "I"], [Bool, Source, Set(Call)],
                Im(Born(b, t), Im(Ideal(b, t, i), Q("e", Call, Im(Mem(e, Events(b, t)),
                    Iffn(C("Guard", e, cut), C("Enabled", b, t, i, e))))))),
            "cut_events" => Bind(["b", "t", "I"], [Bool, Source, Set(Call)],
                Im(Born(b, t), Im(Ideal(b, t, i), Eqn(Events(b, cut), i)))),
            "cut_full" => Bind(["b", "t"], [Bool, Source],
                Im(Born(b, t), Eqn(Cut(b, t, Events(b, t)), t))),
            "execution_adequacy" => new Formula.Aligned([
                Seq(Amp, BindFlat(["b", "t"], [Bool, Source],
                    Seq(P(Born(b, t)), Sp, Rightarrow, Sp, Open))),
                Seq(Amp, BindFlat(["K", "J"], [Set(Event(b, t)), Set(Event(b, t))],
                    Seq(P(C("IsLowerSet", k)), Sp, Rightarrow, Sp, Open,
                        P(C("IsLowerSet", j)), Sp, Rightarrow, Sp, Open))),
                Seq(Amp, Q("l", List(Event(b, t)),
                    Iffn(C("Exec", k, l, j),
                        Eqn(Run(Cut(b, t, C("raw", b, t, k)), Erase(l)),
                            Some(Cut(b, t, C("raw", b, t, j)))))), Close, Close, Close)]),
            "linear_extension_histories" => Q("t", Source, Im(C("D", t),
                Q("l", List(Event(C("true"), t)),
                    Iffn(Eqn(Run(AlphaLeaf, Erase(l)), Some(t)), Extension(l))))),
            "all_histories" => Q("t", Source, Im(C("D", t), Q("w", List(Call),
                Iffn(Eqn(Run(AlphaLeaf, w), Some(t)),
                    Ex("l", List(Event(C("true"), t)), And(Eqn(Erase(l), w), Extension(l))))))),
            _ => throw new System.ArgumentOutOfRangeException(nameof(name))
        };
    }
}
