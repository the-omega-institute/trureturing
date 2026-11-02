using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Geometry;

internal sealed class NativePromiseCausalBoundaryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every all-assignment promised comb has native causal histories and distinct legal serial orders.",
        H("Native promise causal boundary"), Blocks(
        Paragraph(Text("C is the original ActualImageSevenLeafSeparation.E=(beta,alpha). D0 is the original FourExitRawEndpointSpectrum.z=(beta,C), and D1 is ActualImageSevenLeafSeparation.A=(C,beta). The marker is ((C,alpha),alpha), using NativeFreshSensorGrowth.cone false. promise N z is the unchanged right comb with 15N slots and that marker. Every assignment z from Fin(15N) to Bool is included; no sampled-support, group, sampler, controller or independence premise restricts the family.")),
        Paragraph(Text("Original Lean suppliers: "),
            Ref("D5/S3/Arith/FibonacciAtomic/ActualImageSevenLeafSeparation"), Text(" (E and A); "),
            Ref("D5/S3/Arith/FibonacciAtomic/FourExitRawEndpointSpectrum"), Text(" (z and comb); "),
            Ref("D5/S3/Arith/FibonacciAtomic/Geometry/NativeFreshSensorGrowth"), Text(" (cone and original run_append); "),
            Ref("D5/S3/Arith/FibonacciAtomic/Geometry/NativeGuardedLeafRepair"), Text(" (original context_run and D_mul).")),
        Paragraph(Text("Mathematical definitions. Bool = {false,true}; Source is the original free ordered binary-tree algebra, with of : Bool → Source and mul : Source × Source → Source; alpha = of(true), beta = of(false). For b : Bool, slot(b) is mul(C,beta) if b = true and mul(beta,C) otherwise, where C = mul(beta,alpha). The marker is mul(mul(C,alpha),alpha). For m : Source and the unique f : Fin(0) → Source, comb(0,f,m) = m. For k : Nat, f : Fin(k+1) → Source and m : Source, comb(k+1,f,m) = mul(f(0),comb(k,(i ↦ f(i+1)),m)), where i ranges over Fin(k). Thus for N : Nat and z : Fin(15N) → Bool, promise(N,z) = comb(15N,(i ↦ slot(z(i))),marker). Fin(k) = {i : Nat | i < k}, including the empty type at k = 0.")),
        Paragraph(Text("The native predicates and operations D, run, Event, erase, some, univ and the strict event order are defined in "), Ref("D5/S3/Arith/FibonacciAtomic/Geometry/NativeEndpointEventIdeals"), Text(". D is the original no-left-alpha domain; run is the guarded original Call-word computation, some is successful Option output, and Event(true,t) is the full endpoint-event subtype with its induced prefix/phase order. erase maps every subtype element to its original Call without changing the list. ExtensionList(empty,univ,l) says that l lists each such event exactly once in an order with no later event below an earlier event. List(Call) contains all finite raw Call words, and ++ is concatenation. The exact recursively defined Edge and its nonreflexive finite-path closure TransGen are defined in "), Ref("D5/S3/Arith/FibonacciAtomic/Geometry/NativeEndpointCausalOrder"), Text("; val forgets only event membership proofs. Every type and operation below has the same meaning as in those two native modules.")),
        Describe.Lean(DescribeId.Create("native-promise-causal-boundary"),
            DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Geometry/NativePromiseCausalBoundary.result"),
            H("All promised assignments and the causal versus serial boundary"),
            StatementSource.FromAuthor(Statement()), AssessedProvenance.FromRepo(), Blocks(
            Paragraph(Text("For every natural N at least four and every assignment z, the actual promised endpoint is in D. For every raw Call word, native success from alpha to that endpoint is equivalent to a lift to an exact labelled linear extension of its endpoint order. Every prefix of every successful word is itself a successful actual run to an intermediate source. The endpoint order is proved equal to the transitive closure of the exact local and creating-split edges. There also exist two different raw words that both succeed to this same endpoint.")),
            Paragraph(Text("The proof first verifies the original D predicate structurally on every gadget and comb. NativeEndpointEventIdeals.all_histories then gives the full raw-history characterization. Existence of a finite enabled execution is transported to an actual native run only through the proved execution_adequacy, partial_empty and cut_full; no source-specific adequacy is assumed.")),
            Paragraph(Text("For serial ambiguity, prepare a reachable comb whose first two slots are C. The zero slot insertion is promote-right then split-right; the one slot insertion is split-left then promote-right. Each is a literal two-call successful original run. Original context_run shifts these insertions into the disjoint first and second slots. Original run_append composes them in either order, producing distinct words with the same endpoint; prepending the common preparation preserves their inequality. Thus the bare endpoint supplies labelled causal information, while selecting a serial extension requires additional recipe-order data.")),
            Paragraph(Text("This is the native structural prerequisite for Unified Joint Law Bridge 5.3 and 5.6. It does not close those compound propositions, the generation-grade arithmetic, Section 3/4 actual group and partition laws, complete bounded adaptive controller measurability, the exact eight-event signed law, or common full-tree submass. No theorem about unconditional adaptive independence or recovery of a serial clock from a bare endpoint is asserted."))),
            DescribeRole.Theorem))));

    private static Formula V(string name) => F.Id(name);
    private static Formula P(Formula f) => Seq(Open, f, Close);
    private static Formula C(string name, params Formula[] args) =>
        args.Length == 0 ? Seq(Operatorname, Grp(V(name)))
            : new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula Q(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, P(body));
    private static Formula Ex(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, V(name), Colon, Sp, type, Comma, Sp, P(body));
    private static Formula Rel(Formula x, Formula op, Formula y) => Seq(x, Sp, op, Sp, y);
    private static Formula Eqn(Formula x, Formula y) => Rel(x, F.Eq, y);
    private static Formula And(Formula x, Formula y) => Rel(P(x), Land, P(y));
    private static Formula Im(Formula x, Formula y) => Rel(P(x), Rightarrow, P(y));
    private static Formula Iffn(Formula x, Formula y) => Rel(P(x), Iff, P(y));
    private static Formula Statement()
    {
        var n = V("N"); var z = V("z"); var w = V("w"); var l = V("l");
        var p = V("p"); var q = V("q"); var u = V("u"); var c = V("c");
        var d = V("d"); var v = V("v");
        var nat = Seq(Mathbb, Grp(V("N")));
        var target = C("promise", n, z);
        var events = C("Event", C("true"), target);
        var words = C("List", C("Call"));
        var alpha = C("of", C("true"));
        var endpoint = C("some", target);
        var history = Q("w", words, Iffn(Eqn(C("run", alpha, w), endpoint),
            Ex("l", C("List", events), And(Eqn(C("erase", l), w),
                C("ExtensionList", Emptyset, C("univ"), l)))));
        var prefixes = Q("p", words, Q("q", words,
            Im(Eqn(C("run", alpha, Rel(p, Seq(Plus, Plus), q)), endpoint),
                Ex("u", C("Source"), Eqn(C("run", alpha, p), C("some", u))))));
        var causal = Q("c", events, Q("d", events,
            Iffn(C("TransGen", C("Edge", C("true"), target), C("val", c), C("val", d)),
                Rel(c, Lt, d))));
        var distinct = Ex("w", words, Ex("v", words,
            And(Rel(w, Neq, v), And(Eqn(C("run", alpha, w), endpoint),
                Eqn(C("run", alpha, v), endpoint)))));
        var conclusion = new Formula.Aligned([
            Seq(Amp, C("D", target)),
            Seq(Amp, Land, Sp, P(history)),
            Seq(Amp, Land, Sp, P(prefixes)),
            Seq(Amp, Land, Sp, P(causal)),
            Seq(Amp, Land, Sp, P(distinct))]);
        return Q("N", nat, Im(Rel(D(4), Leq, n),
            Q("z", Rel(C("Fin", Rel(D(1, 5), Cdot, n)), To, C("Bool")), conclusion)));
    }
}
