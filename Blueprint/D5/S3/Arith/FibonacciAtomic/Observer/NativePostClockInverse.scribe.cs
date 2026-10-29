using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer;

internal sealed class NativePostClockInverseDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact rational post-clock fields recover every finite legal native addressed word.",
        H("Native post-clock inverse"), Blocks(
            Paragraph(Text("Source is the original Boolean free magma: true is alpha and false is beta. Material coordinates include each beta's separate left marker. The original guarded Call runner promotes alpha at p or splits beta at p into the literal branch (beta,alpha). Promotion adds only pL. Splitting retains the old pL and adds only pLL and pR. The current endpoint consists of the term and a rational function on its explicitly listed finite material support.")),
            Paragraph(Text("For positive rational a and c, clock(a,c,t) is a times the identity plus c times the unit native material adjacency. Its determinant is assumed nonzero on every actual term reached by a finite legal word. Encoding starts at the earned alpha field 1, and each successful letter performs actual zero inclusion followed by Tick on the new term. Replay is partial exactly through the original logical guard; no Reset, Add or extra Tick appears in this recurrence.")),
            Describe.Lean(
                DescribeId.Create("nativepostclockinverse"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Observer/NativePostClockInverse.postclock_inverse"),
                H("Complete reached-image inverse"), StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For every finite successful addressed word, including the empty word, encoding exists on its actual final term and every material coordinate is strictly positive. Decode of that endpoint returns exactly that word. Decode followed by replay returns the input endpoint on the reached image, and equal encoded endpoints force equal words. At every further enabled event, the local predecessor returns exactly the original endpoint and event; its material size is strictly smaller.")),
                    Paragraph(Text("Untick computes the rational reciprocal of the finite determinant times the adjugate, then multiplies the full finite field. It uses finite rational arithmetic. The zeros after Untick are exactly the last fresh support: a singleton pL for promotion or the pair pLL,pR for splitting. These signatures distinguish both the kind and the address. The current local subtree is tested against the literal replacement before selection. Collapse replaces beta by alpha or (beta,alpha) by beta and restricts the unticked field, retaining all old coordinates. Each fresh coordinate has an old neighbor, so the positive edge coefficient makes it positive after Tick; at old coordinates the positive diagonal suffices.")),
                    Paragraph(Text("DecodeFuel uses the current material size as fuel. Each actual reverse step strictly reduces that size, and the empty origin returns the empty list. The runtime inputs are only the current native term, its full finite rational field, and a,c. Histories occur in correctness proofs and are absent from predecessor selection and decoder inputs. There is no off-image recognition assertion. The pre-clock construction and the common-source inverse outside this reached image are separate questions."))),
                DescribeRole.Theorem))));

    private static Formula V(string s) => F.Id(s);
    private static Formula P(Formula x) => Seq(Open, x, Close);
    private static Formula C(string s, params Formula[] xs) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(s))), [.. xs]);
    private static Formula Q(string n, Formula t, Formula f) =>
        Seq(Forall, Sp, V(n), Colon, Sp, t, Comma, Sp, P(f));
    private static Formula Ex(string n, Formula t, Formula f) =>
        Seq(Exists, Sp, V(n), Colon, Sp, t, Comma, Sp, P(f));
    private static Formula Eqn(Formula x, Formula y) => Seq(x, Sp, F.Eq, Sp, y);
    private static Formula A(Formula x, Formula y) => Seq(P(x), Sp, Land, Sp, P(y));
    private static Formula Im(Formula x, Formula y) => Seq(P(x), Sp, Rightarrow, Sp, P(y));
    private static Formula Lt(Formula x, Formula y) => Seq(x, Sp, F.Lt, Sp, y);
    private static Formula All(string[] ns, Formula[] ts, Formula f)
    {
        for (int i = ns.Length - 1; i >= 0; --i) f = Q(ns[i], ts[i], f);
        return f;
    }
    private static Formula Ands(params Formula[] fs)
    {
        var f = fs[^1];
        for (int i = fs.Length - 2; i >= 0; --i) f = A(fs[i], f);
        return f;
    }
    private static Formula Source => C("Source");
    private static Formula Word => C("List", C("Call"));
    private static Formula Endpoint => C("Endpoint");
    private static Formula Rational => Seq(Mathbb, Grp(V("Q")));
    private static Formula Some(Formula x) => C("some", x);
    private static Formula Statement()
    {
        var a = V("a"); var c = V("c"); var w = V("w"); var v = V("v");
        var t = V("t"); var e = V("e"); var x = V("x"); var g = V("g"); var q = V("q");
        Formula Enc(Formula word) => C("encode", a, c, word);
        Formula Dec(Formula endpoint) => C("decode", a, c, endpoint);
        var tx = C("endpoint", t, x);
        var law = All(["v", "t"], [Word, Source],
            Im(Eqn(C("run", C("alpha"), v), Some(t)),
                Seq(C("det", C("clock", a, c, t)), Sp, Neq, Sp, D(0))));
        var legal = All(["w", "t"], [Word, Source],
            Im(Eqn(C("run", C("alpha"), w), Some(t)),
                Ex("x", C("Field", t), Ands(Eqn(Enc(w), Some(tx)), Eqn(Dec(tx), Some(w)),
                    Q("q", C("Coordinate", t), Lt(D(0), C("apply", x, q)))))));
        var left = All(["w", "e"], [Word, Endpoint],
            Im(Eqn(Enc(w), Some(e)), Eqn(Dec(e), Some(w))));
        var right = Q("e", Endpoint,
            Im(Ex("w", Word, Eqn(Enc(w), Some(e))),
                Eqn(C("bind", Dec(e), C("encode", a, c)), Some(e))));
        var inj = All(["w", "v", "e"], [Word, Word, Endpoint],
            Im(Eqn(Enc(w), Some(e)), Im(Eqn(Enc(v), Some(e)), Eqn(w, v))));
        var enabled = Eqn(C("subtree", C("address", g), C("term", e)),
            Some(C("of", C("kind", g))));
        var local = All(["w", "e", "g"], [Word, Endpoint, C("Call")],
            Im(Eqn(Enc(w), Some(e)), Im(enabled, A(
                Eqn(C("predecessor", a, c, C("appendEndpoint", a, c, e, g)), Some(C("pair", e, g))),
                Lt(C("length", C("material", C("term", e))),
                    C("length", C("material", C("edited", C("term", e), g))))))));
        return All(["a", "c"], [Rational, Rational],
            Im(Lt(D(0), a), Im(Lt(D(0), c), Im(law, Ands(legal, left, right, inj, local)))));
    }
}
