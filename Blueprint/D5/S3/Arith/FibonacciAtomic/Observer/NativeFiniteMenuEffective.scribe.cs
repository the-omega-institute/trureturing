using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer;
internal sealed class NativeFiniteMenuEffectiveDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Observer/NativeFiniteMenuEffective.";

    private static Formula V(string n) => F.Id(n);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Call(string n, params Formula[] a) => new Formula.Apply(Seq(Operatorname, Grp(V(n))), [.. a]);
    private static Formula EqOf(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula And(params Formula[] a) => Seq(a.Select((f,i) => i == 0 ? Par(f) : Seq(Sp, Land, Sp, Par(f))).ToArray());
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));
    private static Formula Less(Formula a, Formula b) => Seq(a, Sp, Lt, Sp, b);
    private static Formula Mem(Formula a, Formula b) => Seq(a, Sp, InMacro, Sp, b);
    private static Formula All(string ns, Formula t, Formula b) => Seq(Forall, Sp, Seq(ns.Split(',').Select((n,i) => i == 0 ? V(n) : Seq(Comma,Sp,V(n))).ToArray()), Colon, Sp, t, Comma, Sp, Par(b));
    private static Formula Rank(Formula s, Formula u) => Call("code", s, u);
    private static Formula Len(Formula a) => Call("length", a);

    private static Formula Le(Formula a, Formula b) => Seq(a, Sp, Leq, Sp, b);
    private static Formula IffOf(Formula a, Formula b) => Seq(Par(a), Sp, Iff, Sp, Par(b));
    private static Formula ExistsOne(string n, Formula t, Formula b) =>
        Seq(Exists, Sp, V(n), Colon, Sp, t, Comma, Sp, Par(b));

    private static Formula Statement()
    {
        var d = V("D"); var s = V("S"); var xs = V("xs");
        var u = V("u"); var v = V("v"); var t = V("t"); var k = V("k");
        Formula Init(Formula x) => Call("initial", s, x);
        Formula Fut(Formula x) => Call("future", s, x, k);
        Formula Restore(Formula x) => Call("restore", d, s, x);
        Formula Raw(Formula x) => Call("rawDecode", d, s, x, k);
        var defaultVector = Call("replicate", Len(s), V("absent"));
        var correct = All("u", V("Source"), All("k", V("Nat"),
            EqOf(Call("decode", d, s, Init(u), k), Fut(u))));
        var invalid = All("xs", Call("List", V("Nat")), All("k", V("Nat"),
            Imp(EqOf(Call("rawValid", s, xs), V("false")), EqOf(Raw(xs), defaultVector))));
        var inconsistent = All("xs", Call("List", V("Nat")), All("k", V("Nat"),
            Imp(EqOf(Restore(Call("map", V("rawReply"), xs)), V("none")),
                EqOf(Raw(xs), defaultVector))));
        var rawCorrect = All("u", V("Source"), All("k", V("Nat"),
            EqOf(Raw(Call("rawVector", s, u)), Fut(u))));
        var ranks = All("u,v", V("Source"),
            Imp(EqOf(Init(u), Init(v)), EqOf(Rank(s, u), Rank(s, v))));
        var sound = All("xs", Call("List", V("Reply")), All("t", V("Source"),
            Imp(EqOf(Restore(xs), Call("some", t)),
                And(Le(Call("height", t), d), EqOf(Init(t), xs)))));
        var rejected = All("xs", Call("List", V("Reply")),
            IffOf(EqOf(Restore(xs), V("none")),
                Seq(Neg, Sp, Par(ExistsOne("u", V("Source"), EqOf(Init(u), xs))))));
        var result = And(Call("ComputableTwo", Call("decode", d, s)), correct,
            Call("PrimrecTwo", Call("rawDecode", d, s)),
            Call("ComputableTwo", Call("rawDecode", d, s)), invalid,
            inconsistent, rawCorrect, ranks, sound, rejected);
        var depth = All("q", V("Address"), Imp(Mem(V("q"), s), Less(Len(V("q")), d)));
        return All("D", V("Nat"), All("S", V("Menu"),
            Imp(And(Call("PrefixClosed", s), depth), result)));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Total computable fixed-menu prediction", H("Total computable fixed-menu prediction"), Blocks(
            Paragraph(Text("For each fixed public D and ordered menu S, the finite input type Fin(length(S))->Reply has a primitive-recursive reconstruction table. Its entries are computed by reconstruct, not by an assumed decoder or an assumed normal-form semantics. Lookup uses the first occurrence of an address in the public order, and never sorts the menu.")),
            Paragraph(Text("Restore rejects wrong tuple lengths, inconsistent repeated coordinates and constructor inconsistency as none. Decode returns the fixed all-absent vector after rejection; after success it applies genuine native substitution and four-valued readout to the reconstructed representative. Raw input is an arbitrary list of natural numbers. RawValid requires the correct length and every symbol below four, with alpha,beta,branch,absent represented by 0,1,2,3.")),
            Paragraph(Text("The total functions cover malformed and inconsistent represented inputs. The table is primitive recursive because its domain is finite for this fixed public menu. Unbounded natural iteration and exact readout reuse their existing primitive-recursive implementations. This proves computability, not a time, bit, energy, physical memory or native Read cost bound.")),
            Paragraph(Text("Fix D>=1 and an ordered public menu P in A_D: every literal is Rq with length(q)+1<=D. RelativeMenu removes this first R at every list position, and PublicMenu restores it. Empty, epsilon-containing and nested relative menus all remain in scope. Source is the exact native FreeMagma Bool carrier; no positive-source, right-only-path or restricted-epoch promise is used.")),
            Paragraph(Text("InitialSufficient means there exists one function from the initial reply list and the supplied natural count to a reply list, correct for every v with original height(v)<=D and every count k. EffectiveSufficient adds total ComputableTwo evidence for that same represented function domain. CodeSufficient means that equality of the whole initial vectors of any two such v implies equality of the exact original FM.17 numerical ranks.")),
            Paragraph(Text("These three clauses are equivalent to relative prefix closure. Sufficiency reconstructs an actual representative from the root reply and recursive child blocks; the total computable decoder evaluates its future trajectory. Necessity uses every prescribed missing-prefix pair, which jointly supplies equal initial vectors, unequal original codes and a common legal future distinction. Each selected vector retains the original public order.")),
            Paragraph(Text("The D=1 case allows only epsilon as a relative address, so every admissible menu is prefix-closed. For an empty menu reconstruction returns alpha, the original rank is zero and every future output is empty. Relabeling by the initial R is valid at every count and for blocked suffixes. The four-way statement asserts value prediction under a supplied same-source count; it makes no acquisition, authentication, runtime or physical-efficiency claim.")),
            Paragraph(Text("The four-way criterion follows from the reconstruction theorem and every_missing_prefix_obstruction. Prefix closure gives the total computable decoder and equality of original ranks; a total computable decoder is a function. If a prefix is missing, the prescribed same pair contradicts both functional prediction and rank determination. Thus each of the three conditions is equivalent to prefix closure, with no normal-form semantics premise. This application retains the full original height family and all natural counts.")),
            Describe.Lean(DescribeId.Create("total-native-menu-decoder"),
                DeclarationHandle.Create(Prefix + "total_native_menu_decoder"),
                H("Totality, rejection and all attained vectors"),
                StatementSource.FromAuthor(Disp(Statement())), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every attained vector reconstructs one actual representative with its original code and entire future trajectory. Induction on reconstruction fuel shows that acceptance realizes every selected coordinate and bounds the returned tree height. Tuple coherence also checks repeated coordinates. Every realizable list is accepted under prefix closure, so rejection is exactly nonexistence of a realizing source. Equal attained initial lists yield the same representative and hence equal original ranks. The guarantee ranges over all finite actual sources and therefore over the full original height family."))),
                DescribeRole.Theorem))));
}
