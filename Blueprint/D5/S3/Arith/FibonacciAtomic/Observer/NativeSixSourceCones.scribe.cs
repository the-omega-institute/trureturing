using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer;
internal sealed class NativeSixSourceConesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Observer/NativeSixSourceCones.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Six simultaneous actual finite origins have five complete predecessor rows, while every literal native address respects its exact occurrence cone.",
        H("Six Actual Repeated-Partner Sources"), Blocks(
            Paragraph(Text("Sources are the original finite ordered Boolean trees. False is beta and true is alpha. The substitution sends alpha to beta and beta to the ordered pair (beta,alpha), preserving ordered brackets. Addresses are all finite Boolean lists, with false meaning left. The native replies are alpha, beta, branch and absent. The cut P consists of all eight depth-three addresses, in lexicographic order. Their classes are a,b1,a,b2,c,b3,c,b4. Canonical class names are the first occurrence ordinals 0,1,0,3,4,5,4,7; different classes retain every disequality.")),
            Paragraph(Text("The six source indices 0,1,2,3,4,5 denote 0a,0c,1,2,3,4 respectively. The target label is zero at the first two indices and j at index j+1. Group A consists of indices 0,2,3. The original orbit is T0=alpha and T(n+1)=rho(Tn). The fixed branch images are A=T2, C=T3 and Dj=T(j+3). In group A the a coordinate is beta and c is C; in the other group a is A and c is beta. The right coordinate bj is alpha at index j+1 and Dj elsewhere. Filling uses the same a coordinate at LLL and LRL and the same c coordinate at RLL and RRL.")),
            Entry("prefix_free", "The Complete Cut Is Prefix Free", Call("CutPrefixFree", V("P")),
                "For any finite addresses a and b in P, if a is a prefix of b then a=b. Every member of P is one of the eight listed positions and has length three. A prefix between equal-length lists is equality. This property lets canonical row naming and class-value recovery use the same literal cut: the recovered coordinate profile and its native-read and predecessor-row identities apply to every origin in the entire fiber."),
            Entry("six_source_realization", "Simultaneous Actual Realization", All("z", Call("Fin", D(6)), And(
                EqOf(Call("rho", Call("origin", V("z"))), Call("current", V("z"))),
                EqOf(Call("canonicalRow", V("P"), Call("current", V("z"))), V("row")),
                EqOf(Call("canonicalRow", V("P"), Call("origin", V("z"))), Call("predecessor", Call("label", V("z")))))),
                "The theorem additionally asserts injectivity of predecessor on Fin 5. Each origin is an actual finite inverse of its fixed current tree. Its entire canonical current row equals row, so it belongs to the full infinite OriginFiber(P,row). Predecessor zero is the current row. At positive j the pair at qj is replaced by one concrete beta, while the other six occurrences retain their restricted partition with recomputed first occurrence names. The surviving repeated partner remains a hole. These are complete LiteralRow outputs, including their exterior, equality, disequality and absence information."),
            Entry("occurrence_read", "Every Literal Occurrence and Suffix", All("p", Call("Fin", D(8)), All("w", V("Address"), All("z", Call("Fin", D(6)), EqOf(
                Call("readout", Call("append", Call("position", V("p")), V("w")), Call("current", V("z"))),
                Call("readout", V("w"), Call("values", V("z"), Call("occurrenceClass", V("p")))))))),
                "The suffix is any finite address. It can be empty, continue past a leaf or leave the finite subtree. Absence is the ordinary native reply. Both occurrences of each repeated partner are included, but each address enters one occurrence cone."),
            Entry("all_address_factor", "Exact All-Address Restriction", All("a", V("Address"), Some("f", Fn(V("Bool"), V("Reply")), All("z", Call("Fin", D(6)), EqOf(
                Call("readout", V("a"), Call("current", V("z"))), Call("f", Call("question", V("a"), V("z"))))))),
                "Location is determined by the first three literal address edges. Shorter addresses are common skeleton branches. Partner cones use the group-A bit, and the four right cones use their respective positive-singleton bit. Thus the actual replies are either constant or induce the stated group or singleton partition, depending on whether f has equal or distinct values. Question is only a mathematical factor of the original native readout; the controller receives no extra query port. The claim concerns these six simultaneous sources and does not make the full infinite fiber binary. Acquisition, authentication, export, lawful entry and isolation from discarded fields remain supplied conditions. No inverse service or physical resource bound follows."))));
    private static DocumentBlock Entry(string n, string h, Formula f, string p) => Describe.Lean(
        DescribeId.Create("nativesixsourcecones-" + n.Replace("_", "-")), DeclarationHandle.Create(Prefix + n), H(h),
        StatementSource.FromAuthor(Disp(n == "six_source_realization" ? And(f,Call("Injective",V("predecessor"))) : f)),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(p))), DescribeRole.Theorem);
    private static Formula V(string s) => F.Id(s);
    private static Formula Par(Formula f) => Seq(Open,f,Close);
    private static Formula Call(string n, params Formula[] a) => new Formula.Apply(Seq(Operatorname,Grp(V(n))),[..a]);
    private static Formula Fn(Formula a, Formula b) => Seq(Par(a),Sp,To,Sp,Par(b));
    private static Formula EqOf(Formula a,Formula b) => Seq(a,Sp,Eq,Sp,b);
    private static Formula And(params Formula[] fs) => Seq(fs.Select((f,i)=>i==0?Par(f):Seq(Sp,Land,Sp,Par(f))).ToArray());
    private static Formula All(string n,Formula t,Formula b) => Seq(Forall,Sp,V(n),Colon,Sp,t,Comma,Sp,Par(b));
    private static Formula Some(string n,Formula t,Formula b) => Seq(Exists,Sp,V(n),Colon,Sp,t,Comma,Sp,Par(b));
}
