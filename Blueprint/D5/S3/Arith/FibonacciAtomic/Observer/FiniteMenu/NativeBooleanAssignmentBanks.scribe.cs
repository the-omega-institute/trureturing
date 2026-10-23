using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu;
internal sealed class NativeBooleanAssignmentBanksDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Observer/FiniteMenu/NativeBooleanAssignmentBanks.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Exact lexicographic Boolean banks on the unrestricted native origin fiber.",
        H("Boolean Assignment Banks and Both Whole Predecessor Rows"), Blocks(
            Paragraph(Text("Source is the actual finite ordered FreeMagma Bool: alpha is of(true), beta is of(false), and pair is its binary constructor. Substitution rho sends alpha to beta and beta to pair(beta,alpha), and preserves pairs. Addresses use false=L and true=R, ordered lexicographically with L before R. Height counts edges from a leaf of height zero. The size function is the length of PreorderTreeEvaluation.word, hence counts every constructor occurrence, including every occurrence of a repeated subtree. No DAG sharing is used in these bounds.")),
            Paragraph(Text("Put ell(n)=Nat.clog 2 (max 2 n). The list words(d) sorts the entire image of frontierAddress(fullPattern(d)) in the ordinary address order; it contains exactly all length-d words without repetitions. selected(n)=take(n,words(ell(n))). The zero-based variableWord(n,i) is selected(n)[i]; it represents source variable i+1. The fixed literal is RLL concatenated with this exact word. There is no arbitrary finite-equivalence enumeration. The bounds are 0<ell(n), n<=2^ell(n)<=4(n+1), and ell(n)<=n+1.")),
            Definition("LiteralSpec", "Literal Data and Polynomial Length", LiteralStatement(),
                "LiteralSpec records the sorted complete word list, the exact selected prefix, distinct words, every literal length and the total length bound. PairwiseLe means the list is pairwise ordered by the ordinary non-strict lexicographic relation. literalLengths(n) is List.ofFn(i ↦ length(literal(n,i)))."),
            Definition("AllSources", "Total Interpretation on Every Source", AllSourceStatement(),
                "assignment(n,u,i)=branchBit(readout(literal(n,i),rho(u))). branchBit is true precisely for branch. Its values on alpha, beta and absent are false. The quantifier over Source has no resource, profile or Boolean-witness premise and therefore applies to the entire actual Fiber. Equal stationary literals have equal readings, including repeated syntactic occurrences."),
            Paragraph(Text("B(j)=NativeClassRootPadding.pad(j,beta), so B(0)=beta and B(j+1)=pair(B(j),B(j)). payload(b,a) is B(1) when some selected variable word equals a and its bit is true, and is beta otherwise. bank(b) is exactly fill(fullPattern(ell(n)),j ↦ payload(b,frontierAddress(j))). Every selected false slot and every unused slot is beta; a true slot is the whole pair(beta,beta). This payload identity is stronger than a root branch reply.")),
            Definition("BankSpec", "The Entire Prescribed Bank", BankStatement(),
                "fullFillPayload(d,b) abbreviates fill(fullPattern(d),j ↦ payload(b,frontierAddress(j))). Image(C) means an actual finite preimage under rho exists. The bank is a branch image for every n and b. Its height is at most ell(n)+1 and its ordinary size plus one is at most 16(n+1). The universal frontier assertion includes unselected positions."),
            Paragraph(Text("The source D order is (a,c,bone,btwo,bthree,bfour). Native order is (a,bone,btwo,c,bthree,bfour). dToNative=[0,3,1,2,4,5] and nativeToD=[0,2,3,1,4,5] are inverse permutations; the native canonical first-occurrence names are [0,1,3,4,5,7]. The existing filling operation is pair(pair(pair(a,bone),pair(a,btwo)),pair(pair(c,bthree),pair(c,bfour))). Thus a and c each occur twice as the same whole subtree.")),
            Paragraph(Text("For second=false, tuple(n,C,second) in native order is [beta,alpha,B(ell(n)+2),C,B(ell(n)+3),B(ell(n)+4)]; for second=true the second and third entries are exchanged. targetIndex is respectively 1 and 2. The bank has positive height at most ell(n)+1, both leaves have height zero and different labels, and the three marker heights are ell(n)+2, ell(n)+3 and ell(n)+4. Injectivity of this six-entry function is exactly all fifteen whole-value inequalities.")),
            Definition("WitnessSpec", "Actual Origins and Complete Target Rows", WitnessStatement(),
                "Fiber is NativeClassRootImage.OriginFiber(P,row): every finite u with canonicalRow(P,rho(u))=row. P consists of all eight length-three cut addresses. row is the complete repeated-partner current row. A witness has that exact current tree, the required entire predecessor row, the prescribed assignment and literal subtrees, and bounds for both the current tree and its actual origin."),
            Paragraph(Text("The whole Rone row is pair(pair(beta,pair(hole(0),hole(1))),pair(pair(hole(2),hole(3)),pair(hole(2),hole(5)))). The whole Rtwo row is pair(pair(pair(hole(0),hole(1)),beta),pair(pair(hole(2),hole(3)),pair(hole(2),hole(5)))). These are predecessor(1) and predecessor(2), with concrete blocking beta leaves and surviving occurrences in canonical first-member order. They are not merely acquired labels. The original legal-values row theorem gives the current row, and native_full_root_feasibility, finite_root_minimax and type_finite_row give these complete predecessor rows on the actual origin.")),
            Paragraph(Text("The inverse bank replaces each beta frontier payload by alpha and each pair(beta,beta) payload by pair(alpha,alpha), preserving the full skeleton. Homomorphic transport proves its image is the required bank. In the first origin the exceptional leftmost depth-two pair is the concrete beta leaf; in the second origin it is the next pair. Both right-side occurrences use the one inverse bank value. Marker preimages are pad(j,alpha). Thus the inverse is explicit on this family and is compatible with the original unique native inverse, without assuming an independent realization bridge.")),
            Paragraph(Text("For an arbitrary frontier function f with height(f(j))<=H and size(f(j))<=M, induction on the complete skeleton proves height(fill(d,f))<=d+H and size(fill(d,f))+1<=2^d(M+1). This includes d=0, heterogeneous payloads and repeated payloads. Applying this to the bank and inverse bank gives size+1<=4*2^ell(n). For padding, height(pad(d,t))=d+height(t) and size(pad(d,t))+1=2^d(size(t)+1). Substituting the exact six entries into the fixed eight-occurrence exterior gives height<=ell(n)+7 and size+1<=280(n+1) for both actual origin and current image. These are numerical polynomial bounds on constructed witnesses; they impose no restriction on the all-source domain.")),
            Definition("LocalRenumbering", "Separate Syntactic Renumbering", LocalStatement(),
                "Name is List Bool, a finite syntactic spelling. Each formula is represented by its ordered name-occurrence list. localCount(names)=length(dedup(names)); localIndex uses the index in that fixed syntactic deduplication order. commonCount(formulas)=max(1,foldr(max,0,map(localCount,formulas))). commonIndex embeds localIndex into Fin(commonCount). Each formula independently extends every assignment on its appearing names. Different formulas need not agree on equal spellings; the common universe uses the maximum local count, not a union count."),
            Definition("CoordinateSpec", "Exact Coordinate Interface", CoordinateStatement(),
                "nativeClassNames abbreviates the function i ↦ value(coord(i)), represented by its six entries. The two explicit permutations preserve the source/native coordinate correspondence and the six original canonical class names."),
            Describe.Lean(DescribeId.Create("native-boolean-b-height"),
                DeclarationHandle.Create(Prefix+"B_height"), H("Exact Basis Heights"),
                StatementSource.FromAuthor(Disp(All("d",V("Nat"),EqOf(Call("height",Call("B",V("d"))),V("d"))))), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Every original B(d) has height d, including B(0)=beta. Thus B(1) through B(6) are distinct actual branch values."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("native-boolean-pad-preimage"),
                DeclarationHandle.Create(Prefix+"pad_preimage"), H("Actual Basis Preimages"),
                StatementSource.FromAuthor(Disp(All("d",V("Nat"),EqOf(Call("rho",Call("pad",V("d"),V("alpha"))),Call("B",V("d")))))), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Padding alpha to depth d gives an actual predecessor of the original B(d). Every prescribed basis image is therefore in the original substitution image, with no replacement image predicate."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("native-boolean-assignment-banks"), DeclarationHandle.Create(Prefix+"native_boolean_assignment_banks"),
                H("Full FTC Lemma 6.1"), StatementSource.FromAuthor(Disp(MainStatement())), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The first clause holds for every natural n and every Boolean assignment, and supplies both second=false and second=true actual witnesses. At n=0, ell=1, selected is empty and the bank is B(1), while both witness families remain available. Independently of every assignment, zeroTuple=[B(1),B(3),B(4),B(2),B(5),B(6)] in native order is B(1) through B(6) in D order. Its explicit origin is filling of the corresponding pad(j,alpha) values. The six values are distinct branch images and its full predecessor is Rzero=predecessor(0)=row. This is the unconditional Zstar witness.")),
                    Paragraph(Text("The statement combines existing actual geometry and whole-row supply with the quantitative full-skeleton construction. Finite lists, logarithms, sorting, injection extension and elementary arithmetic use the pinned mathlib library. No external hardness premise, open-problem result, source-size promise, native computed address or runtime workspace is introduced."))), DescribeRole.Theorem)
        )));

    private static DocumentBlock Definition(string name,string title,Formula statement,string prose) =>
        Describe.Lean(DescribeId.Create("native-boolean-"+name.ToLowerInvariant()),DeclarationHandle.Create(Prefix+name),
            H(title),StatementSource.FromAuthor(Disp(statement)),AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))),DescribeRole.Definition);
    private static Formula LiteralStatement()
    {
        var n=V("n");var d=Call("ell",n);var ws=Call("words",d);var i=V("i");
        var lengths=Call("sum",Call("literalLengths",n));
        return All("n",V("Nat"),Iff(Call("LiteralSpec",n),And(
            Call("PairwiseLe",ws),All("a",V("Address"),Iff(Member(V("a"),ws),EqOf(Call("length",V("a")),d))),
            EqOf(Call("length",Call("selected",n)),n),Call("Nodup",Call("selected",n)),Call("Injective",Call("variableWord",n)),
            All("i",Call("Fin",n),And(EqOf(Call("length",Call("variableWord",n,i)),d),
                EqOf(Call("literal",n,i),Call("append",ListOf(V("R"),V("L"),V("L")),Call("variableWord",n,i))),
                EqOf(Call("length",Call("literal",n,i)),Add(d,D(3))))),
            EqOf(lengths,Mul(n,Add(d,D(3)))),LeOf(lengths,Mul(n,Add(n,D(4)))))));
    }
    private static Formula AllSourceStatement()
    {
        var n=V("n");var u=V("u");var i=V("i");var j=V("j");
        return All("n",V("Nat"),Iff(Call("AllSources",n),And(
            All("u",V("Source"),All("i",Call("Fin",n),Iff(EqOf(Call("assignment",n,u,i),V("true")),
                EqOf(Call("readout",Call("literal",n,i),Call("rho",u)),V("branch"))))),
            All("u",V("Source"),All("i",Call("Fin",n),All("j",Call("Fin",n),Imp(
                EqOf(Call("literal",n,i),Call("literal",n,j)),EqOf(Call("assignment",n,u,i),Call("assignment",n,u,j)))))),
            EqOf(Call("branchBit",V("branch")),V("true")),EqOf(Call("branchBit",V("alpha")),V("false")),
            EqOf(Call("branchBit",V("beta")),V("false")),EqOf(Call("branchBit",V("absent")),V("false")))));
    }
    private static Formula BankStatement()
    {
        var n=V("n");var b=V("b");var c=V("C");var a=V("a");var i=V("i");
        return All("n",V("Nat"),All("b",Assignment(n),All("C",V("Source"),Iff(Call("BankSpec",n,b,c),And(
            EqOf(c,Call("fullFillPayload",Call("ell",n),b)),
            All("a",V("Address"),Imp(EqOf(Call("length",a),Call("ell",n)),EqOf(Call("subtree",a,c),Call("some",Call("payload",b,a))))),
            All("i",Call("Fin",n),EqOf(Call("payload",b,Call("variableWord",n,i)),BitPayload(b,i))),
            All("a",V("Address"),Imp(All("i",Call("Fin",n),NeOf(Call("variableWord",n,i),a)),EqOf(Call("payload",b,a),V("beta")))),
            Call("Image",c),EqOf(Call("rootType",c),V("none")),LeOf(Call("height",c),Add(Call("ell",n),D(1))),
            LeOf(Add(Call("size",c),D(1)),Mul(D(1,6),Add(n,D(1)))))))));
    }
    private static Formula WitnessStatement()
    {
        var n=V("n");var b=V("b");var c=V("C");var s=V("second");var u=V("u");var uv=Call("value",u);var t=Call("rho",uv);
        var vals=Call("tuple",n,c,s);var h=Add(Call("ell",n),D(7));var m=Mul(D(2,8,0),Add(n,D(1)));
        return All("n",V("Nat"),All("b",Assignment(n),All("C",V("Source"),All("second",V("Bool"),All("u",V("Fiber"),
            Iff(Call("WitnessSpec",n,b,c,s,u),And(EqOf(t,Call("filling",vals)),Call("Injective",vals),
                EqOf(Call("canonicalRow",V("P"),uv),Call("predecessor",Call("targetIndex",s))),
                EqOf(Call("assignment",n,uv),b),All("i",Call("Fin",n),EqOf(Call("subtree",Call("literal",n,V("i")),t),Call("some",BitPayload(b,V("i"))))),
                LeOf(Call("height",t),h),LeOf(Add(Call("size",t),D(1)),m),
                LeOf(Call("height",uv),h),LeOf(Add(Call("size",uv),D(1)),m))))))));
    }
    private static Formula LocalStatement()
    {
        var fs=V("formulas");var ns=V("names");var ci=Call("commonIndex",fs,ns);var count=Call("commonCount",fs);
        return Iff(V("LocalRenumbering"),All("formulas",Call("List",Call("List",V("Name"))),And(LeOf(D(1),count),
            All("names",Call("List",V("Name")),Imp(Member(ns,fs),And(LeOf(Call("localCount",ns),count),Call("Injective",ci),
                All("a",Fn(Call("Appearing",ns),V("Bool")),Some("b",Assignment(count),All("x",Call("Appearing",ns),
                    EqOf(App(V("b"),App(ci,V("x"))),App(V("a"),V("x"))))))))))));
    }
    private static Formula CoordinateStatement() => Iff(V("CoordinateSpec"),And(
        Call("LeftInverse",V("dToNative"),V("nativeToD")),Call("LeftInverse",V("nativeToD"),V("dToNative")),
        EqOf(V("nativeClassNames"),ListOf(D(0),D(1),D(3),D(4),D(5),D(7)))));
    private static Formula MainStatement()
    {
        var n=V("n");var b=V("b");var bank=Call("bank",b);
        return And(All("n",V("Nat"),And(Call("LiteralSpec",n),Call("AllSources",n),
            All("b",Assignment(n),And(Call("BankSpec",n,b,bank),All("second",V("Bool"),
                Some("u",V("Fiber"),Call("WitnessSpec",n,b,bank,V("second"),V("u")))))))),
            And(EqOf(Call("ell",D(0)),D(1)),EqOf(Call("selected",D(0)),ListOf()),
                All("b",Assignment(D(0)),EqOf(Call("bank",V("b")),Call("B",D(1))))),
            Some("u",V("Fiber"),And(EqOf(Call("rho",Call("value",V("u"))),Call("filling",V("zeroTuple"))),
                Call("Injective",V("zeroTuple")),EqOf(Call("canonicalRow",V("P"),Call("value",V("u"))),Call("predecessor",D(0))))),
            V("LocalRenumbering"),V("CoordinateSpec"));
    }
    private static Formula V(string s) => F.Id(s);
    private static Formula Par(Formula f) => Seq(Open,f,Close);
    private static Formula App(Formula f, Formula a) => new Formula.Apply(f,[a]);
    private static Formula Call(string n, params Formula[] a) => new Formula.Apply(Seq(Operatorname,Grp(V(n))),[..a]);
    private static Formula Assignment(Formula n) => Fn(Call("Fin",n),V("Bool"));
    private static Formula Fn(Formula a, Formula b) => Seq(Par(a),Sp,To,Sp,Par(b));
    private static Formula Add(Formula a,Formula b) => Seq(Par(a),Sp,Plus,Sp,Par(b));
    private static Formula Mul(Formula a,Formula b) => Seq(Par(a),Sp,Times,Sp,Par(b));
    private static Formula EqOf(Formula a,Formula b) => Seq(a,Sp,Eq,Sp,b);
    private static Formula NeOf(Formula a,Formula b) => Seq(a,Sp,Neq,Sp,b);
    private static Formula LeOf(Formula a,Formula b) => Seq(a,Sp,Leq,Sp,b);
    private static Formula Member(Formula a,Formula b) => Seq(a,Sp,InMacro,Sp,b);
    private static Formula Iff(Formula a,Formula b) => Seq(Par(a),Sp,Leftrightarrow,Sp,Par(b));
    private static Formula Imp(Formula a,Formula b) => Seq(Par(a),Sp,Implies,Sp,Par(b));
    private static Formula And(params Formula[] fs) => Seq(fs.Select((f,i)=>i==0?Par(f):Seq(Sp,Land,Sp,Par(f))).ToArray());
    private static Formula All(string n,Formula t,Formula b) => Seq(Forall,Sp,V(n),Colon,Sp,t,Comma,Sp,Par(b));
    private static Formula Some(string n,Formula t,Formula b) => Seq(Exists,Sp,V(n),Colon,Sp,t,Comma,Sp,Par(b));
    private static Formula ListOf(params Formula[] fs) => Seq(OpenBracket,Seq(fs.Select((f,i)=>i==0?f:Seq(Comma,Sp,f)).ToArray()),CloseBracket);
    private static Formula BitPayload(Formula b,Formula i) => Call("ite",EqOf(App(b,i),V("true")),Call("B",D(1)),V("beta"));
}
