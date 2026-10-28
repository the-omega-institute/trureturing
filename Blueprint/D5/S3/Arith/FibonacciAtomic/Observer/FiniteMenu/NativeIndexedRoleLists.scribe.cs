using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer.FiniteMenu;
internal sealed class NativeIndexedRoleListsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Observer/FiniteMenu/NativeIndexedRoleLists.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Concrete deterministic exact role lists for arbitrary indexed native read constraints.",
        H("Native Indexed Role Lists"), Blocks(
            Paragraph(Text("Source is the entire set of finite nonempty ordered FreeMagma Bool terms. Alpha is of(true), beta is of(false), and pair is mul. The original substitution sends alpha to beta, beta to pair(beta,alpha), and pairs to pairs of images. Class A is exactly alpha, H is exactly beta, I is the original actual substitution image with beta removed, and O is the complement of their union. The computable kind classifier agrees with these four disjoint classes. Applying the original pair_image theorem gives type I exactly for the ordered pairs (H,A), (H,H), (H,I), (I,H), (I,I); the other eleven give O. No branch has leaf type.")),
            Paragraph(Text("Roles are in original order a,c,bone,btwo,bthree,bfour. Their native filling indices are 0,3,1,2,4,5, using the original dToNative permutation. The physical occurrences LLL and LRL share a; RLL and RRL share c; LLR, LRR, RLR and RRR give bone, btwo, bthree and bfour. These are whole subtree identities, not Boolean labels. Different role lists may overlap.")),
            Paragraph(Text("An arbitrary installed record family has literals words(i) and requested raw replies replies(i), indexed by every i in Fin(n). Install keeps the original index of every word of length at least three, its actual occurrence role, the suffix after those three letters, and its requested reply. It preserves duplicate suffixes and separate repeated-role occurrences. ShortGuard requires branch on every shorter word, including the empty word. Both conditions refer to the same proposed reply family.")),
            Paragraph(Text("Under(v,R) follows the actual prefix trie edges, removing exactly v from every surviving suffix. Its membership theorem restores v and preserves the index, role and reply. Explicit(v) means that some record survives; markers retain every ending index in its original order. RootNode describes the suffix-record trie. The original installedRoot is # exactly when n=0 and is the explicit empty-address root for every nonempty raw menu, including a menu consisting entirely of short reads. ChildNode uses # precisely when no record lies below that child. NodeRecords at # is empty. Thus # admits an arbitrary finite subtree and never denotes a missing actual child of a pair.")),
            Paragraph(Text("The function lists(R,v,d,k) contains actual Source values. At # its prescribed lists are [alpha], [beta], [B(1),...,B(6)], and [pair(alpha,B(1)),...,pair(alpha,B(6))]. Here B(j) is the original padding of beta. The original pad_preimage proves image membership, and B_height proves all six entries distinct. Each I and O list has length six; each leaf list has length one.")),
            Paragraph(Text("At an explicit root with no suffix records the construction still pairs the prescribed # child bases. At an explicit node, alpha or beta is retained exactly when every ending index of that role asks for that leaf and every strict descendant index of that role asks for absent. This test does not require either child branch language to be realizable. A pair is permitted exactly when every ending role index asks for branch. In fixed A,H,I,O order the construction considers all sixteen ordered child-type pairs, enumerates their concrete retained left and right values, assigns the original parent type, removes duplicate whole terms and keeps the first six. Other roles impose no condition.")),
            Paragraph(Text("Exact(L,K) asserts that L has no repeated values, its length is at most six, all members lie in K, and if its length is less than six every member of K occurs in L. Language(R,d,k) consists of terms of type k satisfying every indexed raw readout for d. NodeLanguage uses the rebased records at that node. OriginalLanguage instead quantifies directly over every original i and every length-three occurrence followed by v and a residual suffix. The theorem identifies these two languages for every address, including empty and contradictory fibers.")),
            Paragraph(Text("The induction budget bounds only the finite observed suffix lengths, without bounding source size, source depth or compatible-language cardinality. The resulting list is independent of any larger valid recursion budget. Consequently the public explicit-node recurrence uses exactly the lists assigned to the two actual trie children. An unconstrained child always uses the same fixed basis.")),
            Paragraph(Text("For the pair induction, an actual compatible pair provides nonempty child languages. Exactness supplies at least one retained value in each. If either retained child list is saturated, pairing its six distinct members with one retained value of the other supplies six different parents of the required type. Therefore a short parent candidate list forces both relevant child lists to be complete. Unique ordered decomposition then supplies every actual pair. A zero child language supplies no parent. This proves the invariant without subtraction, inclusion-exclusion, finite-language assumptions or classical selection of data.")),
            Paragraph(Text("In the displayed formula, toENat is the natural-number cast to extended naturals, rho is the original substitution, and Fiber is NativeSixSourceCones.Fiber. Set.encard is the extended-natural cardinality, so the length of each list equals min(6,encard(K)) also when K is infinite or empty. For a short list, soundness and completeness identify its finite set with the entire language. A saturated list gives a six-element subset of K. The cardinal equation follows in either case from the original list invariant and pinned Set.encard monotonicity.")),
            Paragraph(Text("For every arbitrary native filling x, all proposed installed readouts hold exactly when ShortGuard holds and each x(dToNative(d)) satisfies its original role constraints. The same statement holds for every original origin u in NativeSixSourceCones.Fiber: the original recover and recover_fill reconstruct its entire current image as filling(recoveredNative(u)). The root lists, selected at installedRoot(n), are exact lists for the original typed role languages C(d). This is the actual native root correspondence, with no assumed recurrence or realization bridge.")),
            Paragraph(Text("Contradictory duplicates, empty suffixes, impossible root absence, early leaves and all-absent descendant cones follow the same rules. The statement supplies no shared semantic DAG, DAG node bound, polynomial-time implementation, matching theorem or new truncation-transfer theorem. It formalizes the source-specific constructive recurrence of the native finite-table classification Lemma 4.2, using the existing image grammar, original B suppliers and mature finite-list and cardinality facts. It asserts no literature novelty.")),
            Describe.Lean(DescribeId.Create("native-indexed-role-lists"),
                DeclarationHandle.Create(Prefix+"native_indexed_role_lists"),
                H("All Original Native Role Languages"), StatementSource.FromAuthor(Disp(WholeStatement())),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Specification includes the four original classes, the prescribed # basis and the empty-record explicit-root rule, exactness and extended-natural cardinality at every node, exact leaf and branch rules, prefix and marker correspondence, actual root and child records, the explicit recurrence, every original indexed language, exact original root lists and their cardinality, arbitrary native filling equivalence, and the recovered-origin root equivalence. Every field has its full universal quantifiers; no finite compatible-language premise is imposed."))), DescribeRole.Theorem)
        )));
    private static Formula WholeStatement()
    {
        var R=V("R");var v=V("v");var d=V("d");var k=V("k");var q=V("q");
        var t=V("t");var b=V("b");var l=V("l");var r=V("r");var n=V("n");
        var words=V("words");var replies=V("replies");var x=V("x");var u=V("u");
        var records=Call("List",V("Constraint"));var role=Call("Fin",D(6));
        var opt=Call("Option",V("Address"));var nil=ListOf();
        Formula At(Formula a) => Call("lists",R,a,d,k);
        Formula Lang(Formula a) => Call("nodeLanguage",R,a,d,k);
        Formula Roles(Formula body) => All("d",role,All("k",V("Kind"),body));
        Formula Nodes(Formula body) => All("R",records,All("v",opt,Roles(body)));
        Formula Raw(Formula body) => All("n",V("Nat"),All("words",Fn(Call("Fin",n),V("Address")),
            All("replies",Fn(Call("Fin",n),V("Reply")),body)));
        var installed=Call("install",words,replies);var root=Call("installedRoot",n);
        var original=Call("originalLanguage",words,replies,nil,d,k);
        var rootList=Call("lists",installed,root,d,k);
        var left=Call("lists",R,Call("childNode",R,v,V("false")),d);
        var right=Call("lists",R,Call("childNode",R,v,V("true")),d);
        var recovered=Call("recoveredNative",u);
        Formula RoleCompatible(Formula values) => All("d",role,
            Call("OriginalCompatible",words,replies,nil,d,App(values,Call("dToNative",d))));
        return And(
            All("t",V("Source"),All("k",V("Kind"),Iff(Call("Class",k,t),EqOf(Call("kind",t),k)))),
            All("R",records,Roles(EqOf(At(V("none")),Call("basis",k)))),
            All("R",records,All("v",V("Address"),Roles(Imp(EqOf(Call("under",v,R),nil),
                EqOf(At(Call("some",v)),Call("retain",Call("candidates",nil,d,k,V("basis"),V("basis")))))))),
            Nodes(Call("Exact",At(v),Lang(v))),
            Nodes(EqOf(Call("toENat",Call("length",At(v))),Call("min",D(6),Call("encard",Lang(v))))),
            All("R",records,All("v",opt,All("d",role,All("b",V("Bool"),
                Iff(Member(Call("of",b),Call("lists",R,v,d,Call("kind",Call("of",b)))),
                    Call("LeafRule",Call("nodeRecords",R,v),d,b)))))),
            All("R",records,All("d",role,All("l",V("Source"),All("r",V("Source"),
                Iff(Call("Compatible",R,d,Call("mul",l,r)),And(EqOf(Call("branchOK",R,d),V("true")),
                    Call("Compatible",Call("child",V("false"),R),d,l),
                    Call("Compatible",Call("child",V("true"),R),d,r))))))),
            All("R",records,All("v",V("Address"),All("q",V("Constraint"),
                Iff(Member(q,Call("under",v,R)),Member(Call("restore",v,q),R))))),
            All("R",records,All("v",V("Address"),Iff(Call("Explicit",R,v),
                Some("q",V("Constraint"),Member(Call("restore",v,q),R))))),
            All("R",records,All("v",V("Address"),All("q",V("Constraint"),
                Iff(Member(q,Call("markers",R,v)),And(Member(Call("restore",v,q),R),EqOf(Call("suffix",q),nil)))))),
            All("R",records,EqOf(Call("nodeRecords",R,Call("rootNode",R)),R)),
            All("R",records,All("v",V("Address"),All("b",V("Bool"),
                EqOf(Call("nodeRecords",R,Call("childNode",R,v,b)),Call("child",b,Call("under",v,R)))))),
            All("R",records,All("v",V("Address"),Roles(Imp(Call("Explicit",R,v),
                EqOf(At(Call("some",v)),Call("retain",Call("candidates",Call("under",v,R),d,k,left,right))))))),
            Raw(All("v",V("Address"),Roles(EqOf(Call("nodeLanguage",installed,Call("some",v),d,k),
                Call("originalLanguage",words,replies,v,d,k))))),
            All("n",V("Nat"),And(Iff(EqOf(root,V("none")),EqOf(n,D(0))),
                Iff(EqOf(root,Call("some",nil)),NeOf(n,D(0))))),
            Raw(All("v",V("Address"),Iff(Call("InstalledExplicit",words,replies,v),
                Or(And(NeOf(n,D(0)),EqOf(v,nil)),Some("q",V("Constraint"),Member(Call("restore",v,q),installed)))))),
            Raw(Roles(Call("Exact",rootList,original))),
            Raw(Roles(EqOf(Call("toENat",Call("length",rootList)),Call("min",D(6),Call("encard",original))))),
            Raw(All("x",Fn(role,V("Source")),Iff(Call("Realizes",words,replies,Call("filling",x)),
                And(Call("ShortGuard",words,replies),RoleCompatible(x))))),
            Raw(All("u",V("Fiber"),And(EqOf(Call("filling",recovered),Call("rho",Call("value",u))),
                Iff(Call("Realizes",words,replies,Call("rho",Call("value",u))),
                    And(Call("ShortGuard",words,replies),RoleCompatible(recovered)))))));
    }
    private static Formula V(string s) => F.Id(s);
    private static Formula Par(Formula f) => Seq(Open,f,Close);
    private static Formula App(Formula f,Formula a) => new Formula.Apply(f,[a]);
    private static Formula Call(string n,params Formula[] a) => new Formula.Apply(Seq(Operatorname,Grp(V(n))),[..a]);
    private static Formula Fn(Formula a,Formula b) => Seq(Par(a),Sp,To,Sp,Par(b));
    private static Formula EqOf(Formula a,Formula b) => Seq(a,Sp,Eq,Sp,b);
    private static Formula NeOf(Formula a,Formula b) => Seq(a,Sp,Neq,Sp,b);
    private static Formula Member(Formula a,Formula b) => Seq(a,Sp,InMacro,Sp,b);
    private static Formula Iff(Formula a,Formula b) => Seq(Par(a),Sp,Leftrightarrow,Sp,Par(b));
    private static Formula Imp(Formula a,Formula b) => Seq(Par(a),Sp,Implies,Sp,Par(b));
    private static Formula Or(Formula a,Formula b) => Seq(Par(a),Sp,Lor,Sp,Par(b));
    private static Formula And(params Formula[] fs) => Seq(fs.Select((f,i)=>i==0?Par(f):Seq(Sp,Land,Sp,Par(f))).ToArray());
    private static Formula All(string n,Formula t,Formula b) => Seq(Forall,Sp,V(n),Colon,Sp,t,Comma,Sp,Par(b));
    private static Formula Some(string n,Formula t,Formula b) => Seq(Exists,Sp,V(n),Colon,Sp,t,Comma,Sp,Par(b));
    private static Formula ListOf(params Formula[] fs) => Seq(OpenBracket,Seq(fs.Select((f,i)=>i==0?f:Seq(Comma,Sp,f)).ToArray()),CloseBracket);

}
