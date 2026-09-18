using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Budget;

internal sealed class ResidueChildPrefixStructureDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every identifying residue protocol has chronological child prefixes; every ordered "
            + "identifying child family with internal nonlast heads has an exact parent realization.",
        H("Chronological Child Prefixes for Residue Protocols"),
        Blocks(
            Paragraph(Text(
                "Let p be prime, let d<e be natural numbers, and let b be a residue modulo "
                    + "p to the power d. The nonempty finite set I consists of next-depth "
                    + "labels over b. Write k=card(I), X=ZMod(p^e), C(z) for the complete "
                    + "fiber of z at depth d+1, and S for the union of C(z) over z in I. "
                    + "These are the node, children and siblings fibers of residue geometry. "
                    + "Labels and members of I are coerced to their underlying residues.")),
            Paragraph(Text(
                "Tree denotes PassiveProtocol X with natural-number answers. The actual "
                    + "readout q(c,a) is the greatest congruence depth of c and a, including "
                    + "zero and e. R(T,a) is runPassiveProtocol q T a, a list of Sigma records "
                    + "containing each center and its actual answer. Write Trace for this "
                    + "list type, entry(c,r) for one record, len for list length, app for "
                    + "concatenation and one for a singleton list. Ident(A,T) means that "
                    + "R(T,a)=R(T,b) for a,b in A implies a=b. Equiv(A,B) denotes bijections "
                    + "and Map(A,B) denotes functions. No bound on the number of syntactic "
                    + "nodes or on the depths of all answer branches is assumed.")),
            Describe.Lean(
                DescribeId.Create("residue-child-prefix-structure"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/Budget/ResidueChildPrefixStructure.residue_child_prefix_structure"),
                H("Extraction and arbitrary-family realization"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The first clause applies to every identifying original tree T. It "
                            + "produces a bijection o from Fin k to I, whole child trees U, "
                            + "prefixes P, centers c and continuations next. Every center c(i) "
                            + "belongs to its child and U(i) identifies that complete child. "
                            + "For every target a in it, the original trace is exactly "
                            + "P(i) followed by R(U(i),a). The prefix has at least i entries. "
                            + "When i+1<k, or when k=1 and d+1<e, U(i) has head c(i) and "
                            + "continuation next(i). There is no head requirement on the last "
                            + "child when k>1, nor on a singleton leaf. Whenever i<j, P(i) "
                            + "followed by entry(c(i),d) is a prefix of P(j). Consequently "
                            + "len(R(T,a))=len(P(i))+len(R(U(i),a)) is at least "
                            + "i+len(R(U(i),a)). Original constant delays are retained.")),
                    Paragraph(Text(
                        "The second clause is independently universal in the bijection o "
                            + "and in the supplied child family U. Each U(i) identifies C(o(i)); "
                            + "only nonlast trees must have a head centered in their own child. "
                            + "The resulting c and next are those actual heads and continuations "
                            + "at nonlast positions. The parent V identifies S, and its trace "
                            + "at a target in child i is exactly the first i entries of "
                            + "List.ofFn(j maps to entry(c(j),d)), followed by the unchanged "
                            + "trace of U(i). Its length is i+len(R(U(i),a)). The final value "
                            + "c(k-1) is unused and unrestricted. In particular, no extra "
                            + "entry query is charged to the final child.")),
                    Paragraph(Text(
                        "For extraction, structural induction on T simultaneously tracks the "
                            + "remaining child labels, their distinct exhaustive order, child "
                            + "identification and chronological prefixes. An outside center "
                            + "has a constant answer on the remaining state; this answer is "
                            + "prepended to all later prefixes. An inside center enters one "
                            + "child. Its entire query subtree is retained for that child, "
                            + "and its depth-d continuation handles the other labels. Keeping "
                            + "only one continuation inside the entered child would be incorrect: "
                            + "for p=2,e=2,d=0 and center zero, targets zero and two in the "
                            + "same child give answers two and one. A stop can identify the "
                            + "remaining state only when it is a singleton leaf. Thus a "
                            + "singleton nonleaf is normalized through its actual constant roots.")),
                    Paragraph(Text(
                        "For realization, finite induction starts with the supplied last "
                            + "tree unchanged. At an earlier supplied head, only response d "
                            + "is redirected to the already constructed suffix. Within the "
                            + "head's own child the answer differs from d, so the entire "
                            + "supplied trace is preserved. All other children answer d. "
                            + "These disjoint responses prove identification and give the "
                            + "exact prefix formula. For k=1 the construction is just U(0). "
                            + "Residue geometry is independent of a prior; a uniform positive "
                            + "rational prior suffices when applying its geometric conclusions. "
                            + "The result concerns actual protocol traces and makes no claim "
                            + "about selector termination, optimal horizons or assignment runtime."))),
                DescribeRole.Theorem))));

    private static Formula V(string s) => F.Id(s);
    private static Formula C(string s, params Formula[] a) => Call(s, a);
    private static Formula Par(Formula a) => Seq(Left, Open, a, Right, Close);
    private static Formula EqTo(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula LtTo(Formula a, Formula b) => Seq(a, Sp, Lt, Sp, b);
    private static Formula LeTo(Formula a, Formula b) => Seq(a, Sp, Leq, Sp, b);
    private static Formula In(Formula a, Formula b) => Seq(a, Sp, InMacro, Sp, b);
    private static Formula Both(Formula a, Formula b) => Seq(Par(a), Sp, Land, Sp, Par(b));
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Rightarrow, Sp, Par(b));
    private static Formula All(Formula a, Formula t, Formula body) =>
        Seq(Forall, Sp, a, Sp, InMacro, Sp, t, Comma, Sp, body);
    private static Formula Ex(Formula a, Formula t, Formula body) =>
        Seq(Exists, Sp, a, Sp, InMacro, Sp, t, Comma, Sp, body);
    private static Formula Ands(params Formula[] a) => Seq(Left, OpenBracket,
        new Formula.Aligned([.. a.Select((x, i) => i == 0 ? Par(x) : Seq(Land, Sp, Par(x)))]),
        Right, CloseBracket);

    private static Formula Statement()
    {
        var p=V("p"); var e=V("e"); var d=V("d"); var b=V("b"); var set=V("I");
        var k=V("k"); var i=V("i"); var j=V("j"); var a=V("a");
        var o=V("o"); var u=V("U"); var t=V("T"); var v=V("V");
        var pre=V("P"); var c=V("c"); var next=V("next"); var x=V("X");
        var tree=V("Tree"); var trace=V("Trace"); var nat=Seq(Mathbb, Grp(V("N")));
        var fin=C("Fin",k); var equiv=C("Equiv",fin,set);
        Formula At(Formula f, Formula z) => C("apply",f,z);
        Formula Child(Formula z) => C("C",At(o,z));
        Formula Run(Formula f) => C("R",f,a);
        Formula Length(Formula f) => C("len",f);
        Formula Succ(Formula z) => Seq(z,Plus,D(1));
        Formula Ident(Formula s, Formula f) => C("Ident",s,f);
        Formula Map(Formula f, Formula g) => C("Map",f,g);
        Formula App(Formula f, Formula g) => C("app",f,g);
        Formula Query(Formula z) => C("query",At(c,z),At(next,z));
        Formula Entry(Formula z) => C("entry",At(c,z),d);
        var nonlast=LtTo(Succ(i),k);
        var head=Seq(Par(nonlast),Sp,Lor,Sp,Par(Both(EqTo(k,D(1)),LtTo(Succ(d),e))));
        var extraction=All(t,tree,Imp(Ident(V("S"),t),
            Ex(o,equiv,Ex(u,Map(fin,tree),Ex(pre,Map(fin,trace),
            Ex(c,Map(fin,x),Ex(next,Map(fin,Map(nat,tree)),Ands(
                All(i,fin,Ands(In(At(c,i),Child(i)),Ident(Child(i),At(u,i)),
                    Imp(head,EqTo(At(u,i),Query(i))),LeTo(i,Length(At(pre,i))),
                    All(a,Child(i),EqTo(Run(t),App(At(pre,i),Run(At(u,i))))))),
                All(i,fin,All(j,fin,Imp(LtTo(i,j),
                    C("IsPrefix",App(At(pre,i),C("one",Entry(i))),At(pre,j)))))))))))));
        var root=Ex(V("x"),Child(i),Ex(V("f"),Map(nat,tree),
            EqTo(At(u,i),C("query",V("x"),V("f")))));
        var prefix=C("take",i,C("ofFn",Seq(j,Sp,Mapsto,Sp,Entry(j))));
        var realization=All(o,equiv,All(u,Map(fin,tree),Imp(
            Both(All(i,fin,Ident(Child(i),At(u,i))),All(i,fin,Imp(nonlast,root))),
            Ex(c,Map(fin,x),Ex(next,Map(fin,Map(nat,tree)),Ex(v,tree,Ands(
                All(i,fin,Imp(nonlast,Both(In(At(c,i),Child(i)),EqTo(At(u,i),Query(i))))),
                Ident(V("S"),v),All(i,fin,All(a,Child(i),Ands(
                    EqTo(Run(v),App(prefix,Run(At(u,i)))),
                    EqTo(Length(Run(v)),Seq(i,Plus,Length(Run(At(u,i)))))))))))))));
        return Disp(All(Seq(p,Comma,e,Comma,d),nat,Imp(Both(C("Prime",p),LtTo(d,e)),
            All(b,C("ZMod",C("pow",p,d)),All(set,C("Finset",C("ZMod",C("pow",p,Succ(d)))),
                Imp(Both(C("Nonempty",set),C("Subset",set,C("children",p,d,b))),
                    Both(extraction,realization)))))));
    }
}
