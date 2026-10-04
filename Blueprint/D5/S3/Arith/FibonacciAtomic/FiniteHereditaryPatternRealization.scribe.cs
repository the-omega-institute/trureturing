using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class FiniteHereditaryPatternRealizationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/FiniteHereditaryPatternRealization.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The specified padded face tables give actual third-substitution images with every finite hereditary information-leaf pattern at equal composition.",
        H("Finite Hereditary Patterns in Actual Tree Images"), Blocks(
            Paragraph(Text("Sources are complete nonempty ordered binary trees with alpha and beta leaves. "
                + "The native substitution rho sends alpha to beta and beta to (beta,alpha), preserving every pairing. "
                + "Addresses are finite root-first Boolean lists: false denotes left, true denotes right. "
                + "The original endpoint observation reports alpha, beta, branch or absent, including at the root "
                + "and after a path has passed a leaf. Composition c records the two leaf counts.")),
            Def("Block", "Three column entries", "The entries a, u and v name the complete blocks A, U and V."),
            Def("preimage", "Literal block preimages", "The preimages are alpha, ((alpha,alpha),beta) and ((alpha,beta),alpha), respectively."),
            Paragraph(Text("The blocks use the thirdImage operation on these preimages. Their compositions are (1,2), (4,7) and (4,7).")),
            Def("Delta", "Indexed information leaves", "Delta(P,S) consists of addresses that are leaves of every indexed source in S "
                + "and carry alpha in at least one row and beta in at least one row. Distinct indices may name the same tree."),
            Def("D", "Residual two-block information", "D is Delta for U and V. It contains the address LRLR."),
            Def("Mixed", "Contributing columns", "Mixed(X,S) means no row in S contains A and at least one row contains each of U and V."),
            Def("B_T", "Right-comb context", "B(n,X) has n+1 holes and no literal leaves. B(0,X)=X(0); "
                + "B(n+1,X) pairs X(0) with the context on the remaining entries."),
            Def("hole", "Hole addresses", "The hole addresses follow the left-to-right leaf order. "
                + "For one hole the address is empty; otherwise each initial hole is reached by right steps followed by left, "
                + "and the last is reached entirely by right steps."),
            Def("locate", "Full address decomposition", "locate(n,w) is none when w ends at an internal context node. "
                + "Otherwise it is some(j,v), where w=hole(n,j)++v. The suffix may be empty or continue beyond a block leaf."),
            Def("maximalFaces", "Maximal faces", "This is the set of all inclusion-maximal members of K."),
            Def("FaceColumn", "Face columns", "An original column is a pair (F,k), with F a maximal face and k in F."),
            Def("faceEntry", "Face table", "The entry in row i and column (F,k) is V for i=k, U for i in F other than k, and A outside F."),
            Def("rowCount", "Original row counts", "rowCount(K,i) counts the original columns whose face contains i."),
            Def("M", "Maximum row count", "M(K) is the maximum original row count over all indices, with zero for an empty index set."),
            Def("PaddingColumn", "Private padding", "Row i receives M(K)-rowCount(K,i) private padding columns."),
            Def("Column", "Complete column set", "The complete column set is the disjoint union of original columns and private padding columns."),
            Def("entry", "Padded table", "A padding column contains U in its owner's row and A elsewhere; original entries retain their face-table values."),
            Describe.Lean(DescribeId.Create("finite-hereditary-pattern-realization-result"),
                DeclarationHandle.Create(Prefix + "result"), H("Full reports and hereditary realization"),
                StatementSource.FromAuthor(ResultFormula()), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("In the displayed statement, n,m,T,N are natural numbers, j,k range over Fin(n+1), "
                        + "w,v,u,r are finite addresses, and X in the report clause maps Fin(n+1) to Source. "
                        + "In the information clause X maps Fin(m) times Fin(n+1) to Block, S is a finite subset of Fin(m), "
                        + "and Xj denotes its j-th column. Bblocks(n,X)(i) means B(n,j maps to block(X(i,j))). A concatenation is written concat. Empty denotes the empty address. "
                        + "read(n,X,w) is branch when locate(n,w)=none and is readout(v,X(j)) when locate(n,w)=some(j,v). "
                        + "K is a finite family of subsets of Fin(m); Hereditary(K) is the lower-set property on finite subsets, and Singletons(K) means every singleton belongs to K. "
                        + "T=card(Column(K)) and N=M(K) are fixed by the complete padded table. "
                        + "The result holds for every column enumeration e: Fin(T-1+1) equivalent to Column(K). "
                        + "Qtable(K,e)(i) is B(T-1,j maps to preimage(entry(i,e(j)))); "
                        + "Ptable(K,e)(i) uses block in place of preimage, with the same e. "
                        + "The displayed let-bindings set Q=Qtable(K,e) and P=Ptable(K,e). "
                        + "I(3) is the actual range of the third native substitution. "
                        + "c1 and c2 are the two coordinates of composition, card is finite cardinality, and Nonempty means there exists an address.")),
                    Paragraph(Text("The report holds at every finite address. Its internal-node case is exactly the strict-prefix condition "
                        + "in the second conjunct. The third conjunct describes all information leaves. The fourth makes contributions "
                        + "from different holes disjoint and also makes the suffix unique. These statements include the empty root address "
                        + "and arbitrary paths extending past block leaves.")),
                    Paragraph(Text("Every face lies in a maximal face. Each face column singles out one V row among the U rows of that face. "
                        + "A set of at least two indices has a contributing original column exactly when it is a face of K. "
                        + "Private padding contributes no information leaf on any such set. Padding equalizes the non-A counts without "
                        + "changing this equivalence. For every fixed column order, the specified complete Q and P trees have the displayed common compositions and exact leaf count. "
                        + "The face columns distinguish every pair of rows, and injective native transport gives the unique complete preimages.")),
                    Paragraph(Text("Downward-closed finite set families and Helly terminology are classical background. "
                        + "The equal-composition block-table realization and its exact information-leaf equivalence are the tree-specific derivation."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Def(string name, string title, string prose) => Describe.Lean(
        DescribeId.Create("hereditary-pattern-" +
            (name == "Block" ? "block-type" : name.ToLowerInvariant().Replace('_', '-'))),
        DeclarationHandle.Create(Prefix + name),
        H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(prose))), DescribeRole.Definition);
    private static Formula V(string s) => F.Id(s);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Call(string name, params Formula[] xs) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. xs]);
    private static Formula EqOf(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula InOf(Formula a, Formula b) => Seq(a, Sp, InMacro, Sp, b);
    private static Formula LeOf(Formula a, Formula b) => Seq(a, Sp, Leq, Sp, b);
    private static Formula Add(Formula a, Formula b) => Seq(a, Sp, Plus, Sp, b);
    private static Formula Mul(Formula a, Formula b) => Seq(a, Sp, b);
    private static Formula Pair(Formula a, Formula b) => Par(Seq(a, Comma, Sp, b));
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));
    private static Formula IffOf(Formula a, Formula b) => Seq(Par(a), Sp, Iff, Sp, Par(b));
    private static Formula Not(Formula a) => Seq(Neg, Par(a));
    private static Formula And(params Formula[] xs) => Seq(xs.Select((x,i) =>
        i == 0 ? Par(x) : Seq(Sp, Land, Sp, Par(x))).ToArray());
    private static Formula Names(string names) => Seq(names.Split(',').Select((name, i) =>
        i == 0 ? V(name) : Seq(Comma, Sp, V(name))).ToArray());
    private static Formula All(string names, Formula body) => Seq(Forall, Sp, Names(names), Comma, Sp, Par(body));
    private static Formula Exists(string names, Formula body) => Seq(F.Exists, Sp, Names(names), Comma, Sp, Par(body));
    private static Formula Let(string name, Formula value, Formula body) => Seq(
        Operatorname, Grp(V("let")), Sp, EqOf(V(name), value), Sp,
        Operatorname, Grp(V("in")), Sp, Par(body));
    private static Formula ResultFormula()
    {
        Formula n=V("n"), m=V("m"), x=V("X"), w=V("w"), j=V("j"), k=V("k"), v=V("v"), u=V("u"), r=V("r");
        Formula t=V("T"), z=V("N"), q=V("Q"), p=V("P"), family=V("K"), s=V("S"), i=V("i"), a=V("R");
        Formula report=All("n,X,w",EqOf(Call("readout",w,Call("B",n,x)),Call("read",n,x,w)));
        Formula prefix=All("n,w",IffOf(EqOf(Call("locate",n,w),V("none")),Exists("j,r",And(
            Not(EqOf(r,V("empty"))),EqOf(Call("hole",n,j),Call("concat",w,r))))));
        Formula leaves=All("m,n,X,S,w",IffOf(InOf(w,Call("Delta",Call("Bblocks",n,x),s)),Exists("j,v",And(
            EqOf(w,Call("concat",Call("hole",n,j),v)),Call("Mixed",Call("Xj",x,j),s),InOf(v,V("D"))))));
        Formula disjoint=All("n,j,k,v,u",Imp(EqOf(Call("concat",Call("hole",n,j),v),
            Call("concat",Call("hole",n,k),u)),And(EqOf(j,k),EqOf(v,u))));
        Formula pi=Call("P",i), qi=Call("Q",i);
        Formula data=All("i",And(EqOf(Call("rho3",qi),pi),InOf(pi,Call("I",D(3))),
            EqOf(Call("c",qi),Pair(Add(t,z),z)),
            EqOf(Call("c",pi),Pair(Add(t,Mul(D(3),z)),Add(Mul(D(2),t),Mul(D(5),z)))),
            EqOf(Add(Call("c1",pi),Call("c2",pi)),Add(Mul(D(3),t),Mul(D(8),z)))));
        Formula unique=All("i,R",IffOf(EqOf(Call("rho3",a),pi),EqOf(a,qi)));
        Formula pattern=All("S",Imp(LeOf(D(2),Call("card",s)),
            IffOf(Call("Nonempty",Call("Delta",p,s)),InOf(s,family))));
        Formula trees=Let("Q",Call("Qtable",family,V("e")),
            Let("P",Call("Ptable",family,V("e")),
                And(Call("Injective",q),Call("Injective",p),data,unique,pattern)));
        Formula table=Let("T",Call("card",Call("Column",family)),
            Let("N",Call("M",family),And(LeOf(D(1),t),All("e",trees))));
        Formula realization=All("m",Imp(LeOf(D(2),m),All("K",
            Imp(And(Call("Hereditary",family),Call("Singletons",family)),table))));
        return Disp(And(report,prefix,leaves,disjoint,realization));
    }
}
