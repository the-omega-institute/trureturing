using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Completion;

internal sealed class RawGroupZeroQuotientDocument : IScribeDocumentDefinition
{
    private const string Gid = "D5/S3/Quantum/Completion/RawGroupZeroQuotient.";
    private static Formula I(string s) => F.Id(s);
    private static Formula Real => Seq(Mathbb, Grp(I("R")));
    private static Formula Arr(Formula a, Formula b) => Seq(Open,a,Sp,To,Sp,b,Close);
    private static Formula All(string s, Formula t, Formula b) => Seq(Open,Forall,Sp,I(s),Colon,Sp,t,Comma,Sp,b,Close);
    private static Formula Ex(string s, Formula t, Formula b) => Seq(Open,Exists,Sp,I(s),Colon,Sp,t,Comma,Sp,b,Close);
    private static Formula Eqn(Formula a, Formula b) => Seq(a,Sp,Eq,Sp,b);
    private static Formula Imp(Formula a, Formula b) => Seq(Open,a,Sp,Rightarrow,Sp,b,Close);
    private static Formula Iff(Formula a, Formula b) => Seq(Open,a,Sp,Leftrightarrow,Sp,b,Close);
    private static Formula And(Formula a, Formula b) => Seq(Open,a,Sp,Land,Sp,b,Close);
    private static Formula Conj(params Formula[] xs)
    {
        var result=xs[^1];
        for(var i=xs.Length-2;i>=0;i--) result=And(xs[i],result);
        return result;
    }
    private static Formula Mul(Formula a, Formula b) => Seq(Open,a,Sp,Cdot,Sp,b,Close);
    private static Formula Inv(Formula a) => Call("inv",a);
    private static Formula C(Formula a, Formula b) => Call("c",a,b);
    private static Formula Dst(Formula a, Formula b) => Call("d",a,b);
    private static Formula Z => Call("zeroSubgroup",I("h"),I("hs"));
    private static Formula Quot(Formula z) => Call("QuotientGroup",I("G"),z);
    private static Formula Q => Quot(Z);
    private static Formula Mk(Formula a) => Call("mk",a);
    private static Formula Mem(Formula a, Formula z) => Call("Member",a,z);
    private static Formula Sym(string m,string c) => All("a",I(m),All("b",I(m),Eqn(Call(c,I("a"),I("b")),Call(c,I("b"),I("a")))));
    private static Formula Base(Formula b) => All("G",new Formula.Subscript(I("Type"),I("u")),All("gG",Call("Group",I("G")),
        All("U",Arr(I("G"),I("G")),All("c",Arr(I("G"),Arr(I("G"),Real)),All("h",Call("RawCost",I("U"),I("c")),b)))));
    private static Formula Frame(Formula b) => Base(All("hs",Sym("G","c"),b));
    private static Formula OnG(Formula b,params string[] names)
    {
        for(var i=names.Length-1;i>=0;i--) b=All(names[i],I("G"),b);
        return b;
    }
    private static DocumentBlock Entry(string name,string title,Formula formula,string text) =>
        Describe.Lean(DescribeId.Create("raw-group-zero-quotient-"+name.Replace('_','-').ToLowerInvariant()),
            DeclarationHandle.Create(Gid+name),H(title),StatementSource.FromAuthor(Disp(formula)),
            AssessedProvenance.FromRepo(),Blocks(Paragraph(Text(text))),DescribeRole.Theorem);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The zero set of the actual group cost is normal, and both the cost and arbitrary marker descend to its actual group quotient.",
        H("Actual zero-cost normal quotient and marker descent"),Blocks(
            Paragraph(Text("G is any genuine group in Type u with its displayed instance gG; it need not be commutative, countable, topological or finitely generated. U:G->G and c:G->G->R are total, so all costs are finite real numbers. A proof h of RawCost U c supplies nonnegativity, zero diagonal, and c(a*s,b*t)+c(a*U(s),b*U(t))+c(a*U(U(s)),b*U(U(t)))=3c(a,b)+3c(s,t) for all a,b,s,t. A proof hs supplies symmetry c(a,b)=c(b,a). Neither U(1)=1, marker multiplicativity, periodicity, a triangle inequality, normality, representative independence nor a Hilbert realization is assumed.")),
            Paragraph(Text("In the formulas Z=zeroSubgroup(h,hs) is the actual subgroup with carrier {z | c(z,1)=0}, Q=QuotientGroup(G,Z) is the actual group quotient, mk denotes its canonical map and Member(z,Z) means subgroup membership. The instance zeroNormal supplies the group structure on Q. All appearances of quotientMarker and quotientCost use these same h and hs; no independently chosen equivalence relation is substituted.")),
            Entry("right_diff","The cost is its unit-based right difference",
                Base(OnG(Eqn(C(I("a"),I("b")),C(Mul(I("a"),Inv(I("b"))),D(1))),"a","b")),
                "Apply RawGroupZeroDrift.right_invariant at the actual inverse b inverse. This is a direct reuse of the right-shift theorem and requires no symmetry."),
            Entry("zero_coset","The actual zero coset has constant unit cost",
                Frame(OnG(Imp(Mem(I("z"),Z),Eqn(C(Mul(I("x"),I("z")),D(1)),C(I("x"),D(1)))),"x","z")),
                "Set F(t)=c(x*t,1) on the actual subgroup Z and m=inf(range F). This range is nonempty and bounded below by zero. For each n define T_n(w)=U^n(w)*(U^n(1)) inverse in Z: sync_iter and right_diff show its unit cost is zero. The full balance law at (x*s,1,w,1) becomes F(s*w)+F(s*T_1(w))+F(s*T_2(w))=3F(s). Every term belongs to the same coset and is at least m, hence F(s*w)<=3F(s)-2m. For fixed s and arbitrary t, take the actual element w=t inverse times s. Then (F(s)+2m)/3 is a lower bound for range F, yielding F(s)<=m. The infimum property gives the reverse inequality; compare s with 1. This establishes constancy using the balance law, without an assumed triangle inequality."),
            Entry("independent_representatives","Both zero representatives may change independently",
                Frame(OnG(Imp(Mem(I("z"),Z),Imp(Mem(I("w"),Z),
                    Eqn(C(Mul(I("a"),I("z")),Mul(I("b"),I("w"))),C(I("a"),I("b"))))),"a","b","z","w")),
                "The subgroup exists because single gives c(x*y,1)<=3(c(x,1)+c(y,1)) and inverse_budget preserves zero unit cost. Its normality follows by applying balance to background (a,a), increments (z,1): the nonnegative first term c(a*z,a) is zero, and right_diff identifies the conjugate cost. Thus b*(z*w inverse)*b inverse belongs to Z. The actual group identity (a*z)*(b*w) inverse=(a*b inverse)*(b*(z*w inverse)*b inverse), followed by zero_coset, proves the displayed equality."),
            Entry("zero_iff_class","Zero cost is equality in the actual quotient",
                Frame(OnG(Iff(Eqn(C(I("a"),I("b")),D(0)),Eqn(Mk(I("a")),Mk(I("b")))),"a","b")),
                "Mathlib's QuotientGroup.eq_iff_div_mem identifies equality of quotient classes with membership of the actual difference. The carrier definition and right_diff identify that membership with zero cost."),
            Entry("marker_classes","The total marker preserves quotient classes",
                Frame(OnG(Imp(Eqn(Mk(I("a")),Mk(I("b"))),Eqn(Mk(Call("U",I("a"))),Mk(Call("U",I("b"))))),"a","b")),
                "Apply sync_iter at one step, c(U(a),U(b))=c(a,b), and zero_iff_class in both directions. No point equality of representatives or marker homomorphism is inferred."),
            Entry("quotientMarker_mk","The descended marker has the exact representative equation",
                Frame(OnG(Eqn(Call("quotientMarker",I("h"),I("hs"),Mk(I("a"))),Mk(Call("U",I("a")))),"a")),
                "quotientMarker is Quotient.lift of a maps to mk(U(a)); marker_classes proves representative independence. It is total on the actual quotient Q, and the displayed equation is definitional."),
            Entry("quotientCost_mk","The descended cost has the exact representative equation",
                Frame(OnG(Eqn(Call("quotientCost",I("h"),I("hs"),Mk(I("a")),Mk(I("b"))),C(I("a"),I("b"))),"a","b")),
                "quotientCost is Quotient.lift2 of the original c. For related a,a prime and b,b prime, the actual elements a inverse times a prime and b inverse times b prime lie in Z. independent_representatives therefore supplies the required equality. The representative equation is definitional."),
            Entry("quotient_raw","The complete four-variable relation survives descent",
                Frame(Call("RawCost",Call("quotientMarker",I("h"),I("hs")),Call("quotientCost",I("h"),I("hs")))),
                "Quotient induction on both cost arguments proves nonnegativity, induction on one argument proves zero diagonal, and induction on all four arguments transports the entire balance identity. All operations are those of the actual normal subgroup quotient; the same total descended marker occurs throughout."),
            Entry("quotient_symmetric","The descended cost is symmetric",
                Frame(All("a",Q,All("b",Q,Eqn(Call("quotientCost",I("h"),I("hs"),I("a"),I("b")),Call("quotientCost",I("h"),I("hs"),I("b"),I("a")))))),
                "Induction on the two actual quotient classes reduces the statement to the original symmetry hs."),
            Entry("group19_2","Complete actual-group zero quotient theorem",GroupStatement(),
                "Choose f(g)=c(g,1), Z=zeroSubgroup(h,hs), its proved normality instance hn, V=quotientMarker(h,hs) and d=quotientCost(h,hs). This single theorem packages every displayed clause on the original arbitrary group. f is finite and nonnegative because it is real valued and h supplies its sign. hn supplies the genuine group structure used in every following quotient expression."),
            new DocumentBlock.Section(H("Source and scope"),Blocks(
                Paragraph(Text("This is Lemma 19.2 of AURIC_C133_UNANCHORED_MARKER_FINITE_POSITIVITY_BRIDGE, under Definition 19.1. The function clauses and simultaneous right invariance give (19.2) and (19.5); zeroSubgroup and zeroNormal establish the actual zero set and normality; independent_representatives gives (19.3); marker_classes, the two lift equations, quotient_raw and quotient_symmetric give the full descent; zero_iff_class gives (19.4). The finite inequality (19.6), synchronized normalized marker images (19.7), coset averaging (19.8) and constancy (19.9) are used in the subgroup and zero_coset derivations.")),
                Paragraph(Text("The proof directly reuses RawGroupZeroDrift.right_invariant and inverse_budget, RawUnanchoredReplication.single and sync_iter, and Mathlib's conditional infima, actual subgroup and quotient operations. The new inference is the harmonic constancy argument on each actual zero coset and its use in independent representative descent. No literature novelty is claimed.")),
                Paragraph(Text("No negative-type theorem, global Hilbert space, affine phase action, minimal-span uniqueness, or complete 19.4 classification is supplied here. The arbitrary marker on G is not asserted to be a homomorphism. Mathematical quotient descent supplies no physical preparation, effect, event, instrument, joint operation, empirical realization or physical time interface.")))))));

    private static Formula GroupStatement()
    {
        var g=I("G"); var z=I("Z"); var q=Quot(z);
        Formula f(Formula x) => Call("f",x);
        Formula rep=OnG(Imp(Mem(I("z"),z),Imp(Mem(I("w"),z),
            Eqn(C(Mul(I("a"),I("z")),Mul(I("b"),I("w"))),C(I("a"),I("b"))))),"a","b","z","w");
        Formula mark=OnG(Imp(Eqn(Mk(I("a")),Mk(I("b"))),Eqn(Mk(Call("U",I("a"))),Mk(Call("U",I("b"))))),"a","b");
        Formula lift=Ex("V",Arr(q,q),Ex("d",Arr(q,Arr(q,Real)),Conj(
            OnG(Eqn(Dst(Mk(I("a")),Mk(I("b"))),C(I("a"),I("b"))),"a","b"),
            OnG(Eqn(Call("V",Mk(I("a"))),Mk(Call("U",I("a")))),"a"),
            Call("RawCost",I("V"),I("d")),
            All("a",q,All("b",q,Eqn(Dst(I("a"),I("b")),Dst(I("b"),I("a"))))),
            OnG(Iff(Eqn(C(I("a"),I("b")),D(0)),Eqn(Mk(I("a")),Mk(I("b")))),"a","b"))));
        Formula quotient=Ex("Z",Call("Subgroup",g),And(
            OnG(Iff(Mem(I("z"),z),Eqn(f(I("z")),D(0))),"z"),
            Ex("hn",Call("Normal",z),Conj(rep,mark,lift))));
        return Frame(Ex("f",Arr(g,Real),Conj(
            OnG(Seq(D(0),Sp,Leq,Sp,f(I("g"))),"g"),
            OnG(Eqn(f(I("g")),C(I("g"),D(1))),"g"),
            OnG(Eqn(C(I("a"),I("b")),f(Mul(I("a"),Inv(I("b"))))),"a","b"),
            Eqn(f(D(1)),D(0)),OnG(Eqn(f(Inv(I("g"))),f(I("g"))),"g"),
            OnG(Eqn(C(Mul(I("a"),I("z")),Mul(I("b"),I("z"))),C(I("a"),I("b"))),"a","b","z"),quotient)));
    }
}
