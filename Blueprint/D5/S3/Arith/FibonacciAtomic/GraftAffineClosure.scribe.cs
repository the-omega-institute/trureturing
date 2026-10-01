using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class GraftAffineClosureDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/GraftAffineClosure.";
    private static Formula V(string s) => s.EndsWith("'", StringComparison.Ordinal)
        ? Seq(F.Id(s[..^1]), Apos) : F.Id(s);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Pow(Formula f, Formula n) => Seq(f, Caret, Grp(n));
    private static Formula Pair(Formula a, Formula b) => Par(Seq(a, Comma, Sp, b));
    private static Formula EqOf(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula Add(Formula a, Formula b) => Seq(a, Sp, Plus, Sp, b);
    private static Formula Mul(Formula a, Formula b) => Seq(a, Sp, Times, Sp, b);
    private static Formula Sub(Formula a, Formula b) => Seq(a, Sp, Minus, Sp, b);
    private static Formula Neg(Formula a) => Seq(Minus, a);
    private static Formula And(params Formula[] fs) => Join(Land, fs);
    private static Formula Join(Formula token, Formula[] fs)
    {
        var items = new List<Formula>();
        for (int i = 0; i < fs.Length; i++)
        {
            if (i > 0) items.Add(Seq(Sp, token, Sp, RowBreak, Grp()));
            items.Add(Par(fs[i]));
        }
        return Seq(items.ToArray());
    }
    private static Formula Vars(string vars)
    {
        var xs = new List<Formula>();
        foreach (string s in vars.Split(','))
        {
            if (xs.Count > 0) xs.Add(Seq(Comma, Sp));
            xs.Add(V(s));
        }
        return Seq(xs.ToArray());
    }
    private static Formula All(string vars, Formula body) =>
        Seq(Forall, Sp, Vars(vars), Comma, Sp, body);
    private static Formula Some(string vars, Formula body) =>
        Seq(Exists, Sp, Vars(vars), Comma, Sp, body);
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));
    private static Formula IffOf(Formula a, Formula b) => Seq(Par(a), Sp, Leftrightarrow, Sp, Par(b));
    private static Formula LeOf(Formula a, Formula b) => Seq(a, Sp, Leq, Sp, b);
    private static Formula LtOf(Formula a, Formula b) => Seq(a, Sp, Lt, Sp, b);
    private static Formula InOf(Formula a, Formula b) => Seq(a, Sp, InMacro, Sp, b);
    private static Formula Gcd(Formula a, Formula b) => Call("gcd", a, b);
    private static Formula M(Formula k, Formula x) => Mul(Pow(V("M"), k), x);
    private static Formula Q(Formula x) => Call("q", x);
    private static Formula Rho(Formula x) => Call("rho", x);
    private static Formula O(Formula x) => Call("o", x);
    private static Formula T(Formula word, Formula x) => Call("T", word, x);
    private static Formula Word(Formula k, Formula a, Formula b) => Call("U", k, a, b);
    private static Formula N(Formula k, Formula x) => Q(M(k, x));
    private static Formula Psi(Formula p, Formula h, Formula e, Formula x) => Call("psi", p, h, e, x);
    private static Formula Mat(params Formula[] xs) => Seq(Begin, Grp(V("pmatrix")), xs[0], Amp, xs[1], RowBreak, xs[2], Amp, xs[3], End, Grp(V("pmatrix")));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Forward Fibonacci steps and a fixed complete graft realize exactly the observable translation ideal.",
        H("Fibonacci Graft Words and Complete Composition States"),
        Blocks(
            Paragraph(Text("Natural numbers include zero. Compositions v,w are pairs of natural numbers. "
                + "Unless specified otherwise, k,A,B,j are natural numbers, b,X,Y are integers, W is any finite "
                + "chronological word, and H is a positive natural modulus. A_H is ZMod(H). Residue vectors "
                + "and their scalar coefficients lie in A_H. The word alphabet has two named operations, "
                + "R and G; the empty word is allowed. All prefixes are also words, with no length, phase, "
                + "or expansion restriction. Current readouts include gcd(0,H)=H.")),
            Definition("step", "Fibonacci step", "R(v)=Mv=(v_2,v_1+v_2). The same formula acts on any additive pair."),
            Definition("quantity", "Quantity", "q(v)=2v_1+3v_2, over any semiring."),
            Definition("observe", "Consecutive quantity coordinates", "C(v)=(q(v),q(Mv))=(2v_1+3v_2,3v_1+5v_2)."),
            Definition("run", "Chronological forward words", "T(W,v) executes W from left to right. R sends v to Mv; G sends v to v+w. Both preserve actual nonnegative compositions. False denotes R and true denotes G."),
            Definition("readout", "Current gcd", "o(v)=gcd(q(v),H)."),
            Definition("behavior", "Common-word equivalence", "B(v,v') means o(T(W,v))=o(T(W,v')) for every identical finite word W. Each possible prefix is included as a word; no intermediate readout is assumed free in a query task."),
            Definition("residue", "Complete residue coordinates", "rho(v)=(v_1 mod H,v_2 mod H). res(m) is the scalar residue of m modulo H."),
            Definition("graftGcd", "Observable graft divisor", "d=gcd(gcd(w_1,w_2),H)."),
            Definition("graftSpace", "Translation space", "L_w={a rho(w)+b M rho(w): a,b in A_H}."),
            Definition("realizationWord", "Two graft blocks", "L=(H^2)!. U(k,A,B) is R^k,G^A,R^(L-1),G^B,R in chronological order. All exponents are nonnegative."),
            Definition("psi", "Translation-only local labels", "For prime p and natural h,e, r(X)=depth(p,h,X). If r(X)<e, psi(p,h,e,X) is Low(r(X)); otherwise it is Exact(X mod p^h). These are disjoint sum constructors, in N plus ZMod(p^h). The low label keeps only depth, with no unit coordinate. Multipliers are absent from the local tests."),
            Definition("Autonomous", "Autonomous representation", "A(H,w,E,deltaR,deltaG,oS) means E(Mv)=deltaR(E(v)), E(v+w)=deltaG(E(v)), and oS(E(v))=o(v) for every actual v. E maps the entire N^2 into an arbitrary state type S; its image, rather than a single-source reachable set, is counted."),
            Definition("atomicBlock", "Actual Fibonacci block", "a_j=M^j(1,0), for every natural j. Write alpha=(1,0). The Fibonacci sequence has F_0=0 and F_1=1."),
            Definition("matrixM", "Fibonacci matrix", "M is the integer matrix with rows (0,1) and (1,1)."),
            Definition("matrixC", "Quantity matrix", "C is the integer matrix with rows (2,3) and (3,5)."),
            Definition("blockMatrix", "Block columns", "D_j is the integer matrix with columns a_j and M a_j."),
            Definition("residueReadout", "Residue decoder", "oBar(u)=gcd(val(q(u)),H), where val is the least nonnegative residue representative."),
            Describe.Lean(DescribeId.Create("graft-affine-closure-result"),
                DeclarationHandle.Create(Prefix + "result"), H("Translation classification, realization, and minimal states"),
                StatementSource.FromAuthor(ResultFormula()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The first two groups quantify all natural p,h,e with p prime and e<=h, "
                        + "including h=0. The remaining group quantifies every H>0 and every actual graft w; the affine assertions also hold at H=1. "
                        + "In its local-axis clause, h_p=v_p(H) and e_p=v_p(d), for each prime p dividing H. "
                        + "The local depth is saturated at h; for nonzero integers v_p is the usual valuation. "
                        + "In the actual affine form, t is in N^2; elsewhere t,u,z are residue vectors or scalars. Cardinalities use finite cardinals when finite, and the image lower bound applies "
                        + "also to infinite state types. All conjunctions below are under those scopes.")),
                    Paragraph(Text("Low depth stays unchanged under p^e translations. Different low depths, "
                        + "or a low and a high label, are separated by the zero translation. For two distinct "
                        + "high residues, an integer multiple of p^e cancels the first; its gcd is p^h and "
                        + "the second gcd is smaller. This includes e=0 and e=h. These tests have no arbitrary "
                        + "scalar multiplication, so the low unit information required by multiplier tasks "
                        + "does not occur here.")),
                    Paragraph(Text("The invertible Fibonacci step permutes H^2 residue pairs, so its L-th "
                        + "power is the identity. The exact word U has terminal composition M^(k+L)v+A M^Lw+B Mw. "
                        + "Least nonnegative representatives of the two coefficients realize every translation "
                        + "in L_w, on the same actual source and with no inverse operation. The unimodular "
                        + "quantity matrix gives gcd(qw,qMw,H)=d. Bezout coefficients for these two quantities "
                        + "and H realize each scalar translation db. Thus the full common-word tests equal "
                        + "the integer translation tests at every k.")),
                    Paragraph(Text("At a prime axis, the cofactor d/p^e is invertible modulo the remaining "
                        + "power. Hence each p^e translation is induced by some global db and by a forward "
                        + "word. A difference at one prime already separates the whole gcd. Equality of all "
                        + "prime-axis labels conversely assembles equality of the full gcd. No simultaneous "
                        + "cancellation at other primes is needed. When d=H all observable translations "
                        + "vanish; when H=1 every current output is one.")),
                    Paragraph(Text("For w=a_j the two quantities are consecutive Fibonacci numbers. Their "
                        + "coprimality supplies Bezout coefficients even when neither quantity alone is a unit "
                        + "modulo H. The block is retained as its complete composition, never as its index "
                        + "or as a scalar addend. Different residue pairs have different quantity readings "
                        + "at time zero or one. A common U cancels the first reading, giving outputs H and "
                        + "a proper divisor of H. For alpha its coefficients are A=-c and B=c modulo H, "
                        + "where c=-q(M^kv). Both coefficients have representatives below H.")),
                    Paragraph(Text("Every residue pair has actual nonnegative representatives, and C is "
                        + "invertible modulo H, so every observation pair also occurs. Recording the complete "
                        + "composition residue gives an autonomous representation with exactly H^2 states. "
                        + "If any representation identifies different residues, its deterministic updates "
                        + "give equal outputs after their common separating word, a contradiction. The "
                        + "minimum image size is therefore H^2, including the one-state case H=1."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Definition(string name, string title, string prose) => Describe.Lean(
        DescribeId.Create("graft-affine-" + name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
        H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula ResultFormula()
    {
        Formula p=V("p"), h=V("h"), e=V("e"), x=V("X"), y=V("Y"), b=V("b"),
            hh=V("H"), w=V("w"), v=V("v"), vp=V("v'"), k=V("k"), a=V("A"), bb=V("B"),
            word=V("W"), t=V("t"), z=V("z"), d=V("d"), l=V("L"), j=V("j"), u=V("u");
        Formula r=Call("r",x), ph=Pow(p,h), pe=Pow(p,e), lw=Seq(V("L"),Underscore,Grp(w));
        Formula localTest=IffOf(All("b",EqOf(Gcd(Add(x,Mul(pe,b)),ph),Gcd(Add(y,Mul(pe,b)),ph))),
            EqOf(Psi(p,h,e,x),Psi(p,h,e,y)));
        Formula facts=And(LeOf(r,h),EqOf(Gcd(x,ph),Pow(p,r)),
            IffOf(EqOf(r,h),Seq(ph,Sp,Mid,Sp,x)),
            Imp(Seq(x,Sp,Neq,Sp,D(0)),EqOf(r,Call("min",Call("valuation",p,x),h))),
            IffOf(LeOf(e,r),Seq(pe,Sp,Mid,Sp,x)));
        Formula localHyp=And(Call("Prime",p),LeOf(e,h));
        Formula affine=All("W",Some("k",Some("t",And(InOf(Rho(t),lw),
            All("v",EqOf(T(word,v),Add(M(k,v),t)))))));
        Formula period=All("u",EqOf(M(l,u),u));
        Formula exact=All("k,A,B,v",EqOf(T(Word(k,a,bb),v),
            Add(Add(M(Add(k,l),v),Mul(a,M(l,w))),Mul(bb,M(D(1),w)))));
        Formula realize=All("k",All("t",Imp(InOf(t,lw),Some("W",All("v",
            EqOf(Rho(T(word,v)),Add(M(k,Rho(v)),t)))))));
        Formula ideal=And(EqOf(Gcd(Gcd(Q(w),Q(M(D(1),w))),hh),d),
            All("z",IffOf(Some("t",And(InOf(t,lw),EqOf(Q(t),z))),
                Some("c",EqOf(z,Mul(d,V("c")))))));
        Formula tests=All("v,v'",IffOf(Call("B",v,vp),All("k,b",
            EqOf(Gcd(Add(N(k,v),Mul(d,b)),hh),Gcd(Add(N(k,vp),Mul(d,b)),hh)))));
        Formula axes=All("v,v'",IffOf(Call("B",v,vp),All("p",Imp(
            And(Call("Prime",p),Seq(p,Sp,Mid,Sp,hh)),All("k",EqOf(
                Psi(p,Call("valuation",p,hh),Call("valuation",p,d),N(k,v)),
                Psi(p,Call("valuation",p,hh),Call("valuation",p,d),N(k,vp))))))));
        Formula observation=And(Call("Surjective",V("rho")),
            All("u",Some("v",And(LtOf(Seq(v,Underscore,Grp(D(1))),hh),
                LtOf(Seq(v,Underscore,Grp(D(2))),hh),EqOf(Rho(v),u)))),
            Call("Surjective",Seq(v,Sp,Mapsto,Sp,Mul(V("C"),Rho(v)))),
            All("v",And(EqOf(Mul(V("C"),v),M(D(4),v)),
                EqOf(Mul(V("C"),M(D(1),v)),M(D(1),Mul(V("C"),v))),
                EqOf(Mul(V("C"),Par(Add(v,w))),Add(Mul(V("C"),v),Mul(V("C"),w))))),
            All("k,v",EqOf(Seq(Par(M(k,Mul(V("C"),v))),Underscore,Grp(D(1))),N(k,v))),
            Call("A",hh,w,V("rho"),V("M"),Seq(v,Sp,Mapsto,Sp,Add(v,Rho(w))),V("oBar")),
            EqOf(Call("card",Pow(Call("ZMod",hh),D(2))),Pow(hh,D(2))),
            EqOf(Call("card",Call("image",V("rho"))),Pow(hh,D(2))),
            All("u",EqOf(Mul(V("C"),Pair(
                Sub(Mul(D(5),Seq(u,Underscore,Grp(D(1)))),Mul(D(3),Seq(u,Underscore,Grp(D(2))))),
                Add(Neg(Mul(D(3),Seq(u,Underscore,Grp(D(1))))),Mul(D(2),Seq(u,Underscore,Grp(D(2))))))),u)));
        Formula matrices=And(EqOf(Pow(V("M"),D(4)),V("C")),EqOf(Call("det",V("M")),Neg(D(1))),
            EqOf(Call("det",V("C")),D(1)),EqOf(Mul(V("C"),Mat(D(5),Neg(D(3)),Neg(D(3)),D(2))),V("I")),
            EqOf(Pow(V("M"),D(2)),Add(V("M"),V("I"))));
        Formula stable=All("t",Imp(InOf(t,lw),And(InOf(M(D(1),t),lw),
            InOf(Pair(Sub(Seq(t,Underscore,Grp(D(2))),Seq(t,Underscore,Grp(D(1)))),
                Seq(t,Underscore,Grp(D(1)))),lw))));
        Formula lengths=All("k,A,B",EqOf(Call("length",Word(k,a,bb)),Add(Add(Add(l,k),a),bb)));
        Formula endpoints=And(Imp(EqOf(d,hh),All("k,b,v",EqOf(Gcd(Add(N(k,v),Mul(d,b)),hh),O(M(k,v))))),
            Imp(EqOf(hh,D(1)),All("v",EqOf(O(v),D(1)))));
        Formula atomic=All("j",Imp(EqOf(w,Call("a",j)),And(
            EqOf(Q(w),Call("F",Add(j,D(3)))),EqOf(Q(M(D(1),w)),Call("F",Add(j,D(4)))),
            EqOf(Gcd(Seq(w,Underscore,Grp(D(1))),Seq(w,Underscore,Grp(D(2)))),D(1)),EqOf(d,D(1)),
            Imp(EqOf(j,D(0)),EqOf(w,Pair(D(1),D(0)))),
            Imp(LtOf(D(0),j),EqOf(w,Pair(Call("F",Sub(j,D(1))),Call("F",j)))),
            EqOf(Call("D",j),Pow(V("M"),j)),Call("Coprime",Q(w),Q(M(D(1),w))),
            EqOf(Call("det",Call("D",j)),Pow(Par(Neg(D(1))),j)),
            All("v,v'",IffOf(Call("B",v,vp),EqOf(Rho(v),Rho(vp)))),
            All("v,v'",Imp(Seq(Rho(v),Sp,Neq,Sp,Rho(vp)),Some("k,A,B",And(
                LeOf(k,D(1)),LtOf(a,hh),LtOf(bb,hh),
                Imp(EqOf(w,Pair(D(1),D(0))),And(EqOf(Call("res",a),Call("res",N(k,v))),
                    EqOf(Call("res",bb),Neg(Call("res",N(k,v)))))),
                LeOf(Call("length",Word(k,a,bb)),Add(Add(l,Mul(D(2),Par(Sub(hh,D(1))))),D(1))),
                EqOf(O(T(Word(k,a,bb),v)),hh),LtOf(O(T(Word(k,a,bb),vp)),hh))))),
            All("S,E,deltaR,deltaG,oS",Imp(Call("A",hh,w,V("E"),V("deltaR"),V("deltaG"),V("oS")),
                LeOf(Pow(hh,D(2)),Call("card",Call("image",V("E")))))))));
        return Disp(And(All("p,h,e",Imp(localHyp,All("X,Y",localTest))),
            All("p,h,e",Imp(localHyp,All("X",facts))),
            All("H",Imp(LtOf(D(0),hh),All("w",And(affine,period,exact,realize,ideal,tests,axes,
                observation,matrices,stable,lengths,endpoints,atomic))))));
    }
}
