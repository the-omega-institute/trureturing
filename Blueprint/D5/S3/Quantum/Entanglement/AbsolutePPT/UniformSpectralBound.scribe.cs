using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.AbsolutePPT;

internal sealed class UniformSpectralBoundDocument : IScribeDocumentDefinition
{
    private static Formula Int(long n) => n < 0 ? new Formula.Negate(StrataLint.Scribe.DefinitionDsl.Num(-n)) : StrataLint.Scribe.DefinitionDsl.Num(n);
    private static Formula Id(string name) => F.Id(name);
    private static Formula R => Seq(Mathbb, Grp(Id("R")));
    private static Formula N => Seq(Mathbb, Grp(Id("N")));
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula Qualified(string owner, string name) => Seq(Id(owner), Dot, Id(name));
    private static Formula Call(string name, params Formula[] xs) => new Formula.Apply(name.Contains('.') ? Qualified(name.Split('.')[0], name.Split('.')[1]) : Id(name), [.. xs]);
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp, Parenthesized(Seq(Id(name), Colon, type)), Comma, Sp, body);
    private static Formula Imp(Formula p, Formula q) => Seq(Parenthesized(p), Rightarrow, Sp, q);
    private static Formula And(params Formula[] items) => Seq(items.SelectMany((f,i) => i==0 ? new[] {Parenthesized(f)} : new[] {Land, Sp, Parenthesized(f)}).ToArray());
    private static Formula Eq(Formula x, Formula y) => Seq(x, F.Eq, y);
    private static Formula Le(Formula x, Formula y) => Seq(x, Leq, Sp, y);
    private static Formula Add(params Formula[] xs) => Seq(xs.SelectMany((f,i) => i==0 ? new[] {f} : new[] {Plus, f}).ToArray());
    private static Formula Mul(Formula x, Formula y) => Seq(x, Cdot, Sp, y);
    private static Formula Pow(Formula x, int n) => new Formula.Power(Parenthesized(x), Int(n));
    private static Formula Frac(Formula x, Formula y) => new Formula.Fraction(x, y);
    private static Formula Arrow(Formula x, Formula y) => Seq(x, To, Sp, y);
    private static Formula Fin(Formula d) => Call("Fin", d);
    private static Formula Sum(string j, Formula ty, Formula body) => Seq(new Formula.Subscript(F.Sum, Seq(Id(j), Colon, ty)), Sp, body);
    private static Formula PSInt(Formula m) => Call("Matrix.PosSemidef", m);
    private static DocumentBlock Desc(string module, string name, string title, Formula f, string prose, DescribeRole role = DescribeRole.Definition, AssessedProvenance? provenance = null) =>
        Describe.Lean(DescribeId.Create("appt-"+module.ToLowerInvariant()+"-"+name.ToLowerInvariant().Replace("_","-").Replace(".","-")),
            DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/"+module+"."+name),
            H(title), StatementSource.FromAuthor(Disp(f)), provenance ?? AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);


    private static Formula Statement()
    {
        var k=Id("k");var l=Id("l");
        var fd=Fin(Mul(Int(3),Parenthesized(Add(Int(3),k))));
        var h=And(Call("Antitone",l),All("i",fd,Le(Int(0),Call("l",Id("i")))),
            Eq(Sum("i",fd,Call("l",Id("i"))),Int(1)),
            PSInt(Call("QutritSpectralReduction.K1",Call("QutritSpectralReduction.boundaryValues",k,l))));
        var nat=Parenthesized(Seq(Add(Int(3),k),Colon,N));
        var real=Parenthesized(Seq(nat,Colon,R));
        return All("k",N,Imp(Le(Int(8),k),All("l",Arrow(fd,R),Imp(h,
            Le(Sum("i",fd,Pow(Call("l",Id("i")),2)),Frac(Int(3),Mul(Int(8),real)))))));
    }
    private static Formula Sub(Formula x, Formula y) => Seq(x, Minus, y);
    private static Formula Smul(Formula x, Formula y) => Seq(x, Cdot, Sp, y);
    private static Formula At(string f, string i) => Call(f,Id(i));
    private static Formula Cast(Formula x) => Parenthesized(Seq(x,Colon,R));
    private static Formula Member(Formula x, Formula y) => Seq(x,InMacro,Sp,y);
    private static Formula SumS(string i, Formula f) => Seq(new Formula.Subscript(F.Sum,Member(Id(i),Id("s"))),Sp,f);
    private static Formula Good(Formula c, Formula x) => Call("SharedSpectral.spectralGood",c,x);
    private static Formula For((string,Formula)[] bs, Formula f)
    { for(var i=bs.Length-1;i>=0;i--) f=All(bs[i].Item1,bs[i].Item2,f); return f; }
    private static Formula Closure(Formula e, bool scale)
    {
        var h=And(Call("Good",Int(0)),For([("u",e),("v",e)],Imp(And(Call("Good",Id("u")),Call("Good",Id("v"))),Call("Good",Add(Id("u"),Id("v"))))));
        return scale?And(h,For([("t",R),("u",e)],Imp(And(Le(Int(0),Id("t")),Call("Good",Id("u"))),Call("Good",Smul(Id("t"),Id("u")))))):h;
    }
    private static Formula SharedStatement(string name)
    {
        var d=Id("d");var m=Id("m");var c=Id("c");var x=Id("x");var y=Id("y");var l=Id("l");var p=Id("p");
        var fd=Fin(d);var fm=Fin(m);var vec=Arrow(fd,R);
        var mass=Sum("i",fd,At("x","i"));var square=Sum("i",fd,Pow(At("x","i"),2));
        var shape=Le(square,Mul(Pow(c,2),Pow(mass,2)));
        var nonneg=And(Le(Int(0),c),Le(Int(0),mass));
        return name switch {
            "spectralGood_zero" => For([("d",N),("c",R)],Good(c,Parenthesized(Seq(Int(0),Colon,vec)))),
            "spectralGood_add" => For([("d",N),("c",R),("x",vec),("y",vec)],Imp(And(Good(c,x),Good(c,y)),Good(c,Add(x,y)))),
            "spectralGood_smul" => For([("d",N),("c",R),("t",R),("x",vec)],Imp(And(Le(Int(0),Id("t")),Good(c,x)),Good(c,Smul(Id("t"),x)))),
            "spectralGood_of_square" => For([("d",N),("c",R),("x",vec)],Imp(And(nonneg,shape),Good(c,x))),
            "spectralGood_square" => For([("d",N),("c",R),("x",vec)],Imp(And(nonneg,Good(c,x)),shape)),
            "sum_step" => For([("d",N),("j",N)],Imp(Le(Id("j"),d),Eq(Sum("k",fd,Call("SharedSpectral.step",d,Id("j"),Id("k"))),Cast(Id("j"))))),
            "sum_step_mul" => For([("d",N),("i",N),("j",N)],Imp(And(Le(Id("i"),d),Le(Id("j"),d)),Eq(Sum("k",fd,Mul(Call("SharedSpectral.step",d,Id("i"),Id("k")),Call("SharedSpectral.step",d,Id("j"),Id("k")))),Cast(Call("min",Id("i"),Id("j")))))),
            "mass_synth" => For([("d",N),("m",N),("p",Arrow(fm,N)),("x",Arrow(fm,R))],Imp(All("j",fm,Le(At("p","j"),d)),Eq(Sum("k",fd,Call("SharedSpectral.synth",p,x,Id("k"))),Sum("j",fm,Mul(At("x","j"),Cast(At("p","j"))))))),
            "square_synth" => For([("d",N),("m",N),("p",Arrow(fm,N)),("x",Arrow(fm,R))],Imp(All("j",fm,Le(At("p","j"),d)),Eq(Sum("k",fd,Pow(Call("SharedSpectral.synth",p,x,Id("k")),2)),Sum("i",fm,Sum("j",fm,Mul(Mul(At("x","i"),At("x","j")),Cast(Call("min",At("p","i"),At("p","j"))))))))),
            "spectralGap_nonneg" => For([("d",N),("l",vec)],Imp(And(Call("Antitone",l),All("j",fd,Le(Int(0),At("l","j")))),All("j",fd,Le(Int(0),Call("SharedSpectral.spectralGap",l,Id("j")))))),
            "gap_telescope" => For([("d",N),("l",vec),("a",N),("b",N)],Imp(Le(Id("a"),Id("b")),Eq(Seq(new Formula.Subscript(F.Sum,Member(Id("j"),Call("Ico",Id("a"),Id("b")))),Sp,Parenthesized(Sub(Call("SharedSpectral.extend",l,Id("j")),Call("SharedSpectral.extend",l,Add(Id("j"),Int(1)))))),Sub(Call("SharedSpectral.extend",l,Id("a")),Call("SharedSpectral.extend",l,Id("b")))))),
            "gap_reconstruct" => For([("d",N),("l",vec)],Eq(Sum("j",fd,Smul(Call("SharedSpectral.spectralGap",l,Id("j")),Call("SharedSpectral.step",d,Add(Call("val",Id("j")),Int(1))))),l)),
            "sum_mem_of_closed" => SumClosed(),
            "mixture_transfer" => Mixture(),
            _ => throw new System.ArgumentOutOfRangeException(nameof(name)) };
    }
    private static Formula SumClosed()
    {
        var i=Id("I");var e=Id("E");var type=Id("Type");
        return For([("I",type),("E",type)],Imp(Call("AddCommMonoid",e),For([("Good",Arrow(e,Id("Prop")))],Imp(Closure(e,false),For([("s",Call("Finset",i)),("f",Arrow(i,e))],Imp(All("i",i,Imp(Member(Id("i"),Id("s")),Call("Good",At("f","i")))),Call("Good",SumS("i",At("f","i")))))))));
    }
    private static Formula Mixture()
    {
        var i=Id("I");var e=Id("E");var type=Id("Type");var mass=SumS("j",At("x","j"));
        var h=And(Call("Nonempty",Id("s")),All("i",i,Imp(Member(Id("i"),Id("s")),Le(Int(0),At("x","i")))),All("i",i,Imp(Member(Id("i"),Id("s")),Call("Good",Add(Id("b"),Smul(mass,At("v","i")))))));
        return For([("I",type),("E",type)],Imp(And(Call("AddCommGroup",e),Call("Module",R,e)),For([("Good",Arrow(e,Id("Prop")))],Imp(Closure(e,true),For([("s",Call("Finset",i)),("x",Arrow(i,R)),("v",Arrow(i,e)),("b",e)],Imp(h,Call("Good",Add(Id("b"),SumS("i",Smul(At("x","i"),At("v","i")))))))))));
    }
    private static DocumentBlock Shared(string name, string title, string prose) => Desc("UniformSpectralBound",name,title,SharedStatement(name),prose,DescribeRole.Theorem);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The first qutrit spectral LMI yields the purity bound 3/(8n) for every n at least 11.",
        H("Uniform qutrit APPT spectral bound"),Blocks(
            Desc("UniformSpectralBound","uniform_spectral_bound","K1-only uniform purity estimate",Statement(),
                "Here n=3+k with k at least 8. An antitone nonnegative real spectrum of mass one is bounded using K1 alone. The argument extracts two boundary inequalities, reconstructs the spectrum from gaps, transfers a 33-ray cone certificate, and bounds every middle-coordinate mixture. The sum 3+k is formed in the natural numbers before its coercion to the reals; the quotient is real division.",DescribeRole.Theorem),
            Paragraph(Text("SharedSpectral.spectralGood(c,x) means that the Euclidean norm of x is at most c times its coordinate sum. step(d,j) is the vector with value one at k when k.val<j and zero otherwise. synth(p,x) is the sum over j of x(j) times step(d,p(j)). extend(l,a) equals l(a) for a<d and zero otherwise; spectralGap(l,j)=extend(l,j.val)-extend(l,j.val+1). Natural step lengths, minima and values are computed before real coercion. The original two-row proof uses these shared lemmas; the three-row proof also uses the norm, step-synthesis, gap and additive-closure lemmas. The general mixture lemma remains a supplier of the original proof.")),
            Shared("spectralGood_zero","The zero spectrum satisfies every cone bound","The dimension may be zero and c may have either sign."),
            Shared("spectralGood_add","Addition preserves a common cone bound","Both vectors have the same dimension and coefficient c."),
            Shared("spectralGood_smul","Nonnegative scaling preserves the cone bound","The scale t may vanish; c need not be nonnegative."),
            Shared("spectralGood_of_square","A squared estimate implies the norm estimate","The coefficient and total mass are nonnegative; no entrywise sign condition is imposed here."),
            Shared("spectralGood_square","A norm estimate implies the squared estimate","The coefficient and total mass are nonnegative."),
            Shared("sum_step","Mass of a step spectrum","The natural step length j lies between zero and d."),
            Shared("sum_step_mul","Gram kernel of two step spectra","The overlap is their natural minimum, coerced to the reals."),
            Shared("mass_synth","Mass of a synthesized spectrum","The finite list p consists of step lengths at most d. Coefficients x are arbitrary real numbers."),
            Shared("square_synth","Gram expansion of a synthesized spectrum","All d,m and real coefficient vectors are allowed, subject only to p(j) at most d."),
            Shared("spectralGap_nonneg","Ordered nonnegative spectra have nonnegative gaps","The last gap uses the extension by zero."),
            Shared("gap_telescope","Adjacent differences telescope on any natural interval","The interval is Ico(a,b); b need not be at most d because the extension is zero beyond d."),
            Shared("gap_reconstruct","All adjacent gaps reconstruct the spectrum","The identity holds for every real spectrum, with no ordering or sign hypothesis."),
            Shared("sum_mem_of_closed","Finite sums preserve an additive predicate","I and E are arbitrary types; E is an additive commutative monoid. The finite set s may be empty. Good contains zero and is closed under addition."),
            Shared("mixture_transfer","A fixed-base cone bound survives mixing","I and E are arbitrary types; E is an additive commutative group and real module. Good contains zero and is closed under addition and nonnegative real scaling. The finite set s is nonempty; all weights on s are nonnegative. Writing M for their sum, the premises are Good(b+M*v(i)) at every i in s. The proof treats M=0 without division and M>0 by barycentric weights."))));
}
