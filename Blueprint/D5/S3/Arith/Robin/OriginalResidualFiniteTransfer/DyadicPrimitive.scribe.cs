using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.OriginalResidualFiniteTransfer;

internal sealed class DyadicPrimitiveDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/Robin/OriginalResidualFiniteTransfer/DyadicPrimitive.";
    private static DocumentBlock Definition(string name, string title, string text) =>
        Describe.Lean(DescribeId.Create("dyadic-primitive-" + name),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(text))), DescribeRole.Definition);
    private static DocumentBlock Theorem(string name, string title, Formula formula, string text) =>
        Describe.Lean(DescribeId.Create("dyadic-primitive-" + name.Replace('_', '-')),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(text))), DescribeRole.Theorem);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original two periodic primitives admit a joint folded range for every real second coefficient and arbitrary signed block weights.",
        H("Joint Dyadic Primitive Range"),
        Blocks(
            Paragraph(Text("Write P(d,m)=r*(r-d)/(2*d), where r=m mod d, for the original "
                + "periodic primitive, and phi(d,m)=P(d,m+1)-P(d,m). Put "
                + "s(d,m)=min(m mod (2*d),2*d-(m mod (2*d))). For d>0, s lies in [0,d]. "
                + "The two residue halves and their common seam use these original remainders.")),
            Definition("radius", "The joint radius",
                "For natural d and real A,B, R(d,A,B)=d*(A-B)^2/(8*(2*A-B)) if B<=0; "
                + "otherwise R=d*A^2/(8*(2*A-B)) if B<A; otherwise R=d*B/8. "
                + "The last branch never divides by 2*A-B. With A>0 these formulas agree at B=0 and B=A."),
            Definition("midpoint", "The enclosing midpoint",
                "For natural d and real A,B, c(d,A,B)=-d*(A-B)^2/(8*(2*A-B)) if B<=0; "
                + "otherwise c=d*B/8-d*(A-B)^2/(8*(2*A-B)) if B<A; otherwise c=d*B/8."),
            Theorem("folded_identity", "The actual folded-residue identity", FoldedFormula(),
                "For every natural d>0,m and all real A,B, the actual combination "
                + "A*P(d,m)-B*P(2*d,m) equals (2*A-B)*s(d,m)^2/(4*d)-(A-B)*s(d,m)/2. "
                + "No sign condition is imposed on either coefficient in this identity."),
            Theorem("primitive_range", "All-real-coefficient primitive range", RangeFormula(),
                "For every natural d>0,m, real A>0 and arbitrary real B, the absolute difference "
                + "between A*P(d,m)-B*P(2*d,m) and c(d,A,B) is at most R(d,A,B). "
                + "For B<=0 the folded quadratic lies between -d*(A-B)^2/(4*(2*A-B)) and zero. "
                + "For 0<=B<=A it lies between that lower value and d*B/4. "
                + "For B>=A it lies between zero and d*B/4. The last argument remains valid at "
                + "B=2*A and beyond, without a quadratic-vertex denominator."),
            Theorem("centered_pair_bound", "Joint signed block variation bound", PairFormula(),
                "For all natural N,d>0, every signed real sequence b, real A>0 and arbitrary real B, "
                + "the joint centered block sum is bounded by R(d,A,B)*V(N,b). "
                + "Here V(N,b)=abs(b(N))+abs(b(2*N-1))+sum(N<=m<2*N-1,abs(b(m+1)-b(m))). "
                + "The original shared summation-by-parts argument cancels c before taking absolute "
                + "values, retaining both zero-extension jumps. It also covers N=1, with two endpoint "
                + "payments for the same single coefficient, and requires no vanishing moments. "
                + "At d=1 the first centered kernel vanishes exactly. These finite estimates do not "
                + "assert signed MAIN, strict Robin above 5040 or RH."))));

    private static Formula Naturals => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Twice(Formula x) => Seq(D(2), Cdot, Sp, x);
    private static Formula Joint(Formula d, Formula a, Formula b, Formula m) =>
        Seq(a, Cdot, Sp, Call("P", d, m), Minus, b, Cdot, Sp, Call("P", Twice(d), m));
    private static Formula FoldedFormula()
    {
        var d=F.Id("d"); var m=F.Id("m"); var a=F.Id("A"); var b=F.Id("B");
        var s=Call("s",d,m);
        return Disp(Seq(Forall,Sp,d,Comma,m,InMacro,Sp,Naturals,Comma,
            Forall,Sp,a,Comma,b,InMacro,Sp,Reals,Comma,D(0),Lt,Sp,d,Rightarrow,Sp,
            Joint(d,a,b,m),Eq,Sp,
            new Formula.Fraction(Seq(Open,Twice(a),Minus,b,Close,Cdot,Sp,new Formula.Power(s,D(2))),Seq(D(4),Cdot,Sp,d)),
            Minus,new Formula.Fraction(Seq(Open,a,Minus,b,Close,Cdot,Sp,s),D(2))));
    }
    private static Formula RangeFormula()
    {
        var d=F.Id("d"); var m=F.Id("m"); var a=F.Id("A"); var b=F.Id("B");
        return Disp(Seq(Forall,Sp,d,Comma,m,InMacro,Sp,Naturals,Comma,
            Forall,Sp,a,Comma,b,InMacro,Sp,Reals,Comma,D(0),Lt,Sp,d,Land,Sp,D(0),Lt,Sp,a,
            Rightarrow,Sp,Lvert,Sp,Joint(d,a,b,m),Minus,Call("c",d,a,b),Rvert,Sp,Le,Sp,Call("R",d,a,b)));
    }
    private static Formula PairFormula()
    {
        var n=F.Id("N"); var d=F.Id("d"); var m=F.Id("m"); var a=F.Id("A"); var b=F.Id("B"); var w=F.Id("b");
        Formula sum=Seq(F.Sum,Underscore,Grp(m,Eq,Sp,n),Caret,Grp(Twice(n),Minus,D(1)),Sp,
            Call("b",m),Cdot,Sp,Open,a,Cdot,Sp,Call("phi",d,m),Minus,b,Cdot,Sp,Call("phi",Twice(d),m),Close);
        return Disp(Seq(Forall,Sp,n,Comma,d,InMacro,Sp,Naturals,Comma,
            Forall,Sp,w,InMacro,Sp,new Formula.Power(Reals,Naturals),Comma,
            Forall,Sp,a,Comma,b,InMacro,Sp,Reals,Comma,D(0),Lt,Sp,n,Land,Sp,D(0),Lt,Sp,d,Land,Sp,
            D(0),Lt,Sp,a,Rightarrow,Sp,Lvert,Sp,sum,Rvert,Sp,Le,Sp,Call("R",d,a,b),Cdot,Sp,Call("V",n,w)));
    }
}
