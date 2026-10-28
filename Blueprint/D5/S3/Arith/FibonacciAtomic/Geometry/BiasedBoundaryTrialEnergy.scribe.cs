using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Geometry;

internal sealed class BiasedBoundaryTrialEnergyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every function constant on an actual biased stopping partition has a finite unit-edge extension and a strict free-root Rayleigh bound.",
        H("Stopping-Cylinder Trial Energy"), Blocks(
            Describe.Lean(DescribeId.Create("biasedboundarytrialenergy-extension"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Geometry/BiasedBoundaryTrialEnergy.actual_stopping_trial_energy"),
                H("The Original Single-Edge Trial Extension"),
                StatementSource.FromAuthor(TrialFormula()), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Fix any real threshold t strictly between zero and one. A(t) is the first actual biased mass crossing, with equality included as a stopping event. Vt(t) is the span of its cylinder indicators in the original G=L2(M). The coefficients x(p)=atomMean(p)(F) are the actual normalized cylinder integrals of F.")),
                    Paragraph(Text("The orthogonal cylinder projection fixes each F in Vt(t), so F is the sum of x(p) times its actual cylinder indicators. Put the coefficient x(p) on the single original edge p for every p in A(t), with every other edge coefficient zero and root value zero. Applying J to this finite increment sum gives F. The squared increment norm is the sum of x(p) squared.")),
                    Paragraph(Text("The actual partition norm identity and its constant conditional pullbacks give the boundary squared norm as the sum of mass(p) times x(p) squared. Each actual stopping mass is strictly greater than b*t. If F is nonzero, at least one coefficient is nonzero, so the weighted sum is strictly greater than b*t times the squared increment norm.")),
                    Paragraph(Text("This extension places F in the original free-root domain D. The attained original minimum energy is at most the squared norm of this extension, hence strictly less than the boundary squared norm divided by b*t for every nonzero F. Equality of the chosen extension energy with the minimum is not asserted. The statement includes zero F, with the strict conclusions restricted exactly to nonzero F.")),
                    Paragraph(Text("Here J, M, D and energy are the original biased trace, measure, free-root domain and infimum over all original extensions. The same inequality therefore applies to the centered trial subspace. The polar range identifications, spectral cutoff dimensions and resulting global eigenvalue counts require their further operator and variational arguments."))), DescribeRole.Theorem))));

    private static Formula V(string s) => F.Id(s);
    private static Formula Call(string s, params Formula[] xs) => new Formula.Apply(Seq(Operatorname, Grp(V(s))), [.. xs]);
    private static Formula Par(Formula x) => Seq(Open,x,Close);
    private static Formula All(string s, Formula type, Formula x) => Seq(Forall,Sp,V(s),Colon,Sp,type,Comma,Sp,Par(x));
    private static Formula Sq(Formula x) => Seq(Par(x),Caret,Grp(D(2)));
    private static Formula SqNorm(Formula x) => Sq(Seq(Vert,Sp,x,Sp,Vert));
    private static Formula And(params Formula[] xs) => Seq([.. xs.SelectMany((x,i) =>
        i == 0 ? new[] { Par(x) } : new[] { Land, Sp, Par(x) })]);
    private static Formula TrialFormula()
    {
        Formula t=V("t"), f=V("F"), z=V("z"), p=V("p");
        Formula fv=Call("val",f), tv=Call("val",t), pv=Call("val",p);
        Formula coeff=Call("atomMean",p,fv);
        Formula SumA(Formula x) => Seq(Sum,Underscore,Grp(Seq(p,InMacro,Sp,Call("A",t))),Sp,Par(x));
        Formula bt=Par(Seq(V("b"),Cdot,Sp,tv));
        Formula bound=Seq(bt,Caret,Grp(Seq(Minus,D(1))),Cdot,Sp,SqNorm(fv));
        Formula strict=Seq(fv,Neq,Sp,D(0),Implies,Sp,Par(And(
            Seq(bt,Cdot,Sp,SqNorm(z),Lt,Sp,SqNorm(fv)),
            Seq(SqNorm(z),Lt,Sp,bound),
            Seq(Call("energy",fv),Lt,Sp,bound))));
        Formula body=And(
            Seq(z,Eq,SumA(Call("single",D(2),p,coeff))),
            Seq(Call("J",z),Eq,fv),
            Seq(SqNorm(z),Eq,SumA(Sq(coeff))),
            Seq(fv,InMacro,Sp,V("D")),
            Seq(SqNorm(fv),Eq,SumA(Seq(Call("measureReal",V("M"),Call("cylinder",pv)),Cdot,Sp,Sq(coeff)))),
            Seq(Call("energy",fv),Leq,Sp,SqNorm(z)),strict);
        return All("t",Call("Threshold"),All("F",Call("Vt",t),
            Seq(Exists,Sp,z,Colon,Sp,Call("H"),Comma,Sp,Par(body))));
    }
}
