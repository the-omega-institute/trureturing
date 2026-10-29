using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Probability;

internal sealed class NativeCommandGridMaximalDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform fourth maxima on normal grid windows of the actual native command triple.",
        H("Fourth maxima on the native command grid"),
        Blocks(
            Paragraph(Text("A raw model B determines the original command triple (a,b,j), where j is its chronological area. Put delta=1/n squared. A complete word is a function from Fin(n cubed) to the four sign pairs. Every word has mass 4 to the power minus n cubed, including every unused suffix after a wall contact.")),
            Paragraph(Text("gridFourthMaximum(B,n,w,k,m) is the maximum, over the nonempty set of integers j from zero through m, of the fourth power of the norm of command(B,n,w,(k+j)delta)-command(B,n,w,k delta). The norm is the maximum coordinate norm on the joint triple. gridFourthExpectation is its sum over all complete words multiplied by their original common mass.")),
            Describe.Lean(
                DescribeId.Create("actual-grid-maximal-estimate"),
                DeclarationHandle.Create("D5/S3/Analytic/Probability/NativeCommandGridMaximal.actual_grid_maximal_estimate"),
                H("A common fourth bound for every normal grid window"),
                StatementSource.FromAuthor(Disp(Statement())),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The finite nonempty maximum includes j=0. The condition k+m<=n cubed keeps every observed point on the normal grid; the distinct forced final upper-wall leg is excluded. The same constant depends only on B, independently of n, k, m, the word and whether the path survives. The case m=0 has expectation zero.")),
                    Paragraph(Text("From each alive endpoint, take the full original increment and its chronological area increment; after the first endpoint outside the height walls, hold this auxiliary endpoint chain fixed. The actual stopped command at any normal grid point differs from this chain by at most the length of one chord. The clipping parameter is the original sign-dependent first-wall fraction, and the actual path holds at that clipped point.")),
                    Paragraph(Text("Compactness in height and periodicity in phase bound the original drift and noise coefficients. Consequently there are nonnegative constants D and J such that the four-sign mean endpoint increment has norm at most D delta, every endpoint jump has norm at most J sqrt(delta), and each full chord has Lipschitz bound J sqrt(delta) in its interpolation parameter. The area-coordinate mean uses the original product of the two horizontal increments; it is bounded by the same coefficient estimates.")),
                    Paragraph(Text("Use the finite complete-word history law with constant innovation mass one fourth. Its exact next-prefix conditional expectation shows that the endpoint chain minus its accumulated four-sign means is a martingale. For any window, its centered coordinate jumps have absolute value at most (J+D)sqrt(delta). The finite even maximal inequality at exponent four bounds the expected fourth coordinate maximum by 262144 times (J+D) to the fourth power times T squared, where T=m delta.")),
                    Paragraph(Text("The accumulated mean over the window has norm at most D T. The endpoint comparison contributes at most 2 J sqrt(delta) to an increment. The five-term fourth-power sum bound combines the three centered coordinate maxima, 3 D T and this comparison error. For m positive, delta<=T; for T<=2, T to the fourth power is at most 4 T squared. Thus C=125 times the sum of 3 times 262144 times (J+D) to the fourth power, 324 D to the fourth power and 16 J to the fourth power suffices.")),
                    Paragraph(Text("The expectation is exactly the original finite complete-word sum. No survival conditioning or change of word masses is used. Arbitrary real windows, the fourth estimate on all scales and tightness in continuous path space require additional arguments."))),
                DescribeRole.Theorem))));

    private static Formula V(string x) => F.Id(x);
    private static Formula D(int x) => new Formula.Number(x);
    private static Formula R => Seq(Mathbb,Grp(V("R")));
    private static Formula N => Seq(Mathbb,Grp(V("N")));
    private static Formula Par(Formula x) => Seq(Open,x,Close);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname,Grp(V(name))),[..args]);
    private static Formula All(string x, Formula type, Formula body) =>
        Seq(Forall,Sp,V(x),Colon,Sp,type,Comma,Sp,body);
    private static Formula Some(string x, Formula type, Formula body) =>
        Seq(Exists,Sp,V(x),Colon,Sp,type,Comma,Sp,body);
    private static Formula Le(Formula x, Formula y) =>
        new Formula.Relation(x,FormulaRelationOperator.LessThanOrEqual,y);
    private static Formula Lt(Formula x, Formula y) =>
        new Formula.Relation(x,FormulaRelationOperator.LessThan,y);
    private static Formula And(Formula x, Formula y) =>
        new Formula.Logic(Par(x),FormulaLogicOperator.And,Par(y));
    private static Formula Imp(Formula x, Formula y) =>
        new Formula.Logic(Par(x),FormulaLogicOperator.Implies,Par(y));

    private static Formula Statement()
    {
        var B=V("B"); var n=V("n"); var k=V("k"); var m=V("m"); var C=V("C");
        var T=Multiply(m,Call("mesh",n));
        var estimate=Le(Call("gridFourthExpectation",B,n,k,m),
            Multiply(C,new Formula.Power(T,D(2))));
        var window=Imp(Le(Add(k,m),new Formula.Power(n,D(3))),
            Imp(Le(T,D(2)),estimate));
        return All("B",V("Model"),Some("C",R,And(Le(D(0),C),
            All("n",N,Imp(Lt(D(0),n),All("k",N,All("m",N,window)))))));
    }
}
