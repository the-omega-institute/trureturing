using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fibers;

internal sealed class PhaseConditioningVariationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive probability margins bound the two symmetry-sensitive phase differences of the original five-mode transport.",
        H("Phase Variation and Positive Denominators"),
        Blocks(
            Paragraph(Text("The formulas use J(b) for the original open fiber. BottomMargin(b,k,e) means e<=mass(b,k,j) for every j in Fin 4. BottomProduct is the product of those four masses. WeightedIntegrable requires interval integrability of each of the five original weighted rates on [0,T]. InteriorPath and WholePathMargin impose their named conditions at every point of the closed interval. ResidualIntegral is the five component interval integral and AbsoluteRateIntegral is the integral of absolute alpha. These abbreviations retain every domain and integrability condition in the displayed statements.")),
            Describe.Lean(DescribeId.Create("denominator-margin"),
                DeclarationHandle.Create("D5/S3/Quantum/Fibers/PhaseConditioningVariation.denominator_margin"),
                H("The sampled denominator margin"), StatementSource.FromAuthor(Denominator()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The base is b=(X,Y,Z), r=1-Z, with 0<Z<1 and 0<X,Y<r. The probability order is (0,1,2,3,13); index 4 denotes mode 13. At an interior height k the bottom masses are p0=r-X-Y+k, p1=X-k, p3=Y-k and p13=k. Their total is r. The information I is their reciprocal sum. Q=XY(r-X-Y)+2XYk-rk squared equals I times their product. Expanding it instead as the sum of four positive triple products proves Q positive even when r-X-Y is negative. If these four sampled masses exceed or equal epsilon>0, each triple product exceeds or equals epsilon cubed, so Q exceeds or equals four times epsilon cubed. This sampled condition does not impose a margin on intervening controls."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("pointwise-gap-bound"),
                DeclarationHandle.Create("D5/S3/Quantum/Fibers/PhaseConditioningVariation.pointwise_gap_bound"),
                H("The two pointwise estimates"), StatementSource.FromAuthor(Pointwise()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For i=0 use leftMode=1, rightMode=3 and gap=X-Y. For i=1 use leftMode=0, rightMode=4 and gap=X+Y-r. The phase weight is the original signed direction (1,-1,0,-1,1) divided by probability times I. Reciprocal subtraction gives phaseDifference(w,i)=gap/(I*pLeft*pRight). Sedrakyan's form of Cauchy-Schwarz, applied directly to the four positive masses with constant numerators one, gives I*r>=16. The two masses in the denominator each exceed or equal epsilon. Multiplying these positive inequalities yields the bound with denominator 16*epsilon squared. Both signs of either gap and both exact walls are included."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("integral-variation-bound"),
                DeclarationHandle.Create("D5/S3/Quantum/Fibers/PhaseConditioningVariation.integral_variation_bound"),
                H("The actual integral residual"), StatementSource.FromAuthor(Integral()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let T>=0 be finite, k(t) stay in the original open fiber, and alpha(t) be interval integrable. Assume each original component w(k(t))*alpha(t) is interval integrable and that the same epsilon>0 bounds all four bottom masses along the entire closed time interval. The residual H is their actual interval integral. Subtracting the corresponding two integrals and applying the absolute integral inequality integrates the pointwise estimate against absolute alpha. The result applies to arbitrary integrable rates, without restricting controls to finite affine menus."))),
                DescribeRole.Theorem),
            Paragraph(Text("For each original absolutely continuous or continuous finite-piecewise-C1 control, set alpha=deriv chi. The original control fundamental theorem supplies interval integrability and identifies its integral with chi(T)-chi(0); the original transport-integrability result supplies every weighted component. Thus Vchi is the integral of absolute deriv chi and H is the original real residual, for every signed integer winding. The two bounds are absolute(H1-H3)<=absolute(X-Y)*r*Vchi/(16*epsilon squared) and absolute(H0-H13)<=absolute(X+Y-r)*r*Vchi/(16*epsilon squared). They concern the same actual controls and the original negative state-phase convention, with the middle phase fixed.")),
            Paragraph(Text("For a nonzero target difference Delta and a nonzero corresponding gap, division by the positive r and absolute gap gives Vchi>=16*epsilon squared*absolute(Delta)/(r*absolute(gap)). On an exact wall the matching difference is zero. For a compact target difference phi in the circle of period 2*pi, every real lift x satisfies norm(phi)<=absolute(x). That quotient norm equals the distance from x to the subgroup of integer multiples of 2*pi and is independent of the selected real lift. Replacing absolute(Delta) by that invariant distance gives a necessary bound for every realization, for either coordinate pair. A wrapped representative outside the nearest fundamental interval does not supply such a bound. These are costs in phase variation and specify no calibrated energy, speed or elapsed time.")))));

    private static Formula R => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Abs(Formula x) => Seq(Vert, x, Vert);
    private static Formula Id(string x) => F.Id(x);
    private static Formula All(Formula body, params (string Name, Formula Type)[] bs)
    {
        for (int i=bs.Length-1;i>=0;i--)
            body=Seq(Forall,Sp,Id(bs[i].Name),Colon,Sp,bs[i].Type,Comma,Sp,body);
        return body;
    }
    private static Formula Domain(Formula b, Formula k, Formula e, Formula body) => Seq(
        Call("ValidBase",b),Land,Sp,k,InMacro,Sp,Call("J",b),Land,Sp,D(0),Lt,e,Land,Sp,
        Call("BottomMargin",b,k,e),Rightarrow,Sp,body);
    private static Formula Denominator()
    {
        Formula b=Id("b"),k=Id("k"),e=Id("e");
        return Disp(All(Domain(b,k,e,Seq(Call("Q",b,k),Eq,Call("I",b,k),Call("BottomProduct",b,k),
            Land,Sp,D(4),e,Caret,Grp(D(3)),Le,Call("Q",b,k),Land,Sp,D(0),Lt,Call("Q",b,k))),
            ("b",Call("Base")),("k",R),("e",R)));
    }
    private static Formula Bound(Formula b,Formula e,Formula i) => new Formula.Fraction(
        Seq(Abs(Call("gap",b,i)),Open,D(1),Minus,Call("Z",b),Close),Seq(D(1,6),e,Caret,Grp(D(2))));
    private static Formula Pointwise()
    {
        Formula b=Id("b"),k=Id("k"),e=Id("e"),i=Id("i");
        return Disp(All(Domain(b,k,e,Seq(Abs(Call("phaseDifference",Call("phaseWeight",b,k),i)),Le,Bound(b,e,i))),
            ("b",Call("Base")),("k",R),("e",R),("i",Call("Fin",D(2)))));
    }
    private static Formula Integral()
    {
        Formula b=Id("b"),t=Id("T"),e=Id("e"),k=Id("k"),a=Id("a"),i=Id("i");
        Formula arrow=Seq(R,Rightarrow,Sp,R);
        return Disp(All(Seq(Call("ValidBase",b),Land,Sp,D(0),Le,Sp,t,Land,Sp,D(0),Lt,e,Land,Sp,
            Call("IntervalIntegrable",a,t),Land,Sp,Call("WeightedIntegrable",b,k,a,t),Land,Sp,
            Call("InteriorPath",b,k,t),Land,Sp,Call("WholePathMargin",b,k,e,t),Rightarrow,Sp,
            Abs(Call("phaseDifference",Call("ResidualIntegral",b,k,a,t),i)),Le,
            Bound(b,e,i),Call("AbsoluteRateIntegral",a,t)),
            ("b",Call("Base")),("T",R),("e",R),("k",arrow),("a",arrow),("i",Call("Fin",D(2)))));
    }
}
