using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder;

internal sealed class RHHarmonicPairMomentDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHHarmonicPairMoment";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Positive zero counting supplies the harmonic-weighted pair-moment hypothesis and a short-time phase deficit.",
        H("Harmonic-weighted pair moments of positive zeta zeros"),
        Blocks(
            Paragraph(Text("Assume RiemannHypothesis as supplied to the existing positive-ordinate spectrum. For a positive cutoff T take all positive zeta zeros with ordinate gamma at most T, with analytic multiplicity m. Set a(gamma)=m gamma/(1/4+gamma^2), W=sum a, and w=a/W. Define P(k) as the ordered pair sum of w(i)w(j)(gamma(i)-gamma(j))^k.")),
            Describe.Lean(DescribeId.Create("harmonic-pair-ratio"), DeclarationHandle.Create(Owner + ".harmonic_pair_ratio"),
                H("Logarithmic normalized fourth-to-second moment ratio"), StatementSource.FromAuthor(Bound()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Eventually W>0, every w is nonnegative, sum w=1, P(2)>0, and the displayed bound holds. With c=1/(2 pi), Riemann-von Mangoldt gives N(T)-N(3T/4) at least c T log(T)/8 eventually. For ordinates in that upper band, the weight is at least m/(2T), so the retained band has total harmonic weight at least c log(T)/16. The existing harmonic mass limit gives W(T)<=c log(T)^2 and W(T/2)>=c log(T)^2/16 eventually. The normalized masses of the lower and upper bands are therefore at least 1/16 and 1/(16 log(T)). Differences between these bands have modulus at least T/4, yielding P(2)>=T^2/(4096 log(T)) from their contribution to the ordered pair sum. Since all ordinates lie in (0,T], termwise comparison gives P(4)<=T^2 P(2). Division yields the claimed ratio.")),
                    Paragraph(Text("For cutoffs T(n) tending to infinity with log(T(n))/n tending to zero, the ratio P(4)/(n P(2)^2) tends to zero. The existing central Gaussian score limit applies to the normalized actual harmonic-weighted score, using the scale sqrt(n P(2)/2). The Fejer principal integral also requires a compatible resolution and growing central window. The full noncentral integral still requires further estimates."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("harmonic-reciprocal-time-deficit"), DeclarationHandle.Create(Owner + ".harmonic_reciprocal_time_deficit"),
                H("Uniform harmonic-weighted score deficit on the short noncentral range"),
                StatementSource.FromAuthor(DeficitBound()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Under the same RH interface, there is L>1 such that for every T>=L and 1/T<=|t|<=1/L the displayed inequality holds. Here Z(T,t) is the normalized complex exponential score of the actual inclusive cutoff T. Let X=1/|t|. The shared pair-moment estimate gives P(2) at X at least X^2/(4096 log X) and P(4) at X at most X^2 P(2). The global cosine quartic remainder and X^2 t^2=1 give a squared-score deficit at X at least 1/(16384 log X). Nonnegativity of (1-|Z(X,t)|)^2 therefore gives the norm deficit at least 1/(32768 log X).")),
                    Paragraph(Text("The finite sum through T splits into the retained contribution through X and the omitted positive-weight tail. Its norm is bounded by the norm of the retained sum plus the tail weight, at the same time t. Consequently W(T)(1-|Z(T,t)|)>=W(X)(1-|Z(X,t)|). With c=1/(2 pi), the harmonic mass bounds give W(X)>=c log(X)^2/16 and W(T)<=c log(T)^2. Combining proves the displayed estimate. For fixed 0<delta<1 it yields a deficit of at least delta/(524288 log T) on 1/T<=|t|<=T^(-delta), provided T is large enough. This argument uses analytic multiplicities and does not require distinct-frequency spacing beyond the given cutoff interface. Larger times and the remaining integrated noncentral peak estimate remain open."))), DescribeRole.Theorem))));

    private static Formula I(string name) => F.Id(name);
    private static Formula Div(Formula a, Formula b) => F.Seq(F.Frac,F.Grp(a),F.Grp(b));
    private static Formula Sq(Formula a) => F.Seq(a,F.Caret,F.Grp(F.D(2)));
    private static Formula Bound() => F.Disp(new Formula.Relation(Div(Call("P",F.D(4)),Sq(Call("P",F.D(2)))),
        FormulaRelationOperator.LessThanOrEqual,Multiply(F.D(4,0,9,6),Call("log",I("T")))));
    private static Formula DeficitBound() => F.Disp(new Formula.Relation(
        F.Seq(F.D(1),F.Minus,F.Bar,Call("Z",I("T"),I("t")),F.Bar),
        FormulaRelationOperator.GreaterThanOrEqual,
        Div(Call("log",Div(F.D(1),F.Seq(F.Bar,I("t"),F.Bar))),
            Multiply(F.D(5,2,4,2,8,8),Sq(Call("log",I("T")))))));
}
