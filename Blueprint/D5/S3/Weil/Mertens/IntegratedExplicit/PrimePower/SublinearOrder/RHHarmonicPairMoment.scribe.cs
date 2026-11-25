using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder;

internal sealed class RHHarmonicPairMomentDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHHarmonicPairMoment";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual positive zero counting asymptotic supplies the central pair-moment hypothesis for harmonic weights.",
        H("Harmonic-weighted pair moments of positive zeta zeros"),
        Blocks(
            Paragraph(Text("Assume RiemannHypothesis as supplied to the existing positive-ordinate spectrum. For a positive cutoff T take all positive zeta zeros with ordinate gamma at most T, with analytic multiplicity m. Set a(gamma)=m gamma/(1/4+gamma^2), W=sum a, and w=a/W. Define P(k) as the ordered pair sum of w(i)w(j)(gamma(i)-gamma(j))^k.")),
            Describe.Lean(DescribeId.Create("harmonic-pair-ratio"), DeclarationHandle.Create(Owner + ".harmonic_pair_ratio"),
                H("Logarithmic normalized fourth-to-second moment ratio"), StatementSource.FromAuthor(Bound()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Eventually W>0, every w is nonnegative, sum w=1, P(2)>0, and the displayed bound holds. With c=1/(2 pi), Riemann-von Mangoldt gives N(T)-N(3T/4) at least c T log(T)/8 eventually. For ordinates in that upper band, the weight is at least m/(2T), so the retained band has total harmonic weight at least c log(T)/16. The existing harmonic mass limit gives W(T)<=c log(T)^2 and W(T/2)>=c log(T)^2/16 eventually. The normalized masses of the lower and upper bands are therefore at least 1/16 and 1/(16 log(T)). Differences between these bands have modulus at least T/4, yielding P(2)>=T^2/(4096 log(T)) from their contribution to the ordered pair sum. Since all ordinates lie in (0,T], termwise comparison gives P(4)<=T^2 P(2). Division yields the claimed ratio.")),
                    Paragraph(Text("For cutoffs T(n) tending to infinity with log(T(n))/n tending to zero, the ratio P(4)/(n P(2)^2) tends to zero. The existing central Gaussian score limit applies to the normalized actual harmonic-weighted score, using the scale sqrt(n P(2)/2). The Fejer principal integral also requires a compatible resolution and growing central window. Estimating intermediate phase peaks and the entire noncentral integral remains an arithmetic problem."))), DescribeRole.Theorem))));

    private static Formula I(string name) => F.Id(name);
    private static Formula Div(Formula a, Formula b) => F.Seq(F.Frac,F.Grp(a),F.Grp(b));
    private static Formula Sq(Formula a) => F.Seq(a,F.Caret,F.Grp(F.D(2)));
    private static Formula Bound() => F.Disp(new Formula.Relation(Div(Call("P",F.D(4)),Sq(Call("P",F.D(2)))),
        FormulaRelationOperator.LessThanOrEqual,Multiply(F.D(4,0,9,6),Call("log",I("T")))));
}
