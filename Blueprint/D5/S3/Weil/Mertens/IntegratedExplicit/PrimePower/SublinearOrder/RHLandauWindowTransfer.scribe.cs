using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder;

internal sealed class RHLandauWindowTransferDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHLandauWindowTransfer";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A uniform bound for actual zero sums supplies logarithmic-time harmonic Fourier cancellation.",
        H("Transfer of a uniform Landau sum bound"),
        Blocks(
            Paragraph(Text("Under the existing RiemannHypothesis interface use the inclusive positive cutoff T, analytic multiplicities m(gamma), harmonic weights a(gamma)=m(gamma) gamma/(1/4+gamma^2), W(T)=sum a(gamma), and normalized complex score Z(T,t). Write F(V,t) for the unweighted-with-multiplicity sum through V of exp(i gamma t).")),
            Describe.Lean(DescribeId.Create("harmonic-landau-window-deficit"), DeclarationHandle.Create(Owner + ".harmonic_landau_window_deficit"),
                H("Logarithmic-time deficit under a uniform actual-ordinate sum bound"), StatementSource.FromAuthor(DeficitBound()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Fix b>0 and C>0. The theorem assumes that for every real V>1 and nonzero real t, the norm of F(V,t) is bounded by C times the sum of V, exp(|t|/2)(1+|t|)^2, exp(|t|/2)(1+log V), and log V/|t|. Under this explicit hypothesis there is L>1 such that the displayed inequality holds for every T>=L and b/log T<=|t|<=log T.")),
                    Paragraph(Text("The paper-level source for the hypothesis is Gonek, A Formula of Landau and Mean Values of zeta(s), Theorem 1 equation (3), printed pp. 92–93. Its sum includes multiplicities. Divide by sqrt(x) under RH and set x=exp(|t|), using conjugation for negative times. The main term and nearest-prime-power error are bounded by a constant times V since Lambda(x)<=log x, the minimum in that error is at most V, and |t| exp(-|t|/2) is bounded. The two errors involving x become bounded by the two displayed exponential terms after enlarging C, and the near-1 error is at most log V/|t|. The Landau formula itself is a literature input beyond the current Lean proof.")),
                    Paragraph(Text("For sufficiently large T, log T<=q=T^(1/4), q>=1, q^4=T. On the stated time window and 1<V<=T, exp(|t|/2)<=q^2 and 1+|t|, 1+log V<=2q. The four terms of the assumed bound are at most T, 4T, 2T, T/b. Hence the two inclusive sums at V=T and V=3T/4 are each bounded by C(7+1/b)T. Their difference is the upper-band sum, with norm eventually at most T log T/(32 pi).")),
                    Paragraph(Text("The zero counting asymptotic supplies at least T log T/(16 pi) analytic multiplicity in (3T/4,T]. In that band the actual weights dominate m(gamma)/(2T). Decompose the weights on the entire cutoff into this retained profile and a pointwise nonnegative remainder. Since every phase has unit norm, the triangle inequality bounds the remainder norm by its mass. The retained profile therefore gives a raw score deficit of at least half the upper-band count divided by 2T, namely log T/(64 pi). Normalize using W(T)<=log(T)^2/(2 pi) to obtain the claimed deficit.")),
                    Paragraph(Text("The theorem extends the conditional pointwise estimate to times of order log T. With the previously proved short-time estimates and relative Fejer truncation, resolutions satisfying eta(T) log T tending to infinity can use this window. Smaller resolutions require longer-time arithmetic estimates. The paper-level uniform Landau premise remains an open formalization supplier."))), DescribeRole.Theorem))));

    private static Formula DeficitBound() => F.Disp(new Formula.Relation(
        F.Seq(F.D(1),F.Minus,F.Bar,Call("Z",F.Id("T"),F.Id("t")),F.Bar),
        FormulaRelationOperator.GreaterThanOrEqual,
        F.Seq(F.Frac,F.Grp(F.D(1)),F.Grp(Multiply(F.D(3,2),Call("log",F.Id("T")))))));
}
