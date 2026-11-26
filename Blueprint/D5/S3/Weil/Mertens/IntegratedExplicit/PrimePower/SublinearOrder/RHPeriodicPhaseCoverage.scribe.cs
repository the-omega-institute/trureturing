using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit.PrimePower.SublinearOrder;

internal sealed class RHPeriodicPhaseCoverageDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Weil/Mertens/IntegratedExplicit/PrimePower/SublinearOrder/RHPeriodicPhaseCoverage";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual short-window zero counts force uniform harmonic-weighted Fourier cancellation over a reciprocal-logarithmic range.",
        H("Periodic phase coverage of positive zeta zeros"),
        Blocks(
            Paragraph(Text("Assume RiemannHypothesis in the positive-ordinate spectrum interface. For the inclusive cutoff T, let a(gamma)=m(gamma) gamma/(1/4+gamma^2), W(T) be the sum of these weights, and Z(T,t) be the complex exponential score with weights a(gamma)/W(T). The multiplicity m is the analytic zero multiplicity.")),
            Describe.Lean(DescribeId.Create("harmonic-periodic-phase-deficit"), DeclarationHandle.Create(Owner + ".harmonic_periodic_phase_deficit"),
                H("Uniform score deficit from opposite phase arcs"), StatementSource.FromAuthor(DeficitBound()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("There exist L>1 and b>0 such that the inequality holds for every T>=L and 16 pi/T<=|t|<=b/log T. Let K>0 be furnished by the short-window lower count and take b=pi/(8K). For positive time tau=|t| set H=2 pi/tau, n=floor(T/(4H)), and k0=ceil(T/(2H)). The time inequalities imply 8H<=T, H/16>=K log T, and n>=T/(8H).")),
                    Paragraph(Text("For k=0,...,n-1 construct two families of half-open intervals. Their left endpoints are (k0+k)H and (k0+k)H+H/2, and both widths are H/16. Every interval lies in [T/2,T], and the intervals in either family are pairwise disjoint. Their phases lie within distance pi/8<1/2 of +1 and -1 respectively. As log(x)>=log(T)/2 for each left endpoint x and T>=4, the lower count gives at least H log(T)/(256 pi) zeros counted with multiplicity in each interval. Each weight satisfies a(gamma)>=m(gamma)/(2T) on [T/2,T]. Summing the disjoint intervals yields harmonic mass at least log(T)/(4096 pi) in each family.")),
                    Paragraph(Text("Project the unnormalized score onto its own unit direction u, choosing u=1 when the score vanishes. Every unit phase has projection at most 1. If the real part of u is nonnegative, the arc near -1 has projection at most 1/2. If it is negative, the arc near +1 has projection at most 1/2. Thus the unnormalized norm deficit is at least log(T)/(8192 pi). The two positive arc masses ensure W(T)>0, and the harmonic mass asymptotic gives W(T)<=(log T)^2/(2 pi) eventually. Dividing yields the displayed bound. Complex conjugation gives the same norm at negative time.")),
                    Paragraph(Text("For n-fold scores this pointwise deficit implies exponential suppression in n/log T throughout the stated window. The argument needs a counting lower bound on intervals of width H/16. The range beyond b/log T and its integrated contribution to the growing-cutoff Fejer limit remain open."))), DescribeRole.Theorem))));

    private static Formula DeficitBound() => F.Disp(new Formula.Relation(
        F.Seq(F.D(1),F.Minus,F.Bar,Call("Z",F.Id("T"),F.Id("t")),F.Bar),
        FormulaRelationOperator.GreaterThanOrEqual,
        F.Seq(F.Frac,F.Grp(F.D(1)),F.Grp(Multiply(F.D(4,0,9,6),Call("log",F.Id("T")))))));
}
