using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle;

internal sealed class ThreeNegativeEqualOuterSourceBridgeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Circle/ThreeNegativeEqualOuterSourceBridge.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Consumed publication of three existing ThreeBitSource facts across the module boundary.",
        H("Source facts for the equal-outer marked joint lift"),
        Blocks(
            Paragraph(Text("This module publicly re-exports three private ThreeBitSource facts consumed by ThreeNegativeEqualOuterJointLift. Each proof directly applies the corresponding existing fact; this publication adds no independent mathematical result or novelty claim.")),
            Describe.Lean(DescribeId.Create("equal-outer-source-zero"),
                DeclarationHandle.Create(Prefix + "source_zero"),
                H("Integer total zero"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural k,t with 3<=k, the sum over i<k of centered(modulus(k),2^i*t) is the integer zero. The bridge re-exports ThreeBitSource.source_zero for the full physical source cycle."))),
                DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("equal-outer-actual-source-chains"),
                DeclarationHandle.Create(Prefix + "actual_source_chains"),
                H("The actual three source chains"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For natural x,y,z with 0<x, 0<y and 2<=z, put P=2^x, Q=2^y, R=2^z, N=modulus(x+y+z), u=1+P+PQ, v=1+R+RP and w=1+Q+QR. The re-export retains the bounds 1<=u,v,w<N, the identities Ru=N+v, Qv=N+w and Pw=N+u, and all three indexed formulas for the actual centered source: each positive ladder ends at its specified negative half-difference. It directly applies ThreeBitSource.actual_source_chains without changing its hypotheses or ranges."))),
                DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("equal-outer-physical-schedule"),
                DeclarationHandle.Create(Prefix + "physical_schedule"),
                H("The consumed physical schedule criterion"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any label type and integer increment function f, the word F,av,Q,aw,G,au satisfies InStrip(f,C,0) when it permutes the given labels, its three marked increments are -Av,-Aw,-Au, Av and Aw are nonnegative, Au lies in [0,C], all increments in F,Q,G are nonnegative, the mass of F lies in [Av,C], the height after F,av,Q lies in [Aw,C], and the full label sum is zero. The bridge directly applies ThreeBitSource.physical_schedule; the joint lift supplies these physical inventory and seam hypotheses."))),
                DescribeRole.Lemma)), []));
}
