using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class OriginalRowSaturationDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Foundation/OriginalRowSaturation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual collapse forces both ball saturations and whole-cone least confirmation", H("Actual collapse forces both ball saturations and whole-cone least confirmation"), Blocks(
            Paragraph(Text("V is an arbitrary finite dimensional real normed space, C its entire original pointed cone, and u the original linear unit. Assume C is closed and generating and u is strictly positive on nonzero C. K is the entire normalized base, P its entire extreme locus, and the effects and confirmers are the full original families, including u. EB3 parametrizes every whole exclusion, and PR exchanges only pure endpoints. All label neighborhoods use all P. No mixed PR, weakPair, RegularAnchor, global UF, prescribed saturation or matrix specialization is assumed.")),
            Describe.Lean(DescribeId.Create("actual-collapse-pure-edge-row"),
                DeclarationHandle.Create(Owner + "actual_collapse_pure_edge_row"), H("Actual collapse supplies the complete fixed-edge pure row"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Let original pure pn tend to p and let their entire exclusions tend to the actual pure singleton {q}. Then for every original pure s there is an effect e in the entire F(p) with e(q)=0 and e(s)=T(p,s). The pure input s=p is handled by actual minimum attainment on the original orthogonal edge. For s!=p, original strict exposure gives T(p,s)<1. Pure PR and the frozen full-input Lipschitz bound give convergence of the moving minimum. The same minimizing effect has a genuine zero in K by CommonOldExclusionConfirmation.minimizer_has_zero; that zero belongs to the whole moving exclusion. Full-effect norm control carries it into q, and a compact effect subsequence retains confirmation at p and attainment at s. No mixed PR or simultaneous minimizer for all pure s is claimed."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-row-saturation"),
                DeclarationHandle.Create(Owner + "original_row_saturation"), H("Both actual balls saturate under original Inj and unique A(p)"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Assume EB3, pure PR and Inj. Let p have exactly one full-zero confirmer ep, without restricting F(p), which still includes u. Take an arbitrary complete three-chart a of D(p), unit v with actual pure q=a(v), and an actual collapse pn->p, D(pn)->{q}. The theorem derives the full fixed-edge pure row from that collapse. It proves extensionBudget(a,w)=1 for every unit w, unit optimal budget in every chart of the actual D(q), and the coefficient-one-half law (1+inner(w,z))/2 for every mixed input in both whole balls. The same ep realizes T(p,x) for all mixed x in K and satisfies ep<=f on the entire C for every f in the full F(p). Original normal positivity is paid before constructing effects. Antipodal orthogonality forces the first scale, actual orthogonal points in D(q) force the second scale, and rho=1 in all directions then gives the whole-cone least property."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-nonunit-continuity"),
                DeclarationHandle.Create(Owner + "original_nonunit_continuity"), H("Nonunit unique-confirmation labels have whole-P local budgets"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Under the same original EB3, pure PR, Inj and singleton A(p) hypotheses, if an arbitrary complete three-chart a has extensionBudget(a,v)>1 at any unit v, then the whole-exclusion map is Hausdorff continuous at p. There is an open neighborhood U of p in all P and a finite positive B bounding extensionBudget in every complete chart and every unit direction at every s in U. Every discontinuity supplies an actual collapse, whose saturation contradicts the nonunit budget. The neighborhood conclusion consumes the actual all-P local-budget equivalence and never restricts U to P0."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-discontinuity-branches"),
                DeclarationHandle.Create(Owner + "original_discontinuity_branches"), H("Both Sigma branches and every actual endpoint refinement"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For every original p in Sigma=P\\R, either A(p) is not a singleton, or there is its unique ep such that all original charts at p have optimal budget one, T(p,x)=ep(x) on all K, and ep<=f on all C for every full original confirmer f. In the second branch every actual whole-ball collapse to any pure q forces optimal budget one in every whole chart of D(q). The first branch remains present, and the second unit-budget branch is not excluded. No actual collapse existence beyond the discontinuity witness, automatic UF, physical realization or novelty priority is asserted."))), DescribeRole.Theorem))));
}
