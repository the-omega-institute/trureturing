using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class OriginalComparisonTopologyDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Foundation/OriginalComparisonTopology.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform original comparison estimates and bounded-budget noncollapse",
        H("Uniform original comparison estimates and bounded-budget noncollapse"), Blocks(
            Paragraph(Text("V is an arbitrary finite dimensional real normed space, C a pointed cone, and u its original linear unit. Where stated, C is closed and generating and u is strictly positive on nonzero C. K is the entire normalized base and P its entire extreme locus. All original linear effects between zero and u are retained; the full confirming family F(p) includes u. Pure reciprocity exchanges only two pure endpoints. No mixed reciprocity, matrix specialization, weakPair, unit-width assumption or global uniform-fiber premise is used.")),
            Describe.Lean(DescribeId.Create("original-uniform-comparison"), DeclarationHandle.Create(Owner + "original_uniform_comparison"),
                H("All mixed inputs of every pure row"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Strict positivity and generation give one finite L>0 such that abs(T(p,x)-T(p,y))<=L norm(x-y) for every original pure p and all original mixed x,y in K. This consumed helper directly uses the original frozen CommonOldExclusionConfirmation.comparison_lipschitz owner, enlarging its bound to a positive constant. It provides no independent new mathematical content or escape witness. Neither EB nor PR nor Inj is needed."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-scale-axis-bound"), DeclarationHandle.Create(Owner + "original_scale_axis_bound"),
                H("Universal actual scale-to-axis estimate"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Under closedness, strict positivity, generation, EB and pure PR, one L>0 works at every original pure p and every complete chart a. A positive common scale t<=1/2 has extensionBudget(a,v)=1/(2t) in every unit direction and 2t<=L norm(a(v)-a(-v)). These are the same actual comparison coefficient and original optimal budget, using all mixed inputs of the original scale owner."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-bounded-budget-noncollapse"), DeclarationHandle.Create(Owner + "original_bounded_budget_noncollapse"),
                H("Finite budget on arbitrary whole-P label sets"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("For any set U of original pure labels and real B>0, assume every actual chart and unit direction at every p in U has extensionBudget<=B. There is a single delta>0 with delta<=diam(D(p)) for all p in U, explicitly delta=1/(B L) for the universal comparison bound. U is an arbitrary subset of the entire P; it may be a neighborhood containing labels outside P0. This is the noncollapse direction of the local-budget argument. The converse local-budget implication, the exact whole-ball limit dichotomy, all continuity-point identifications and both Sigma branches are not asserted here."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-diameter-collapse-budget"), DeclarationHandle.Create(Owner + "original_diameter_collapse_budget"),
                H("Every actual diameter collapse makes budgets diverge"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Under the same complete EB plus pure PR hypotheses, let pn be any sequence of original pure labels whose full exclusion diameters tend to zero. Choose arbitrary complete original charts a(n) and any unit coordinate v(n) in each, with dimensions allowed to vary. Then their actual extensionBudget(a(n),v(n)) tends to positive infinity. The universal scale-to-diameter estimate gives 1<=budget(n) L diam(D(pn)); no finite bound can persist along the sequence. The theorem does not assume label convergence, restrict labels to P0, or replace the original budget with a reciprocal definition."))), DescribeRole.Theorem))));
}
