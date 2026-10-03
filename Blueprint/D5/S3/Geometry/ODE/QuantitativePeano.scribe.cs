using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Geometry.ODE;
internal sealed class QuantitativePeanoDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Geometry/rolfes2026peano");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A quantitative Peano integral solution from delayed Tonelli approximations.",
        H("Continuous cylinder fields and integral solutions"),
        Blocks(Describe.Lean(
            DescribeId.Create("quantitative-peano-integral"),
            DeclarationHandle.Create("D5/S3/Geometry/ODE/QuantitativePeano."
                + "exists_eq_forall_mem_Icc_eq_integral"),
            H("Peano existence on the prescribed cylinder interval"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromLiterature(Source),
            Blocks(
                Paragraph(Text("Let E be a finite-dimensional real normed vector space, "
                    + "including dimension zero. Let f be jointly continuous on the closed "
                    + "time interval times the closed ball of radius r about x0, with norm "
                    + "at most L. The initial time t0 belongs to the interval and "
                    + "L times max(tmax-t0,t0-tmin) is at most r. Then a continuous curve "
                    + "in that ball solves alpha(t)=x0+integral from t0 to t of f(s,alpha(s)) "
                    + "at every interval point.")),
                Paragraph(Text("The live construction recursively integrates delayed curves. "
                    + "The common speed bound controls both their ranges and equicontinuity. "
                    + "Compactness of the finite-dimensional closed ball and Arzela-Ascoli "
                    + "yield a uniformly convergent subsequence. Vanishing delays and "
                    + "dominated convergence give the actual integral equation. Reflection "
                    + "in time and gluing at the initial value supply the two-sided interval.")),
                Paragraph(Text("No spatial Lipschitz condition or uniqueness is asserted. "
                    + "The source is an Apache 2.0 adaptation of Mathlib/Analysis/ODE/Peano.lean "
                    + "at philipp-svinger/mathlib4 revision "
                    + "a6c8f2f1ae84638491c3f1635c9f8448bda1e727; original author notices "
                    + "and the applicable LICENSE are retained. "
                    + "The integral existence result establishes no geometric metric-domain "
                    + "invariance, face gluing, volume identity, or flow convergence."))),
            DescribeRole.Theorem)), []));
}
