using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.AbsolutePPT.SchmidtStar;
internal sealed class SixRowHeadScalarDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The scalar estimate uses the explicit quarter-circle recipe with alpha at least one half, k between zero and one, and h between zero and three halves. The half-angle substitution reduces it to the exact polynomial certificate. Both squaring steps compare nonnegative quantities, and every divided denominator is positive.", H("SixRowHeadScalar"), Blocks(
            Paragraph(Text("The scalar estimate uses the explicit quarter-circle recipe with alpha at least one half, k between zero and one, and h between zero and three halves. The half-angle substitution reduces it to the exact polynomial certificate. Both squaring steps compare nonnegative quantities, and every divided denominator is positive.")),
            Describe.Lean(DescribeId.Create("sixrowhead-sixrowheadscalar-half-angle-bound"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadScalar.half_angle_bound"),
                H("half angle bound"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("theorem half_angle_bound (z k h : ℝ) (hz : 0 < z) (hz' : z ≤ 3/4) (hk : 0 ≤ k) (hk' : k ≤ 1) (hh : 0 ≤ h) (hh' : h ≤ 3/2) (hg : 0 ≤ constraint z k h) : let s := (1-z^2)/(1+z^2) let t := 2*z/(1+z^2) let T := Real.sqrt (1+(2*s+s^2)*k) Real.sqrt (1+k*h+t^2*k) ≤ s^2*Real.sqrt (1+k*h)+t^2*T+t^3*(1+s)*k*h/(2*T)"))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("sixrowhead-sixrowheadscalar-unit-bound"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadScalar.unit_bound"),
                H("unit bound"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("theorem unit_bound (s t k h : ℝ) (hs : 0 ≤ s) (ht : 0 < t) (hn : s^2+t^2=1) (hk : 0 ≤ k) (hk' : k ≤ 1) (hh : 0 ≤ h) (hh' : h ≤ 3/2) (hcap : t^2 ≤ 4*s^2*(1+k*h)) : let T := Real.sqrt (1+(2*s+s^2)*k) Real.sqrt (1+k*h+t^2*k) ≤ s^2*Real.sqrt (1+k*h)+t^2*T+t^3*(1+s)*k*h/(2*T)"))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("sixrowhead-sixrowheadscalar-recipe-bound"),
                DeclarationHandle.Create("D5/S3/Quantum/Entanglement/AbsolutePPT/SchmidtStar/SixRowHeadScalar.recipe_bound"),
                H("recipe bound"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("theorem recipe_bound (alpha k h : ℝ) (ha : 1/2 ≤ alpha) (hk : 0 ≤ k) (hk' : k ≤ 1) (hh : 0 ≤ h) (hh' : h ≤ 3/2) : let L := Real.sqrt (alpha^2+1+k*h) let s := alpha/L let t := Real.sqrt (1+k*h)/L let T := Real.sqrt (1+(2*s+s^2)*k) Real.sqrt (alpha^2+1+k+k*h) ≤ alpha*s+t*T+t^2*(1+s)*k*h/(2*T)"))), DescribeRole.Theorem)
        )));
}
