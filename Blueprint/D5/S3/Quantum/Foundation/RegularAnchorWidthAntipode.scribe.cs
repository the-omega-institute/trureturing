using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class RegularAnchorWidthAntipodeDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Foundation/RegularAnchorWidthAntipode.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The entire original effect interval detects actual antipodal contact and unit support at a regular anchor.",
        H("Full original width and antipodal contact"), Blocks(
        Paragraph(Text("Keep the original finite dimensional real carrier V, closed generating cone C, strictly positive unit u, complete base K and full effect interval 0 <= f <= u. Every original exclusion has a full three-ball chart, and equality of exclusions identifies their pure labels. At the original regular anchor p the actual common confirmer e is unique. The NativeChart input is derived by RegularAnchorNormalChart.regular_anchor_native from precisely these original hypotheses; it supplies neither a free positivity bridge nor a chosen subfamily of effects.")),
        Describe.Lean(DescribeId.Create("actual-image"), DeclarationHandle.Create(Owner + "actualImage"),
            H("Entire actual ratio image"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Z is the image of every x in K other than p under H(x)/g(x), where g=u-e. NativeChart proves g is positive on this entire domain. No closedness of the pure state carrier is assumed."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("rho"), DeclarationHandle.Create(Owner + "rho"),
            H("Actual directional support"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("rho(v) is the supremum of -inner(v,z) over the whole actual ratio image. It is the exact source supremum of -inner(v,H(x))/g(x) over all x in K other than p."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("rho-upper"), DeclarationHandle.Create(Owner + "rho_le_iff"),
            H("Whole-base support bound"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For every real r and every coordinate vector v, rho(v)<=r is equivalent to -inner(v,H(x))<=r*g(x) for every original base state x other than p. The whole-cone NativeChart bound proves that the defining supremum is finite."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("rho-lower"), DeclarationHandle.Create(Owner + "rho_unit_lower"),
            H("Actual inner-ball lower bound"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For every unit v, rho(v)>=1 because the actual original chart point a(-v) has g=1 and H=-v. This uses an actual state in the original exclusion."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("direction"), DeclarationHandle.Create(Owner + "direction"),
            H("Original directional linear effect"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The real linear functional direction(v) on V is inner(v,H). Its coordinate expansion lies in the entire signed normal span. The proved restriction isomorphism, rather than an additional premise, reconstructs every normalized positive annihilator with slope v as g+direction(v)."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("antipodal"), DeclarationHandle.Create(Owner + "rho_one_iff_antipodal"),
            H("Exact actual antipodal criterion"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For every unit v, rho(v)=1 exactly when some effect in the entire original interval takes one at a(v) and zero at a(-v). Positivity is derived on the full original cone from the ratio bound; conversely an arbitrary original separating effect enters the existing actual comparison and slope-body theorem. The source direction v and the actual chart antipodes are retained without reversing or replacing their carriers."))), DescribeRole.Theorem),
        Paragraph(Text("These results are an intermediate mathematical interface for Theorem 122.13. The minimum over the entire sphere, the closure shell and boundary criterion, strict delta containment and boundary distance require the remaining original clauses. No whole-theorem completion, matrix realization, physical operation, literature novelty or completed four-slot registration is asserted here."))
        )));
}
