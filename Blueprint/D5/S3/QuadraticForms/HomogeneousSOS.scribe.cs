using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuadraticForms;

internal sealed class HomogeneousSOSDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuadraticForms/HomogeneousSOS.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Homogeneous and parity representatives for sums of squares",
        H("Homogeneous and parity representatives for sums of squares"), Blocks(
            Paragraph(Text("These are polynomial prerequisites for the genuine all-level GNP characterization. They do not themselves establish the tensor-moment bridge or any extension-cone characterization. The full package remains incomplete until those proofs and the normal acceptance are present.")),
            Describe.Lean(DescribeId.Create("homogeneous-sos-iff"),
                DeclarationHandle.Create(Prefix + "homogeneous_sos_iff"),
                H("Homogeneous square representatives"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real homogeneous polynomial of degree twice d, the native unrestricted IsSumSq predicate is equivalent to a finite sum of squares of homogeneous degree-d forms. Positivity of real evaluations removes all lower-degree components; zero forms and d=0 are retained."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("homogeneous-parity-sos-iff"),
                DeclarationHandle.Create(Prefix + "homogeneous_parity_sos_iff"),
                H("Parity square representatives"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("In a finite grading group with a+a=0, a polynomial in the zero sector has an SOS representation whose half-degree forms each lie in an individual sector. Projecting a square to sector zero cancels all cross-sector products. The predicate remains the native unrestricted sum of squares."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("even-form-sos-iff"),
                DeclarationHandle.Create(Prefix + "even_form_sos_iff"),
                H("Even-form SOS decomposition"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The genuine substitution X_i to X_i squared converts a homogeneous real form to a native sum of squares exactly when the original form is a finite sum of binary square-free monomials times squares of homogeneous forms. Every nonzero summand has the exact degree relation. Multiple square terms in one parity sector are retained. This formalizes the polynomial decomposition underlying GNP Proposition 8.10; it is not the full GNP tensor characterization."))),
                DescribeRole.Theorem))));
}
