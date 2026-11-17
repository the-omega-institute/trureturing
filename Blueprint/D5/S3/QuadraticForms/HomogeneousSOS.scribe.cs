using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuadraticForms;

internal sealed class HomogeneousSOSDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuadraticForms/HomogeneousSOS.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Homogeneous and parity representatives for sums of squares",
        H("Homogeneous and parity representatives for sums of squares"), Blocks(
            Paragraph(Text("These polynomial results supply the homogeneous and parity decompositions used by the all-level GNP characterization in BoseHierarchy. The tensor-operator bridge is constructed in BoseSOSCertificates and BoseSOSDuality.")),
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
                Blocks(
                    Paragraph(Text("Let sigma be any variable type, Gamma a finite additive commutative group satisfying a+a=0 for every a, and w : sigma to Gamma any grading. For every real polynomial p : MvPolynomial sigma Real and natural number d, assume p.IsHomogeneous (2*d) and p.IsWeightedHomogeneous w 0. Then the native unrestricted IsSumSq p holds if and only if there exist a natural number m and q : Fin m to Gamma to MvPolynomial sigma Real such that, for every i and a, q(i,a) is homogeneous of degree d and weighted-homogeneous for w in sector a, and p is the finite sum over i : Fin m and a : Gamma of q(i,a) times q(i,a).")),
                    Paragraph(Text("Projecting each homogeneous square to sector zero cancels all cross-sector products; conversely the displayed finite sum is a native sum of squares. The zero polynomial, d=0 and an empty square family m=0 remain in scope."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("even-form-sos-iff"),
                DeclarationHandle.Create(Prefix + "even_form_sos_iff"),
                H("Even-form SOS decomposition"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The genuine substitution X_i to X_i squared converts a homogeneous real form to a native sum of squares exactly when the original form is a finite sum of binary square-free monomials times squares of homogeneous forms. Every nonzero summand has the exact degree relation. Multiple square terms in one parity sector are retained. This formalizes the polynomial decomposition underlying GNP Proposition 8.10; it is not the full GNP tensor characterization."))),
                DescribeRole.Theorem))));
}
