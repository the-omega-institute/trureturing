using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.RegularRepresentation;

internal sealed class CentralAutocorrelationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual real group-algebra autocorrelations give maximal central coefficients at the identity. The proof constructs the Gram factor and uses finite sums of square differences.",
        H("Central coefficients of actual autocorrelations"),
        Blocks(
            Paragraph(Text("Let G be a finite group and a,b real group-algebra elements, retaining all their coefficients and multiplicities. Write a* for coefficient reversal, (a*)(g)=a(g^-1). The source proves that reversal is an anti-involution, proves cyclicity of a central coefficient, and supplies coefficientwise nonnegativity and monotonicity for the actual multiplication and its powers. This is the coefficient form of the finite regular-trace convention in RegularTrace.trace_lmul_list_prod.")),
            Describe.Lean(DescribeId.Create("finite-group-actual-autocorrelation-coefficient-bound"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/RegularRepresentation/CentralAutocorrelation.autocorrelation_coeff_le"),
                H("An actual autocorrelation is largest at the identity"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every real group-algebra element a and every z in G, the coefficient at z of a*a* is at most its coefficient at the identity. No positivity or matrix representation is an assumed input.")),
                    Paragraph(Text("Expand the coefficient as sum_g a(g)a(z^-1*g). Apply 2xy<=x^2+y^2 at each g. Left multiplication by z^-1 permutes G, so the two sums of squares coincide. The identity coefficient is exactly this sum of squares."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("finite-group-central-alternating-autocorrelation-cube"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/RegularRepresentation/CentralAutocorrelation.central_alternating_autocorrelation_le"),
                H("The central coefficient of an alternating cube"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every central z, the coefficient at z of ((a*a*)(b*b*))^3 is at most its identity coefficient. The actual autocorrelation factors a,b are the inputs; an abstract positive-operator or center-comparison supplier is not assumed.")),
                    Paragraph(Text("Put P=reverse(b) times a and T=P times reverse(P). Cyclicity of a central coefficient identifies the coefficient of the original alternating cube with that of T^3. Reversal fixes T, and K=T times P satisfies T^3=K times reverse(K), so the proved autocorrelation coefficient bound applies. Both the rotation and Gram identity are proved in the group algebra. No positivity is asserted for the nonsymmetric product (a*a*)(b*b*) itself."))),
                DescribeRole.Theorem),
            Paragraph(Text("The intended consumer constructs a and b from the literal upper and lower unipotent interval measures. The finite-group result alone does not identify their coefficients with the original six-return-word count; that identification and the interval smoothing bounds belong to the actual-count application.")))));
}
