using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Boundary;

internal sealed class MeromorphicHorizontalLogTransportDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Analytic/Boundary/MeromorphicHorizontalLogTransport.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Compact meromorphic functions satisfy an exact signed horizontal lognorm transport identity.",
        H("Meromorphic horizontal lognorm transport"),
        Blocks(
            Paragraph(Text(
                "Let a<=b and let u and v be arbitrary real heights. Let K be the closed rectangle "
                    + "with real part in [a,b] and imaginary part between min(u,v) and max(u,v). "
                    + "Suppose f is meromorphic on K and meromorphicOrderAt f z is not top for every z in K. "
                    + "the horizontal integral of log ||f|| at v minus the corresponding integral at u "
                    + "equals the signed height integral of the negative imaginary part of f'/f.")),
            Describe.Lean(
                DescribeId.Create("compact-meromorphic-signed-horizontal-transport"),
                DeclarationHandle.Create(Owner + "meromorphic_horizontal_lognorm_transport"),
                H("Signed transport through every zero and pole height"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The proof factors the meromorphic function on the compact rectangle into a "
                        + "finite signed divisor product and an analytic nonvanishing factor. The "
                        + "logarithm of each divisor factor is the real logarithm of a distance, "
                        + "and its quotient contribution is the corresponding real horizontal "
                        + "kernel with its integer multiplicity, including negative multiplicities. "
                        + "The analytic factor is handled by vertical differentiation and real Fubini. "
                        + "Codiscrete equality is restricted independently on every horizontal slice; "
                        + "the finite exceptional sets therefore disappear from the interval integrals. "
                        + "Every horizontal logarithm and imaginary-part slice is interval integrable, "
                        + "as is the outer signed integral. The theorem includes spatial "
                        + "endpoints, degenerate rectangles, zeros and poles on every height, and both "
                        + "orientations of the signed height interval. It does not assert the Riemann "
                        + "hypothesis or impose a zero-free, good-height, open-domain, or assumed "
                        + "integrability restriction."))),
                DescribeRole.Theorem),
            Paragraph(Text(
                "The conclusion concerns finite signed interval integrals of real functions. "
                    + "It does not assert integrability of the complex logarithmic derivative "
                    + "on a singular slice. Global continuation, zeta identification and the "
                    + "Riemann hypothesis require separate results.")))));
}
