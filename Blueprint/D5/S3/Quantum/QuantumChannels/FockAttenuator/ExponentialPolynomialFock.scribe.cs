using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels.FockAttenuator;

internal sealed class ExponentialPolynomialFockDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every exponential polynomial has a genuine Fock vector.",
        H("Every exponential polynomial has a genuine Fock vector"),
        Blocks(Describe.Lean(DescribeId.Create("exponential-polynomial-fock-reconstruction"),
            DeclarationHandle.Create("D5/S3/Quantum/QuantumChannels/FockAttenuator/ExponentialPolynomialFock.exponential_polynomial_reconstruction"),
            H("Every exponential polynomial has a genuine Fock vector"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("For every finite exponential-polynomial function with arbitrary complex exponents and polynomial coefficients, there exists an actual completed square-summable Fock vector whose Bargmann transform is that function. This assertion applies to exponential polynomials, rather than to all entire functions.")),
                Paragraph(Text("For z^m*exp(alpha*z), the coefficient at n=k+m is sqrt((k+m)!)*alpha^k/k!, and coefficients below m are zero. A symbolic factorial comparison bounds (k+m)!/(k!)^2 by m!*2^m*2^k/k!. The exponential series proves square summability for every complex alpha, without a magnitude restriction.")),
                Paragraph(Text("The constructed lp vector has the required entire transform by the convergent factorial series. Finite polynomial and exponential-block sums give the full reconstruction. Transform injectivity gives uniqueness when it is needed by a consumer. No numerical summability test, cutoff, energy premise or real-coefficient restriction is used."))),
            DescribeRole.Theorem))));
}

