using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.PrimitiveRoot;

internal sealed class PrimitiveRootChebyshevThirtyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/PrimitiveRoot/ChebyshevThirty.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Chebyshev's unconditional thirty-period estimate",
        H("Chebyshev's unconditional thirty-period estimate"), Blocks(
            Describe.Lean(DescribeId.Create("psi-nat-lower"),
                DeclarationHandle.Create(Prefix + "psi_nat_lower"),
                H("An explicit lower bound at every positive integer"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Set c=log(2)/2+log(3)/3+log(5)/5-log(30)/30. For every natural " +
                    "n at least one, psi(n) is at least c*n-5*(1+log(n)). No zero " +
                    "hypothesis is assumed. The existing floor_factorial_log_error supplies " +
                    "an absolute error at most 1+log(n) for each of the five factorial " +
                    "terms, including those whose scaled argument is below one. The factorial " +
                    "comparison follows from Lambda*zeta=log: its multiplier is " +
                    "m+floor(m/30)-floor(m/2)-floor(m/3)-floor(m/5), which is at most " +
                    "one by its period thirty. Nonnegativity of Lambda bounds the " +
                    "combination by psi(n). The " +
                    "n*log(n) and linear terms cancel exactly, leaving c*n. " +
                    "This is the classical Chebyshev factorial method; the theorem is " +
                    "an explicit repository formalization, without an originality claim."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("coefficient-bounds"),
                DeclarationHandle.Create(Prefix + "coefficient_bounds"),
                H("Rational coefficient bounds"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "The coefficient c lies between 921/1000 and one. The proof directly " +
                    "uses the pinned Mathlib decimal enclosures for log(2), log(3) and " +
                    "log(5), after expanding log(30). This numerical helper is consumed " +
                    "by the principal triangular sum estimate."))), DescribeRole.Theorem))));
}
