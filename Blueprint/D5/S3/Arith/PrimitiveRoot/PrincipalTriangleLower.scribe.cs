using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.PrimitiveRoot;

internal sealed class PrincipalTriangleLowerDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An unconditional principal triangular sum",
        H("An unconditional principal triangular sum"), Blocks(
            Describe.Lean(DescribeId.Create("principal-triangle-large"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/PrimitiveRoot/PrincipalTriangleLower." +
                    "principal_smoothedCharacterSum_large"),
                H("A linear principal term without RH"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(
                    "For every prime p≥5000000, the real part of the triangular sum " +
                    "for the principal character is at least (23/50)p. The sum retains " +
                    "all von Mangoldt prime powers. A prime power that is a primitive " +
                    "root supplies its prime base as a primitive root in the sieve.")),
                Paragraph(Text(
                    "ChebyshevThirty.psi_nat_lower supplies ψ(n)≥cn−5(1+log n), " +
                    "where c=log(2)/2+log(3)/3+log(5)/5−log(30)/30 and c≥921/1000. " +
                    "Exact discrete summation gives S(p)=p⁻¹Σ(k<p)ψ(k), hence " +
                    "S(p)≥c(p−1)/2−5(1+log p). The tangent bound for log at five " +
                    "million implies log p≤p/50000 throughout this range, yielding " +
                    "the stated bound. The prime-modulus principal sum is identified " +
                    "with S(p) using TriangleRampZeta.principal_smoothedCharacterSum_eq. " +
                    "No zeta zero hypothesis is used in this proof. The explicit loss " +
                    "relative to p/2 is epsilon=1/25; the smaller primes are handled " +
                    "by separate kernel certificates."))), DescribeRole.Theorem))));
}
