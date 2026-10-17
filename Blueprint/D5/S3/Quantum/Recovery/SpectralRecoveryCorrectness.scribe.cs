using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Recovery;

internal sealed class SpectralRecoveryCorrectnessDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The computed spectral transpose recovery is exact whenever any represented Kraus left inverse exists. The proof derives observable intertwining from that inverse, then reuses cfc commutation and the computed support identity. Together with the finite Kraus criterion this closes the three-way equivalence in the finite representation.",
        H("SpectralRecoveryCorrectness"),
        Blocks(new[]
        {
            "computed_recovery_of_kraus_left_inverse"
        }.Select(name => Describe.Lean(
            DescribeId.Create(name.Replace('_', '-')),
            DeclarationHandle.Create("D5/S3/Quantum/Recovery/SpectralRecoveryCorrectness." + name),
            H(name.Replace('_', ' ')),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(
                LibraryNoteRef.Create("D5/L/Quantum/barnumknill2002reversal"),
                LibraryNoteRef.Create("D5/L/Quantum/nayaksen2007invertible"),
                LibraryNoteRef.Create("D5/L/Quantum/choijohnstonkribs2009multiplicative")),
            Blocks(Paragraph(Text("The computed spectral transpose recovery is exact whenever any represented Kraus left inverse exists. Its original proof derives observable intertwining from that inverse and uses the same computed spectral support and inverse square root. The proof-local observable identities hold for every complex logical matrix, and the final recovery calculation consumes their specialization to the original input.")),
                Paragraph(Text("For the actual finite families E and A, put N(T) = sum E(a) T E(a)^H, Q = N(I), P = spectralSupport(Q), W = spectralInverseSqrt(Q), and Y(T) = sum A(b)^H T A(b). The inverse identity on every complex matrix gives Y(T) E(a) = E(a) T and E(a)^H Y(T) = T E(a)^H. Consequently Q Y(T) = Y(T) Q = N(T), W Y(T) = Y(T) W, and pi(T) = W N(T) W = P Y(T). Here W retains its actual zero value on the kernel of Q; no invertibility of Q is required.")),
                Paragraph(Text("The spectral normalization and support identities give pi(I) = P, pi(T)^H = pi(T^H), and P pi(T) = pi(T) P = pi(T). The identity N(T) Y(U) = N(T U), together with W commuting with Y(U), gives pi(T) pi(U) = pi(T U). The same Q is positive semidefinite, P Q = Q P = Q, and Q pi(T) = pi(T) Q = N(T). These are consequences of the existing proof-local producers and finite matrix algebra, rather than new named mathematical declarations.")),
                Paragraph(Text("With the actual F(i,j) = pi(single(i,j,1)), multiplication and conjugate transpose give the matrix-unit laws. The sum of F(i,i) is P, and the matrix basis expansion gives representedMatrix(F,T) = pi(T). Trace preservation of the original E family gives trace(F(v,v) Q) = trace(N(single(v,v,1))) = 1. Thus the existing MatrixUnitDecoder.decoder_recovers_commutant_weight applies with this F, this Q, and the original reset index v, and its input Q representedMatrix(F,T) is exactly N(T). This pointwise application does not establish equality with a previously chosen syndrome family, a global smooth frame or metric, or equality of the two full decoder actions on arbitrary physical matrices."))),
            DescribeRole.Theorem)).ToArray())));
}
