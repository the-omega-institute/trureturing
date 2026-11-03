using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels.FockAttenuator;

internal sealed class RankSeparationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Cardinal range dimension of the actual completed reduced operator is bounded by k exactly when its entire kernel has k separated terms.",
        H("Actual completed rank and entire separation"),
        Blocks(Describe.Lean(DescribeId.Create("completed-fock-rank-separation"),
            DeclarationHandle.Create("D5/S3/Quantum/QuantumChannels/FockAttenuator/RankSeparation.reduced_rank_le_iff_separated"),
            H("The completed rank/separation equivalence"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("For every two-mode vector V in lp(Natural -> H,2), where H=lp(Natural -> Complex,2), and every natural k, the Cardinal Module.rank over Complex of the range of the existing purePartialTrace(V) is at most the natural Cardinal k if and only if the completed Bargmann kernel admits k entire separated terms. Zero terms and the zero operator are included. Infinite-dimensional ranges are measured by Cardinal rank throughout, rather than by finite-dimensional finrank.")),
                Paragraph(Text("In the separation-to-rank direction, the supplied entire factors are arbitrary entire functions. The proof does not assume they are Bargmann transforms of H vectors. It takes the span S of the actual coefficient-operator images of all exponential vectors, maps S injectively by the Bargmann transform into the given finite span of scalar factors, and obtains finite dimension and closedness of S. Totalness of the exponential vectors and continuity of the actual coefficient operator put its entire range in S. The range of C*C-adjoint is then contained in the range of C.")),
                Paragraph(Text("In the reverse direction, first establish finite dimension of the actual reduced range from its finite Cardinal bound. The closures of range(C) and range(C*C-adjoint) agree because their orthogonal complements agree. Closedness of the finite reduced range puts range(C) inside that range. A finite orthonormal basis of this actual Hilbert subspace supplies vectors u_i. The companion vectors are conjugates of C-adjoint(u_i). Their genuine Bargmann transforms give both entire families. Padding by zeros preserves the exact bound k.")),
                Paragraph(Text("This correspondence uses the synthesized Hilbert-Schmidt column operator and its proved identity with the existing physical partial trace. It is valid for arbitrary infinite support. It supplies the completed reconstruction join used in the physical classification; it neither assumes finite input support nor replaces the physical channel by a matrix with an assigned spectrum."))),
            DescribeRole.Theorem))));
}
