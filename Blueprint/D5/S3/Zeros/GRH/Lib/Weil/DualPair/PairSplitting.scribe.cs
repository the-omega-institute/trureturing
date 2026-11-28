using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.Weil.DualPair;

internal sealed class PairSplittingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Pair Splitting", H("Pair Splitting"),
        Blocks(
            Paragraph(Text("Rational points of the unitary group fix the theta functional, by doubling. Kronecker coordinates of rational maps on the Hom space; invertible Gram matrix. Dual pair acting on Hom(S,T): determinants, continuity, unitarity, automorphy of theta kernels. Mixed model for a dual pair: Levi and unipotent action, theta expansion.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/Weil/DualPair/PairSplitting.sourceTerm_radicalElt"),
                H("sourceTerm_radicalElt"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("For the unipotent element u = Space.Splitting.radicalElt c z, z hermitian, (ω_{a,b}(u,1)f)[x] = ψ(½ tr(z x*ε′x)) ϱ(x c* ε₀) f[x], where ε′, ε₀ are the standard forms of T and V₀.")))))));
}
