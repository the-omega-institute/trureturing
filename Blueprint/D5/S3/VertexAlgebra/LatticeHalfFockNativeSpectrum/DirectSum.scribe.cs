using StrataLint.Scribe;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.LatticeHalfFockNativeSpectrum;

internal sealed class DirectSumDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Background =
        LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original integral spectral direct sum",
        H("Finite inverse components, not assigned labels"),
        Blocks(
            Paragraph(Text("IntegerComponents is the algebraic direct sum over every integer n of the actual original L0 eigenspace at n. Its assembly map adds the finitely supported components into the original tensor state. Distinct complex integer eigenvalues give independence by the standard eigenspace theorem. The range of assembly is the supremum of these submodules, which integral_supremum identifies with ker(S+id). Thus integerDirectSumEquiv is a genuine linear equivalence to the actual odd sector.")),
            Describe.Lean(
                DescribeId.Create("native-half-fock-integer-inverse-coordinate"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/LatticeHalfFockNativeSpectrum/DirectSum.integer_inverse_coordinate"),
                H("The inverse component is the exact integer coefficient projector"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(Background),
                Blocks(Paragraph(Text("For every odd-sector state and every integer n, the underlying vector of the n-th inverse component is integerProjector(n) of the original state. This projector filters actual occupation coefficients by rank/16+W/2=n. On a homogeneous state it is the identity for the selected integer and zero for every other integer. Direct-sum induction proves the assembly-coordinate identity, hence the inverse formula."))),
                DescribeRole.Theorem),
            Paragraph(Text("integerDirectSumEquiv_value expresses the forward map as the finite DFinsupp sum of actual eigenspace vectors. The linear equivalence supplies both inverse laws. Together with finite_reconstruction and finite_directness these identities retain pointwise finite support and exclude an unrestricted infinite-sum assumption.")),
            Paragraph(Text("No target-field conjugation, new intertwiner, assumed module law, ground endomorphism classification or moonshine gluing is part of this spectral direct-sum construction.")))));
}
