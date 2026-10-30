using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround;

internal sealed class ActualPairingSymmetryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Symmetry of the Original Selected Actual Tensor Pairing",
        H("Symmetry of the Original Selected Actual Tensor Pairing"),
        Blocks(Describe.Lean(
            DescribeId.Create("actual-form-symmetric"),
            DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/ActualPairingSymmetry.actualForm_symmetric"),
            H("Symmetry of the Original Selected Actual Tensor Pairing"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("For every integral symmetric even lattice D and integer unit determinant witness hu, the literal existing ActualChargedAdjoint.actualForm(D,hu) is symmetric on the original ActualTensor(D,hu). There is no positivity, positive-rank, pairing-choice or additional symmetry premise. Its selectedGroundPairing is the original Classical.choice(actual_ground_pairing D hu); the definition and the choice are unchanged.")),
                Paragraph(Text("Let B be any GroundPairing on the existing ActualGround(D,hu). Choose an already constructed symmetric nondegenerate invariant form S on that same selected representation. Mathlib's symmCompOfNondegenerate gives A=S.toDual inverse composed with B, with S(Ax,y)=B(x,y). Invariance and the actual representation inverse show S(A rho(g)x,y)=S(rho(g)Ax,y). Nondegeneracy of S implies A commutes with every actual representation operator.")),
                Paragraph(Text("The selected representation supplies its original rank equation and central sign. The existing actual_operator_algebra scalar_commutant therefore gives A=c times the identity. Consequently B(x,y)=c S(x,y)=c S(y,x)=B(y,x). This argument applies to the unchanged selected B and includes rank zero. It needs neither a new selected symmetric pairing nor a proof that c is nonzero.")),
                Paragraph(Text("The signed oscillator Wick form is symmetric by its existing owner theorem. Mathlib's scalar-valued tensor-product symmetry theorem transports these two factor symmetries to the literal actualForm. The consumed comparison-operator argument supplies the new proof content; finite-dimensional duality and tensor symmetry are reused. This is classical invariant bilinear-form theory, with no literature novelty claim.")),
                Paragraph(Text("This symmetry substep does not prove the full ordered-kernel exchange identity, original-source skew exchange, three-twisted crossing, an extension VOA, Monster symmetry, string theory or AdS/CFT. It leaves the existing all-state BPZ theorem unchanged."))),
            DescribeRole.Theorem))));
}
