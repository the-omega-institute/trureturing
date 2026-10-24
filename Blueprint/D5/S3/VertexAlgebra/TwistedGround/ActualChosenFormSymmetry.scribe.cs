using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.TwistedGround;
internal sealed class ActualChosenFormSymmetryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Symmetry of the Original Chosen Ground Form", H("Symmetry of the Original Chosen Ground Form"), Blocks(
            Paragraph(Text("The selected ActualGround, original GroundPairing structure, private selectedGroundPairing and public ActualChargedAdjoint.actualForm are unchanged. In particular the original choice remains Classical.choice (actual_ground_pairing D hu), not a choice of SymmetricGroundPairing.")),
            Paragraph(Text("For any two original GroundPairings, the generic invariant-form comparison and the already proved actual operator algebra give a unique nonzero proportionality scalar. Applying this comparison to the symmetric witness of SymmetricPairing proves that every original GroundPairing is symmetric. This includes the exact original chosen pairing. The two bind-only comparison helpers remain private and are consumed in the final proof.")),
            Paragraph(Text("Mathlib tensor symmetry combines the derived ground symmetry with the original SignedOscillatorWick.wick_symmetric. The sole new visibility change removes private from wick_symmetric while preserving its statement and proof. No positive-definite metric, fixed rank, new carrier or new representation is used. All integral lattices with IsUnit D.G.det remain in scope, including rank zero and indefinite lattices.")),
            Paragraph(Text("This closes symmetry of the old actual tensor bilinear form. It neither changes the orientations of existing charged adjoint laws nor proves restricted-dual representability, inversion, mixed Jacobi, a twisted intertwiner, fusion, string theory or AdS/CFT. Classical Schur duality and bilinear tensor symmetry are the literature source; no novelty claim.")),
            Paragraph(Text("The accompanying Reg source has compiled the faithful equality-readout family, exact full-telescope bridge, positive law, whole-family intervention, sensitivity and observational dependence. Typed elaboration and current four-slot admission are separate checks. The source-selection and reconstruction boundary remains unfinished at https://github.com/the-omega-institute/trureturing/issues/21214; no current declared_validated status is claimed.")),
            Describe.Lean(DescribeId.Create("actual-form-is-symmetric"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/TwistedGround/ActualChosenFormSymmetry.actualForm_isSymm"),
                H("Symmetry of the Original Chosen Ground Form"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The selected ActualGround, original GroundPairing structure, private selectedGroundPairing and public ActualChargedAdjoint.actualForm are unchanged. In particular the original choice remains Classical.choice (actual_ground_pairing D hu), not a choice of SymmetricGroundPairing."))),
                DescribeRole.Theorem))));
}
