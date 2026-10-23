using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.ChargedResidue;

internal sealed class LocalityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Independent tails of the complete charged physical residue.",
        H("Complete Charged Residue Tail"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("charged-complete-residue-independent-tail"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/ChargedResidue/Locality.chargedPhysicalResidueRow_tail"),
                H("The complete row vanishes at every padded locality cutoff"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/flm1988monster")),
                Blocks(Paragraph(Text("Let D be arbitrary lattice data with unit Gram determinant, sigma and tau arbitrary charges, "
                    + "epsilon and eta either projected sign, and gamma, delta, r, n arbitrary signed integer lifts and indices. "
                    + "For every natural K at least natAbs(bilinear D sigma tau), put L=((K:Int)-r).toNat. "
                    + "For every natural l with L <= l and every x:ActualTensor D hu, the complete forward-minus-reverse "
                    + "physical residue row is zero. The boundary l=L, K=0 and L=0 are included.")),
                    Paragraph(Text("Both projections are expanded into their reflected charge components. All four charged "
                    + "commutators have the same locality order, which is padded to K by the actual difference operator. "
                    + "Nonnegative residue extraction then annihilates the complete row. This argument uses neither "
                    + "the collision-row transform nor the source comparison and asserts no separate vanishing of an ordered branch."))),
                DescribeRole.Theorem))));
}
