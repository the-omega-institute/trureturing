using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.GRH.Lib.PadicComparison.CrystallineFrobenius;

internal sealed class CrystallineCohomologyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Crystalline Cohomology", H("Crystalline Cohomology"),
        Blocks(
            Paragraph(Text("p-adic etale cohomology of smooth proper varieties is finite with continuous Galois action. Natural Galois-equivariant period map, bijective for smooth proper varieties. Frobenius relations on special-fibre points pass to l-adic cohomology; inertia acts trivially. p-adic cohomology is crystalline and its Frobenius satisfies the congruence relation.")),
            Describe.Lean(DescribeId.Create("source-result"),
                DeclarationHandle.Create("D5/S3/Zeros/GRH/Lib/PadicComparison/CrystallineFrobenius/CrystallineCohomology.isCrystalline_and_linearFrob_rel"),
                H("isCrystalline_and_linearFrob_rel"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/Zeros/alpoge2026dirichletgrh")),
                Blocks(Paragraph(Text("R noetherian, mapping into the place A above p of Ω ≅ ℚ̄; W, Y proper over R, charted over Ω, Y also over R; (γ_i, a_i) Weil pairs at A. If ∑ m_i[Frob^{a_i}u_i(x)] = 0 at field points x of W above A, then V^n(Y) is crystalline and ∑ m_i u_i^*β_{γ_i,a_i} = 0.")))))));
}
