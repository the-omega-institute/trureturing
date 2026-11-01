using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class LatticeMatterGhostCouplingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The native algebraic lattice matter-ghost coupling",
        H("The native algebraic lattice matter-ghost coupling"), Blocks(
            Paragraph(Text("The carrier is the original all-charge lattice carrier tensor over the complex numbers with the original countable occupation ghost Fock space. The quadratic matter modes are the actual Sugawara field coefficients at m+1. No inverse-Gram equations are needed for construction or the two Ward identities. This is the classical matter term of the algebraic BRST construction; no mathematical or physical novelty is asserted.")),
            Describe.Lean(
                DescribeId.Create("latticematterghostcoupling-state"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostCoupling.State"),
                H("The original algebraic tensor carrier"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every lattice data D, State D is Carrier D tensor over the complex numbers with the original countable occupation Fock carrier. No charge sector, finite prefix or completed tensor product replaces either factor."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("latticematterghostcoupling-ghost-b"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostCoupling.ghostB"),
                H("The original b lift"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every D and integer r, ghostB D r is the tensor map id tensor BcGhostFock.b r on State D."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("latticematterghostcoupling-ghost-c"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostCoupling.ghostC"),
                H("The original c lift"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every D and integer r, ghostC D r is the tensor map id tensor BcGhostFock.c r on State D."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("latticematterghostcoupling-matter-mode"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostCoupling.matterMode"),
                H("The actual Sugawara lift"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every D, complex matrix H and integer r, matterMode D H r is sugawaraMode D H r tensor id on State D. The original matter field coefficient is taken at r+1."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("latticematterghostcoupling-ghost-virasoro"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostCoupling.ghostVirasoro"),
                H("The original ghost Virasoro lift"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every D and integer r, ghostVirasoro D r is id tensor BcGhostVirasoro.L r. L is the original pointwise locally finite normal ordered ghost action."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("latticematterghostcoupling-summand"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostCoupling.summand"),
                H("The original matter-c action family"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every D,H and integer m, summand D H m is sugawaraMode D H m tensor BcGhostFock.c (-m), equivalently the product M_m C_{-m}. Its action on each state is proved finitely supported before T is defined."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("latticematterghostcoupling-upper"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostCoupling.upper"),
                H("The actual integer field cutoff"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every D,H and matter state v, upper D H v is max(0,-order(sugawaraField D H applied to v)-2), after the canonical HahnModule identification. The order is integer-valued. The exponent -m-2 comes from the original vertex coefficient m+1."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("latticematterghostcoupling-t"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostCoupling.T"),
                H("The pointwise locally finite coupling"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For arbitrary lattice data D and complex matrix H, T acts on x as the finite-support sum over integers m of the tensor map L_m tensor c_{-m}. The endomorphism family itself is never finitely summed. Additivity and scalar compatibility follow from pointwise finite supports."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("latticematterghostcoupling-summand-finite"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostCoupling.summand_finite"),
                H("Finiteness on every algebraic tensor state"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every D,H,x, the action family m maps to (L_m tensor c_{-m})x has finite support. On a simple tensor v tensor w in ghost radius A, its support lies in [-A,U(v)]. U(v)=max(0,-order(Y_H(v))-2) comes from actual VertexOperator truncation at coefficient m+1. Tensor induction extends the result to every algebraic tensor state."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticematterghostcoupling-t-apply"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostCoupling.T_apply"),
                H("Equality with the actual operator-product local sum"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every tensor state x, T x equals the pointwise finite sum of (M_m C_{-m})x, with M and C the original tensor lifts. This is a formula for a linear map already constructed from state actions."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticematterghostcoupling-finite-capture"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostCoupling.finite_capture"),
                H("Cutoff independence"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every finite set containing the support of the state-action family, its finite sum equals T x. Two valid captures consequently compute the same vector."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticematterghostcoupling-common-capture"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostCoupling.common_capture"),
                H("Joint capture of all prescribed intermediates"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Every finite collection X of tensor states has one finite mode set containing every summand support on X. Taking the finite union also handles sums, scalar multiples and intermediate ghost and matter actions."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticematterghostcoupling-t-tmul"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostCoupling.T_tmul"),
                H("The actual simple-tensor finite formula"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every lattice state v and ghost state w in radius A at least two, T(v tensor w) is the sum over m in [-A,U(v)] of L_m v tensor c_{-m}w. Both endpoints are proved from the original operators."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticematterghostcoupling-ward-b"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostCoupling.ward_b"),
                H("All-integer b Ward identity"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For arbitrary D,H and every integer r, T B_r+B_r T=M_r. The CAR contraction is at the matter index m=r. The summation passes through B_r using the genuine finite supports on x and B_r x."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("latticematterghostcoupling-ward-c"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/LatticeMatterGhostCoupling.ward_c"),
                H("All-integer c Ward identity"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For arbitrary D,H and every integer r, T C_r+C_r T=0. The proof uses the original c CAR and finite support on x and C_r x, with no desired identity assumed."))), DescribeRole.Theorem))));
}
