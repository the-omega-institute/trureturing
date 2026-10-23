using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.NestedResidues.LatticeHalfFockSecondSourceTaylor;

internal sealed class LocalResiduesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Signed current/second-source local residues",
        H("The rational inner field and its ordered coefficients"),
        Blocks(
            Paragraph(Text("The current/second-source diagonal is expanded over the rational field of the two remaining labelled variables v and z. Signed Laurent exponents, the independent spectator pole and both Hahn orders are retained. Local coefficients have finite support on the antidiagonals used by the outer residue.")),
            Describe.Lean(
                DescribeId.Create("second-source-coefficients"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockSecondSourceTaylor/LocalResidues.second_source_coefficients"),
                H("Both actual local coefficient maps come from the same rational field"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice")),
                Blocks(Paragraph(Text("The fractional shift is multiplied into the rational field before expansion. The v,z and z,v coefficient maps then give the two complete lastSourceLocalQ values with their exact shifted mode indices."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("second-source-rational-evaluation"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockSecondSourceTaylor/LocalResidues.second_source_rational_evaluation"),
                H("Finite Laurent evaluation of the inner rational field"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice")),
                Blocks(Paragraph(Text("Each supported numerator monomial is evaluated with its original signed exponent. Summing these local residues gives the explicit finite Taylor rational field at the supplied cutoff K."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("rational-joint-support"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockSecondSourceTaylor/LocalResidues.rational_joint_support"),
                H("Finite support for both ordered outer sums"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice")),
                Blocks(Paragraph(Text("Hahn antidiagonals give finite mode fibers in both orders. A finite union over the fractional outer index gives joint finite support at every natural outer cutoff H and all signed r,n. This does not impose a complete-field locality order on an ordered half."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("source-monomial-complete-residue"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockSecondSourceTaylor/LocalResidues.source_monomial_complete_residue"),
                H("Signed complete residue of a Laurent monomial times the diagonal"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice")),
                Blocks(Paragraph(Text("The difference of the two ordered residues is evaluated for arbitrary signed p,q,t,r,n. The r+t<0 branch gives the exact finite binomial coefficient subject to the degree equation; the complementary branch cancels. Both branches enter the later monomial outer readout."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("source-inner-monomial-normal-form"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockSecondSourceTaylor/LocalResidues.source_inner_monomial_normal_form"),
                H("The original inner Taylor summand as a finite signed Laurent sum"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice")),
                Blocks(Paragraph(Text("The local Taylor index h is kept explicit. Reversing z-v to v-z contributes the exact epsilon factor before the outer coefficient map is applied; all source exponents and the independent spectator pole remain in the expression."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("second-source-inner-taylor-term"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockSecondSourceTaylor/LocalResidues.secondSourceInnerTaylorTerm"),
                H("The signed inner Taylor summand"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice")),
                Blocks(
                    Paragraph(Text("This finite coefficient-field term records the complete signed Laurent factors after the J/B local residue and before either outer Hahn order."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("second-source-monomial-taylor-index"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockSecondSourceTaylor/LocalResidues.second_source_monomial_taylor_index"),
                H("The finite local Taylor index"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice")),
                Blocks(
                    Paragraph(Text("The actual signed monomial residue equals its explicit finite local Taylor expansion on every alpha in range M-j."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("second-source-taylor-inner-expansion"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/NestedResidues/LatticeHalfFockSecondSourceTaylor/LocalResidues.second_source_taylor_inner_expansion"),
                H("The complete signed inner Taylor expansion"),
                StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/VertexAlgebra/bakalovkac2004lattice")),
                Blocks(
                    Paragraph(Text("For every alpha in the actual finite range, secondSourceTerm is expanded over the local Taylor index u < M-j-alpha. The expansion retains signed numerator exponents, both pair poles, the spectator factor and the fractional z^(-alpha) shift. The complete G_j is the finite sum over alpha and the actual coefficient support."))),
                DescribeRole.Theorem))));
}
