using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra.Lattice;

internal sealed class LatticeBRSTCohomologyProductDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Multiplication on original critical BRST cohomology", H("Multiplication on original critical BRST cohomology"), Blocks(
            Paragraph(Text("The carrier is the actual kernel of the original tensor totalCharge modulo its actual image. Rank 26 and both inverse Gram identities remain explicit. The existing b(-1) Ward identity makes the original translation exact on cycles, so translation vanishes on the quotient and covariance kills every mode except -1. Multiplication is the descended bilinear -1 mode. The original supported tensor iterate proves associativity for arbitrary classes. Signed locality gives supercommutativity for homogeneous classes; spectral projections express braiding for arbitrary parity mixtures. Nonzero classes, closure, associativity and locality are not premises.")),
            Paragraph(Text("The original lattice, ghost, Scott Carnahan vertexAlg, Kalle Kytola Sugawara and Mathlib attribution remains in the imported sources. Native compilation, measured axiom closure, semantic registration and formal publication are distinct checks. No literature novelty or completion of string theory or AdS/CFT is claimed.")),
            Describe.Lean(DescribeId.Create("original-brst-product-translation-zero"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyProduct.translation_eq_zero"),
                H("Exact translation vanishes in cohomology"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The original b(-1) operator supplies the boundary witness for every translated cycle."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-brst-product-modes-zero"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyProduct.mode_eq_zero"),
                H("All modes except -1 vanish"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Translation covariance and the nonzero scalar -(k+1) handle every integer k other than -1."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-brst-product-assoc"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyProduct.product_assoc"),
                H("Associativity of the actual -1 product"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Finite action supports are carried through the cycle subtype and quotient before reducing the original iterate sums."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-brst-product-supercomm"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyProduct.product_supercomm"),
                H("Homogeneous supercommutativity"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The exact eigenvalue hypotheses on the two classes determine the Koszul sign; homogeneous cycle lifts are proved in the field supplier."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("original-brst-product-mixed-braiding"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/Lattice/LatticeBRSTCohomologyProduct.product_mixed_braiding"),
                H("Braiding for arbitrary mixed classes"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The four even and odd terms retain the actual quotient parity projections."))), DescribeRole.Theorem))));
}
