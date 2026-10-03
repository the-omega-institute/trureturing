using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.CharacterSelection;

internal sealed class PeriodicGridHolonomyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Fourier/CharacterSelection/PeriodicGridHolonomy.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Binary plaquette flatness on a periodic rectangle has exactly two global seam bits.",
        H("Periodic Grid Holonomy"),
        Blocks(
            Describe.Lean(DescribeId.Create("edge-label"),
                DeclarationHandle.Create(Prefix + "EdgeLabel"), H("Periodic edge labels"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A label has horizontal and vertical ZMod 2 values indexed by Fin M and Fin N. "
                    + "For M,N at least three these index the two edge directions of the simple "
                    + "periodic rectangular grid."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("plaquette"),
                DeclarationHandle.Create(Prefix + "plaquette"), H("Plaquette sum"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The plaquette at (i,j) is s(i,j)+u(i,j+1)+s(i+1,j)+u(i,j), "
                    + "with the additions in the two Fin indices taken cyclically."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("flat"),
                DeclarationHandle.Create(Prefix + "Flat"), H("Flat edge labels"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Flatness means every plaquette sum vanishes."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("row-holonomy"),
                DeclarationHandle.Create(Prefix + "rowHolonomy"), H("Horizontal holonomy"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The horizontal holonomy of a row is the sum of its horizontal labels."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("column-holonomy"),
                DeclarationHandle.Create(Prefix + "columnHolonomy"), H("Vertical holonomy"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The vertical holonomy of a column is the sum of its vertical labels."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("gradient"),
                DeclarationHandle.Create(Prefix + "gradient"), H("Vertex differential"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The horizontal and vertical labels of a vertex potential are the binary "
                    + "sums of its endpoint values."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("seam"),
                DeclarationHandle.Create(Prefix + "seam"), H("Two seam labels"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A horizontal seam value h occupies precisely the edges at the final column. "
                    + "A vertical seam value v occupies precisely the edges at the final row."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("flat-holonomy-constant"),
                DeclarationHandle.Create(Prefix + "flat_holonomy_constant"),
                H("Holonomy is constant across rows and columns"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a flat label, every row has the holonomy of row zero and every column "
                    + "has the holonomy of column zero. Summing one strip of plaquettes proves each equality."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("flat-decomposition"),
                DeclarationHandle.Create(Prefix + "flat_decomposition"),
                H("Gradient and seam decomposition"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Every flat binary edge label is the sum of a vertex differential and a seam "
                    + "whose values are its two holonomies. The vertex value at (0,0) is fixed to zero. "
                    + "The proof constructs the potential by cyclic integration and uses each plaquette "
                    + "to transfer horizontal differences between rows."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("flat-exact-iff"),
                DeclarationHandle.Create(Prefix + "flat_exact_iff"), H("Exact lift criterion"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A flat label is a single-valued periodic vertex differential exactly when "
                    + "both its horizontal and vertical holonomies vanish."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("horizontal-seam-counterexample"),
                DeclarationHandle.Create(Prefix + "horizontal_seam_counterexample"),
                H("Non-exact flat seam"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every M,N at least three, the seam with horizontal value one and vertical "
                    + "value zero is flat, has holonomy (1,0), and admits no periodic vertex lift. "
                    + "The argument uses no parity condition on M or N."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("flat-label-card"),
                DeclarationHandle.Create(Prefix + "flat_label_card"), H("Number of flat labels"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For positive M,N there are exactly 2^(MN+1) flat labels. The proof uses a "
                    + "bijection with anchored vertex assignments and two independent binary holonomies."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("holonomy-sector-card"),
                DeclarationHandle.Create(Prefix + "holonomy_sector_card"),
                H("Equal-size holonomy sectors"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every prescribed pair of binary holonomies, the corresponding flat sector "
                    + "contains exactly 2^(MN-1) labels. In particular all four sectors are nonempty."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("plaquette-relation-rank-one"),
                DeclarationHandle.Create(Prefix + "plaquette_relation_rank_one"),
                H("Unique plaquette relation"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A binary linear combination of plaquette equations vanishes for every edge "
                    + "label exactly when all its coefficients are equal. Single-edge labels force "
                    + "adjacent coefficients to agree in both directions; the all-one relation "
                    + "follows by summing every plaquette."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("edge-label-card"),
                DeclarationHandle.Create(Prefix + "edge_label_card"), H("Number of all labels"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The two edge directions contain 2MN binary positions, giving 2^(2MN) labels."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("exact-label-card"),
                DeclarationHandle.Create(Prefix + "exact_label_card"), H("Number of liftable labels"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Exactly 2^(MN-1) labels are periodic vertex differentials. They are the "
                    + "zero-holonomy sector among the flat labels."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("edge-space"),
                DeclarationHandle.Create(Prefix + "EdgeSpace"), H("Binary edge-coordinate space"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The two arrays of periodic edge labels form a product vector space over ZMod 2."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("plaquette-linear"),
                DeclarationHandle.Create(Prefix + "plaquetteLinear"), H("Linear plaquette map"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "This linear map sends each edge assignment to its array of cyclic "
                    + "plaquette sums."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("flat-subspace"),
                DeclarationHandle.Create(Prefix + "flatSubspace"), H("Flat kernel"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The kernel of the plaquette map consists exactly of the flat edge labels."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("periodic-grid-linear-statistics"),
                DeclarationHandle.Create(Prefix + "periodic_grid_linear_statistics"),
                H("Plaquette rank, flat dimension, and uniform proportions"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The plaquette equations form an actual ZMod 2 linear map on the two "
                    + "edge-coordinate spaces. Its kernel is identified with flat labels, "
                    + "giving kernel dimension MN+1; rank-nullity gives plaquette rank MN-1. "
                    + "Both finite-uniform denominators are positive. Exact labels occupy "
                    + "1/4 of flat labels, while flat and exact labels occupy respectively "
                    + "1/2^(MN-1) and 1/2^(MN+1) of all edge labels."))),
                DescribeRole.Theorem))));
}
