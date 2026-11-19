using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.PartialTransposeSaturation;

internal sealed class PartialTransposeSaturationSufficiencyDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Entanglement/PartialTransposeSaturation/Sufficiency.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Eigenstructure/wangchen2025partialtranspose");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Concatenation criteria sufficient for partial transpose saturation", H("Sufficiency"),
        Blocks(
            Paragraph(Text("All ranks are ordinary complex matrix ranks. Index types may be arbitrary finite types, including empty types. Wang and Chen give the general bound that partial transpose rank is at most the number of tensor summands times the original rank. The assertions here prove two sufficient equality families for two summands.")),
            Describe.Lean(DescribeId.Create("tensorsum"),
                DeclarationHandle.Create(Prefix + "tensorSum"), H("Two coefficient tensor sum"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("For arbitrary complex rectangular coefficient matrices the row index is the ordered product of output indices and the column index is the ordered product of input indices. The matrix is A1 tensor B1 plus A2 tensor B2."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("partialtranspose"),
                DeclarationHandle.Create(Prefix + "partialTranspose"), H("First factor partial transpose"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Transpose both first-factor coefficient matrices while retaining the second-factor pair. The first-factor input and output indices exchange places. This convention agrees with first-factor transposition in the source rank inequality."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("hrank"),
                DeclarationHandle.Create(Prefix + "hRank"), H("Horizontal concatenation rank"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The ordinary matrix rank of the horizontal concatenation of the two coefficient matrices."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("vrank"),
                DeclarationHandle.Create(Prefix + "vRank"), H("Vertical concatenation rank"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("The ordinary matrix rank of the vertical concatenation of the two coefficient matrices."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("tensorsum-eq-zero-iff"),
                DeclarationHandle.Create(Prefix + "tensorSum_eq_zero_iff"), H("An independent pair detects both other coefficients"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("If A1 and A2 are linearly independent as matrices, their tensor sum with B1 and B2 vanishes exactly when both B1 and B2 vanish. Coefficient independence applies separately at every second-factor matrix entry. Empty and rectangular index types are included."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("rank-tensorsum-change"),
                DeclarationHandle.Create(Prefix + "rank_tensorSum_change"), H("Coordinate invariance of tensor sum rank"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("When all four square change matrices have invertible determinants, the transformed tensor sum has the original rank."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("joint-control-iff"),
                DeclarationHandle.Create(Prefix + "joint_control_iff"), H("Independent prescription of the two outputs"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Vertical concatenation rank is twice horizontal concatenation rank exactly when every ordered pair of vectors in the sum of the coefficient images is attained by the joint output map. Its image lies in the product of that common image with itself. Equal finite dimensions force equality of the two subspaces."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("rank-tensorsum-of-jointsurjective"),
                DeclarationHandle.Create(Prefix + "rank_tensorSum_of_jointSurjective"), H("Tensor rank from independent output control"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Suppose the second pair can attain every ordered pair of vectors in its combined image. The tensor sum has rank equal to the product of the dimensions of the combined images of the two pairs. For each pure tensor, prescribe one second-factor output and set the other to zero. These preimages give both inclusions in the exact tensor rectangle range equality. The dimension of that rectangle is the product of the dimensions of its factors."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("rank-tensorsum-of-vertical-saturated"),
                DeclarationHandle.Create(Prefix + "rank_tensorSum_of_vertical_saturated"), H("The untransposed rank from one saturated pair"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For arbitrary A1 and A2, if the vertical rank of the B pair is twice its horizontal rank, the tensor sum has rank hA times hB. No independent coefficient assumption is needed."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("rank-partialtranspose-of-vertical-saturated"),
                DeclarationHandle.Create(Prefix + "rank_partialTranspose_of_vertical_saturated"), H("The transposed rank from one saturated pair"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Under the same hypothesis on B, the first-factor partial transpose has rank vA times hB. Apply the tensor rank formula to the transposed A pair and use the concatenation transpose identity."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("saturation-of-vertical"),
                DeclarationHandle.Create(Prefix + "saturation_of_vertical"), H("The vertical saturation family"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("If vA equals twice hA and vB equals twice hB, the tensor sum has rank hA times hB and its partial transpose has twice that rank."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("saturation-of-horizontal"),
                DeclarationHandle.Create(Prefix + "saturation_of_horizontal"), H("The horizontal saturation family"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("If hA equals twice vA and hB equals twice vB, the partial transpose again has twice the original rank. Transpose both coefficient pairs, apply the vertical family, and use invariance of rank under full transposition."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("finrank-tensorsum-tomatrix"),
                DeclarationHandle.Create(Prefix + "finrank_tensorSum_toMatrix"), H("Tensor rank in arbitrary finite bases"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The rank of the sum of two tensor products of linear maps equals the rank of the Kronecker sum of their matrices in any four finite bases. Tensor product bases identify the maps, and matrix rank is the dimension of their image."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("sufficient"),
                DeclarationHandle.Create(Prefix + "sufficient"), H("Sufficiency of the concatenation test"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For any four finite rectangular complex coefficient matrices, either pair of matching concatenation rank equalities implies that the partial transpose has twice the original rank. This is the sufficient direction of the proposed criterion. It imposes no linear independence assumptions. The necessity direction for arbitrary coefficient pairs is outside this statement."))), DescribeRole.Theorem))));
}
