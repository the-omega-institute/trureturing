using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class OriginalNonzeroGhostMultiplicityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "At each integral native level, the released original projection has an explicit finite weighted-transverse basis with native J degrees one and two.",
        H("Actual Nonzero-Charge Transverse Multiplicity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("actual-transverse-index-finite"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/OriginalNonzeroGhostMultiplicity.transverseLevelIndex_finite"),
                H("Finite actual transverse index"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("level"), Sp, Rightarrow, Sp, Call("Finite", F.Id("transverseLevelIndex"))))),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The index contains all finite oscillator exponents with both longitudinal occupations zero, ghost subset contained in {3}, and exact native level.")))),
            Describe.Lean(
                DescribeId.Create("actual-transverse-count"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/OriginalNonzeroGhostMultiplicity.nativeTransverseEnergy_finrank"),
                H("Complete basis and exact count"),
                StatementSource.FromAuthor(Disp(Seq(
                    Call("finrank", F.Id("Complex"), F.Id("nativeTransverseEnergySpace")),
                    Sp, Eq, Sp, Call("card", F.Id("transverseLevelIndex"))))),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The range-energy space is spanned by the actual native words and the index map is linearly independent; this is not a formal generating function.")))),
            Describe.Lean(
                DescribeId.Create("actual-transverse-j-degree"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/OriginalNonzeroGhostMultiplicity.nativeTransverseEnergyBasis_J_degree"),
                H("Native J degrees"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("J"), Sp, Eq, Sp, F.Id("degree"), Times, Sp, F.Id("basis")))),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The empty ghost partner has native degree one and the c0 partner has native degree two. The absolute partner is retained.")))),
            Describe.Lean(
                DescribeId.Create("actual-transfer-j-covariance"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/OriginalNonzeroGhostTransferJ.J0_finite_transferred_differential_commutator"),
                H("Actual transfer covariance"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("J"), Sp, InMacro, Sp, F.Id("finiteOriginalCorrectionInverse"), Sp, Eq, Sp, Num(0), Comma, Sp,
                    F.Id("J"), Sp, InMacro, Sp, F.Id("finiteOriginalTransferredDifferential"), Sp, Eq, Sp,
                    F.Id("finiteOriginalTransferredDifferential")))),
                AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The actual finite original-Q transfer has a genuine native J degree. The true quotient transfer remains the original Q transfer, not reduced delta cohomology."))))
        )));
}
