using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class OriginalZeroChargeBrstGradingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exceptional quotient is graded by the original integer ghost-number operator.",
        H("Native Integer Ghost Grading"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("exceptional-original-number-descent"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/OriginalZeroChargeBrstGrading.cohomologyNumber_native"),
                H("Number operator on actual classes"),
                StatementSource.FromAuthor(Disp(Seq(
                    Call("cohomologyNumber", Call("class", F.Id("v"))), Sp, Eq, Sp,
                    Call("class", Call("cycleNumber", F.Id("v")))))),
                AssessedProvenance.FromRepo(), Blocks(
                Paragraph(Text("The sector number operator is proved equal to the restriction of the original tensor J. Coordinates show it preserves cycles and descends on the exact quotient. The descended operator is not assumed to be a ghost-current zero mode.")))),
            Describe.Lean(
                DescribeId.Create("exceptional-number-eigenspaces"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/OriginalZeroChargeBrstGrading.mem_graded_iff_number"),
                H("True integer eigenspaces"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("x"), Sp, InMacro, Sp, Call("gradedCohomology", F.Id("r")), Sp, Iff, Sp,
                    Call("cohomologyNumber", F.Id("x")), Sp, Eq, Sp, F.Id("r"), Times, Sp, F.Id("x")))),
                AssessedProvenance.FromRepo(), Blocks(
                Paragraph(Text("A class belongs to degree r exactly when all its surviving coefficients outside degree r vanish. The proved native number correspondence identifies this support condition with the eigenvalue equation, rather than merely attaching integer labels to a basis.")))),
            Describe.Lean(
                DescribeId.Create("exceptional-graded-dimensions"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/OriginalZeroChargeBrstGrading.graded_finrank"),
                H("Every ghost degree"),
                StatementSource.FromAuthor(Disp(Seq(
                    Call("finrank", F.Id("Complex"), Call("gradedCohomology", F.Id("D"), F.Id("r"))),
                    Sp, Eq, Sp, Call("gradedDimension", F.Id("D"), F.Id("r"))))),
                AssessedProvenance.FromRepo(), Blocks(
                Paragraph(Text("The dimensions are 1 in degree 0, rank(D) in degree 1, rank(D) in degree 2, 1 in degree 3, and zero in every other integer degree. The explicit survivor equivalence and homogeneous coordinate basis prove this table. At rank 26 it is 1, 26, 26, 1; this substitution contributes no new mathematical content.")),
                Paragraph(Text("The vacuum is assigned number zero. Every occupied creator in this energy fiber is a c creator, including the site-3 c0 mode, so its degree is its number of occupied sites. Conventions assigning a shifted number to the vacuum shift this table; they do not alter the actual source J or the native quotient.")))),
            Describe.Lean(
                DescribeId.Create("exceptional-homogeneous-native-representatives"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/OriginalZeroChargeBrstGrading.homogeneous_representative"),
                H("Homogeneous actual representatives"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("x"), Sp, InMacro, Sp, Call("gradedCohomology", F.Id("r")), Sp, Rightarrow, Sp,
                    Call("class", Call("representative", Call("coordinates", F.Id("x")))), Sp, Eq, Sp,
                    F.Id("x"), Sp, Land, Sp,
                    Call("J", Call("representative", Call("coordinates", F.Id("x")))), Sp, Eq, Sp,
                    F.Id("r"), Times, Sp, Call("representative", Call("coordinates", F.Id("x")))))),
                AssessedProvenance.FromRepo(), Blocks(
                Paragraph(Text("Every homogeneous quotient class, including every finite superposition, has the explicitly constructed actual cycle representative of that same integer J degree. Its class is exactly the original class, and the descended J agrees with applying the native J before taking the class. This is a proved representative construction, not a spectral assumption.")))),
            Describe.Lean(
                DescribeId.Create("exceptional-original-boundary-preimages"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/OriginalZeroChargeBrstGrading.original_boundary_homogeneous_preimage"),
                H("Original Q and the shifted degree"),
                StatementSource.FromAuthor(Disp(Seq(
                    Call("homogeneousBoundary", F.Id("v"), F.Id("r")), Sp, Rightarrow, Sp,
                    Exists, Sp, F.Id("w"), Comma, Sp,
                    Call("Q", F.Id("w")), Sp, Eq, Sp, F.Id("v"), Sp, Land, Sp,
                    Call("J", F.Id("w")), Sp, Eq, Sp,
                    Open, F.Id("r"), Minus, Num(1), Close, Times, Sp, F.Id("w")))),
                AssessedProvenance.FromRepo(), Blocks(
                Paragraph(Text("The native J-Q commutator proves Q shifts integer degree by one. Every homogeneous actual boundary in degree r has an actual sector preimage in degree r-1. A nonzero boundary necessarily has degree 2 and is a multiple of the pure pair; its preimage is half that multiple of the c0 ground vector, of degree 1. The zero boundary has the zero preimage in every degree."))))
        )));
}
