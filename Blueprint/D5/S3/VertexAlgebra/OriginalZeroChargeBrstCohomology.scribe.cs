using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.VertexAlgebra;

internal sealed class OriginalZeroChargeBrstCohomologyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Explicit representatives and inverse coordinates for the actual exceptional cohomology.",
        H("Complete Original Cohomology Coordinates"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("exceptional-quotient-kernel"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/OriginalZeroChargeBrstCohomology.quotientCoordinates_kernel"),
                H("No hidden quotient classes"),
                StatementSource.FromAuthor(Disp(Seq(
                    Call("ker", F.Id("quotientCoordinates")), Sp, Eq, Sp,
                    Call("boundarySubmoduleInCycles", F.Id("D"))))),
                AssessedProvenance.FromRepo(), Blocks(
                Paragraph(Text("Coordinates retain every sector label except the c0 ground vector and the pure {1,5} ground vector. On cycles the first omitted coordinate is already zero. If all retained coordinates vanish, basis injectivity says the cycle is its pure-pair coefficient times that basis vector, hence a true boundary. Conversely every true boundary has all retained coordinates zero.")))),
            Describe.Lean(
                DescribeId.Create("exceptional-original-quotient-inverse"),
                DeclarationHandle.Create("D5/S3/VertexAlgebra/OriginalZeroChargeBrstCohomology.cohomologyCoordinates"),
                H("Explicit basis and inverse"),
                StatementSource.FromAuthor(Disp(Seq(
                    Call("Cohomology", F.Id("D")), Sp, Equiv, Sp,
                    Call("FiniteSupport", F.Id("survivingLabels"), F.Id("Complex"))))),
                AssessedProvenance.FromRepo(), Blocks(
                Paragraph(Text("The right inverse extends every finite coefficient function by zero on the omitted labels, then applies the actual sector basis inverse. Its c0 coefficient vanishes, so it is a cycle. This right inverse and the exact kernel identify the true quotient with all finite coefficient functions on the surviving labels.")),
                Paragraph(Text("The surviving representatives are the vacuum ground tensor, the {1,3,5} ground tensor, and for each matter axis its frequency-one excitation with {1} or {1,3}. In particular the triple and the excited c0-containing states are retained; ghost zero modes are not silently discarded."))))
        )));
}
