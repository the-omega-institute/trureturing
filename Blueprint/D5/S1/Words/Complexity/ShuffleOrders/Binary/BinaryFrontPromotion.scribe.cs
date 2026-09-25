using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Words.Complexity.ShuffleOrders.Binary;

internal sealed class ShuffleOrdersBinaryBinaryFrontPromotionDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S1/Words/Complexity/ShuffleOrders/Binary/BinaryFrontPromotion";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Words/nilforoushanparvaresh2026kdecks");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A smaller leading source can be promoted without decreasing evaluation.",
        H("BinaryFrontPromotion"),
        Blocks(
            Paragraph(Text(
                "The source paper uses shuffle products and retains their alignment multiplicities. "
                + "This repository module supplies the fixed-source occurrence bookkeeping needed "
                + "later: equal letters and duplicate source factors are never identified.")),
            D("fixed-source-front-promotion", "fixedSource_frontPromotion", "Promote the larger source to the front",
                "For linearly ordered A, fixed words first>=second, a valid schedule starting with second, and a successful evaluation word, there exist a valid promoted schedule starting with first and an evaluated promotedWord with word<=promotedWord. Both source words and every occurrence are retained.", literature: false))));

    private static DocumentBlock.Describe D(string id, string declaration, string title,
        string prose, DescribeRole role = DescribeRole.Theorem, bool literature = false) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Module + "." + declaration),
            H(title), StatementSource.FromAuthor(Disp(F.Id(declaration.Replace("_", string.Empty)))),
            literature ? AssessedProvenance.FromLiterature(Source) : AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
