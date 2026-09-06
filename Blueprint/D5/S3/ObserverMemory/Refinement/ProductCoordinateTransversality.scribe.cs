using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.Refinement;

internal sealed class ProductCoordinateTransversalityDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ObserverMemory/Refinement/ProductCoordinateTransversality.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Independent local and layer coordinates have singleton cross-fibers, commuting coordinate updates, and a faithful paired observer.",
        H("Product Coordinate Transversality"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("local-fiber-inter-layer-fiber"),
                DeclarationHandle.Create(Prefix + "local_fiber_inter_layer_fiber"),
                H("A local fiber and a layer fiber meet in one state"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("intersection")),
                    Open,
                    Operatorname, Grp(F.Id("localFiber")), Open, F.Id("local"), Close,
                    Comma, Sp,
                    Operatorname, Grp(F.Id("layerFiber")), Open, F.Id("layer"), Close,
                    Close,
                    Sp, Eq, Sp,
                    OpenBrace, Open, F.Id("local"), Comma, Sp, F.Id("layer"), Close,
                    CloseBrace, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Fixing both independent coordinates identifies exactly one product state.")),
                    Paragraph(Text(
                        "This is the set-theoretic transversality used for local-channel and golden-layer addresses; no metric or inner-product orthogonality is asserted."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("local-move-layer-move-commute"),
                DeclarationHandle.Create(Prefix + "local_move_layer_move_commute"),
                H("Independent coordinate moves commute"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("localMove")),
                    Sp, Circ, Sp,
                    Operatorname, Grp(F.Id("layerMove")),
                    Sp, Eq, Sp,
                    Operatorname, Grp(F.Id("layerMove")),
                    Sp, Circ, Sp,
                    Operatorname, Grp(F.Id("localMove")), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "An update confined to the local coordinate commutes with an update confined to the layer coordinate.")),
                    Paragraph(Text(
                        "The paired repository readout is faithful and each single-coordinate readout remains blind to motion in the other direction."))),
                DescribeRole.Theorem))));
}
