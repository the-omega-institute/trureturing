using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.ObservationTopology;

internal sealed class DiagonalTopologicalEscapeDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/ObservationTopology/DiagonalTopologicalEscape.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete relative diagonals force discontinuity and strict refinement.",
        H("Diagonal Topological Escape"),
        Blocks(Describe.Lean(
            DescribeId.Create("complete-relative-diagonal-settlement"),
            DeclarationHandle.Create(Prefix + "complete_diagonal_topological_settlement"),
            H("A complete relative diagonal settles four topological failures"),
            StatementSource.FromAuthor(SettlementFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Assume an inhabited address space, a fixed-point-free output twist, and "
                        + "a decoder catalog surjective onto all coordinate-indexed output "
                        + "functions.")),
                Paragraph(Text(
                    "The relative semantic diagonal twists the catalog entry selected by "
                        + "the latent coordinate. Catalog completeness makes this target "
                        + "impossible to recover from the latent readout.")),
                Paragraph(Text(
                    "That non-factorization is equivalently discontinuity from the latent "
                        + "partition topology to the discrete output topology, and it leaves "
                        + "a nonempty separation deficit.")),
                Paragraph(Text(
                    "Adjoining the diagonal target as a coordinate separates a pair that the "
                        + "latent observation could not separate, so the resulting partition "
                        + "topology is a strict observation refinement. The displayed theorem "
                        + "asserts all four conclusions simultaneously under exactly the "
                        + "listed hypotheses."))),
            DescribeRole.Theorem))));

    private static Formula Arrow(Formula source, Formula target) =>
        Seq(source, Sp, To, Sp, target);

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula SettlementFormula()
    {
        Formula address = F.Id("Address");
        Formula coordinate = F.Id("Coordinate");
        Formula outputType = F.Id("Output");
        Formula twist = F.Id("twist");
        Formula latent = F.Id("latent");
        Formula catalog = F.Id("decoderCatalog");
        Formula output = F.Id("output");
        Formula diagonal = Call(
            "relativeSemanticDiagonal",
            twist,
            latent,
            catalog);
        Formula fixedPointFree = Seq(
            Forall, Sp, output, Colon, Sp, outputType, Comma, Sp,
            Apply(twist, output), Sp, Neq, Sp, output);
        Formula hypotheses = Seq(
            Open, fixedPointFree, Close, Sp, Land, Sp,
            Call("Surjective", catalog));
        Formula discontinuity = Seq(
            Neg, Sp,
            Call(
                "Continuous",
                Call("partitionTopology", latent),
                Call("bottomTopology", outputType),
                diagonal));
        Formula strictRefinement = Call(
            "StrictObservationRefinement",
            Call("partitionTopology", latent),
            Call(
                "partitionTopology",
                Call("conceptJoin", latent, diagonal)));
        Formula conclusions = Seq(
            Neg, Sp, Call("Refines", diagonal, latent), Sp, Land, RowBreak, Grp(),
            discontinuity, Sp, Land, RowBreak, Grp(),
            Call("Nonempty", Call("separationDeficit", latent, diagonal)),
            Sp, Land, RowBreak, Grp(),
            strictRefinement);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, twist, Colon, Sp, Arrow(outputType, outputType), Comma, Sp,
            latent, Colon, Sp, Call("Concept", address, coordinate), Comma, Sp,
            catalog, Colon, Sp,
            Arrow(address, Arrow(coordinate, outputType)), Comma, RowBreak, Grp(),
            OpenBracket, Call("Nonempty", address), CloseBracket, Sp,
            Open, hypotheses, Close, Sp, Rightarrow, RowBreak, Grp(),
            Open, conclusions, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
