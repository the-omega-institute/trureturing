using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.PrimeGaps;

internal sealed class PrimeWeilFoundationsRootDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "One local import root assembles the fragment, mixed-form and quadratic-probe proof modules without duplicating their definitions.",
        H("Prime and Weil Foundations Root"), Blocks(
            Paragraph(Text("FragmentMeshTruncation imports the actual FragmentLaw and proves the retained/deleted mass and mesh-event bounds. ScaledComplexQuadraticRowBound imports the existing ComplexQuadraticRowBound and adds positive diagonal scaling, absolutely convergent matrix coefficients, geometric envelopes and robust margins. QuadraticObserverPolarization supplies the unchanged three-probe reconstruction and strict joint-kernel results.")),
            Paragraph(Text("This file contains imports only. Building this root checks its mathematical dependency closure; it does not by itself establish a maximal canonical information-escape catalog, complete AnalysisDisposition coverage, repository admission or a frozen truth release. The five mathematical modules each have a separate companion Scribe source."))
        )));
}
