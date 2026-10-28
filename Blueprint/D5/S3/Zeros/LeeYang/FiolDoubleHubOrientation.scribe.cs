using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.LeeYang;

internal sealed class FiolDoubleHubOrientationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The physical double-hub family: orientation.",
        H("Double-hub orientation"), Blocks(
            Paragraph(Text("For any finite endpoint maps, reverse a chosen set of arrows and replace k_e by n_e-k_e on precisely those edges. This is an involution of the complete admissible split set. It preserves every vertex mass and the full factorial weight. Reindexing the complete sum proves arrow reversal invariance; an individual unsummed split is not asserted invariant.")),
            Paragraph(Text("These new declarations are absent from the pinned statement-projection corpus. The supported omission records that projection gap; the mathematical argument and exact theorem statements are given in this document. No projection entry or judge is changed.")),
            Describe.Lean(DescribeId.Create("fioldoublehuborientation-polynomial"),
                DeclarationHandle.Create("D5/S3/Zeros/LeeYang/FiolDoubleHubOrientation.polynomial"), H("polynomial"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This defines polynomial for the physical double-hub family."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("fioldoublehuborientation-polynomial-reverse"),
                DeclarationHandle.Create("D5/S3/Zeros/LeeYang/FiolDoubleHubOrientation.polynomial_reverse"), H("polynomial reverse"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Reindexes the full weighted source by that split involution. Exact source statement: theorem polynomial_reverse {V E : Type} [Fintype V] [Fintype E] [DecidableEq E] [DecidableEq V]     (s t : E \u2192 V) (n : E \u2192 \u2115) (f : E \u2192 Bool) :     polynomial (reverseSrc s t f) (reverseTgt s t f) n=polynomial s t n."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("fioldoublehuborientation-actual-arrow-sum-invariance"),
                DeclarationHandle.Create("D5/S3/Zeros/LeeYang/FiolDoubleHubOrientation.actual_arrow_sum_invariance"), H("actual arrow sum invariance"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Connects the full reversed physical source with the original independent source. Exact source statement: theorem actual_arrow_sum_invariance (m : \u2115) (n : Edge m \u2192 \u2115)     (f : Edge m \u2192 Bool) :     polynomial (reverseSrc (src : Edge m \u2192 Vertex m) tgt f)       (reverseTgt src tgt f) n=allVertexSource n."))), DescribeRole.Theorem))));
}
