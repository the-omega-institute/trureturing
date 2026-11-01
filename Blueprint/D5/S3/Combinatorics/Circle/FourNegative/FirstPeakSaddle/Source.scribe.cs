using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSaddle;

internal sealed class SourceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Literal source recurrences and centered bounds",
        H("Four original chains and their enlarged counterparts"),
        Blocks(
            Describe.Lean(DescribeId.Create("helper-source-1"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddle/Source.source_recurrences"),
                H("Eight exact recurrences"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The four source chain lengths are d,c,b,a. With N=xyzt-1 and Q=2N+1, the recurrences are tA=N+B, zB=N+L, yL=N+M, xM=N+A and t(2A)=Q+Bn, zBn=Q+Ln, yLn=Q+Mn, xMn=Q+A. The proof checks each native Fin4 index by ring normalization using the existing PacketNormalForm.Source constants."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("helper-source-2"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddle/Source.source_parity"),
                H("Odd bases and successors"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a,b,c,d>=2, the old modulus and old bases are odd, as are all enlarged successors. The enlarged first base 2A is even; no assertion that every enlarged base is odd is made."))), DescribeRole.Lemma),
            Describe.Lean(DescribeId.Create("helper-source-3"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddle/Source.source_centered_bounds"),
                H("Bounds for exact ladder reduction"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The old and enlarged bases lie from 1 to their respective modulus minus two. The proof reuses chain_values and new_base_bounds and combines parity with nonnegative charge. Physical uses these bounds and the recurrences to control the actual centered residues; no second source realization is assumed."))), DescribeRole.Lemma),
            Paragraph(Text("These existing private declarations are consumed by the strict-saddle endpoint. This mirror documents their stated hypotheses and use; it makes no independent literature-novelty claim, no claim of a four-slot registration for every helper, and no claim to settle unrestricted four-gap J or Circle Conjecture 3.1."))), []));
}
