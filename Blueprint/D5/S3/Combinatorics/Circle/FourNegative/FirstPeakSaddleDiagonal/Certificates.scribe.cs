using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSaddleDiagonal;

internal sealed class CertificatesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Polynomial margins for strict and equality diagonals",
        H("Exact corner certificates"),
        Blocks(
            Describe.Lean(DescribeId.Create("helper-certificates-1"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddleDiagonal/Certificates.scaledMargin"),
                H("Four scaled rectangle margins"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The private constants D,A,B,L,M,Bn,Ln,Mn fix the same literal source algebra as the physical constructor. grain=4*K*J and reserve=2*K*J*t-grain. scaledMargin, rectangleMargin and boundaryMargin encode the four signed slacks used by the diagonal selector; gateMargin keeps the corresponding twelve physical seam bounds."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("helper-certificates-2"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddleDiagonal/Certificates.chart_strict_neg1"),
                H("Unbounded strict-diagonal corner family"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Seven strict charts supply four margins each. The equality boundary uses six charts with K>=2 and six with J>=2, again four margins each. Each chart states explicit nonnegative polynomial slacks for nonnegative shifted integer parameters and proves them by ring normalization and positivity. GeneralArithmetic consumes these exact terms through its corner lemmas. This module supplies 28 strict and 48 equality margins; it does not by itself construct a physical word."))), DescribeRole.Lemma),
            Paragraph(Text("These existing private declarations are consumed by the strict-saddle endpoint. This mirror documents their stated hypotheses and use; it makes no independent literature-novelty claim, no claim of a four-slot registration for every helper, and no claim to settle unrestricted four-gap J or Circle Conjecture 3.1."))), []));
}
