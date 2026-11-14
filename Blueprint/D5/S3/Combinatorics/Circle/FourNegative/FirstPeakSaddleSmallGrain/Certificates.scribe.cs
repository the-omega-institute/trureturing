using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.FourNegative.FirstPeakSaddleSmallGrain;

internal sealed class CertificatesDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Nineteen direct c=2 margins",
        H("Twelve unbounded phase charts"),
        Blocks(
            Describe.Lean(DescribeId.Create("helper-certificates-1"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddleSmallGrain/Certificates.margin"),
                H("Physical seams followed by capacities"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("At z=4 put D=5y+1, A=xD+1, B=xt(y+1)+t+1, L=4xt+4t+5 and M=4ty+D. The first twelve Fin19 entries are the exact old and enlarged seam pairs. The seven additional entries are s-1,x-2s,r-1,s-r,v,t-2v-2,y-8(h+1). Margins requires all nineteen to be nonnegative."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("helper-certificates-2"),
                DeclarationHandle.Create("D5/S3/Combinatorics/Circle/FourNegative/FirstPeakSaddleSmallGrain/Certificates.chart_K1_J1_0"),
                H("A direct phase chart with unbounded T"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The twelve retained theorems chart_K1_J1_0 through _3, chart_K1_J2_0 through _3 and chart_K2_J1_0 through _3 use t=16,32,64,128 plus 10T with T>=0 and the explicit native s,r,h,v. Each proves nineteen polynomial inequalities. The three t=8 exceptions are inline in Arithmetic.select_chart rather than standalone named certificates. No finite exponent cutoff or external certificate is a premise."))), DescribeRole.Lemma),
            Paragraph(Text("These existing private declarations are consumed by the strict-saddle endpoint. This mirror documents their stated hypotheses and use; it makes no independent literature-novelty claim, no claim of a four-slot registration for every helper, and no claim to settle unrestricted four-gap J or Circle Conjecture 3.1."))), []));
}
