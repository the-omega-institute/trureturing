using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.WeylChronology;

internal sealed class GoldenWordInterferometryDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A word and its reverse share a displacement endpoint and differ by twice the Magnus phase.",
        H("Chronology in Displacement Interference"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("word-reversal-weyl-phase"),
                DeclarationHandle.Create("D5/S3/Quantum/WeylChronology/GoldenWordInterferometry.word_reverse_relative_phase"),
                H("The exact relative phase"),
                StatementSource.FromAuthor(Relative()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("True letters apply real displacement a and false letters apply imaginary displacement ib. The list head acts first. The existing magnusCenter, equal to 2P-rz, supplies the integer coordinate.")),
                    Paragraph(Text("Each word has phase ab times its Magnus center. Comparing it with its reverse doubles this phase while keeping the endpoint displacement equal. This is ordinary coherent path comparison, not antiunitary time reversal or an indefinite-causal-order advantage claim."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("count-only-compensated-phase"),
                DeclarationHandle.Create("D5/S3/Quantum/WeylChronology/GoldenWordInterferometry.endpoint_compensated_word_phase"),
                H("A count-only reference"),
                StatementSource.FromAuthor(Compensated()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Endpoint compensation applies D(-ar,-bz) after the signal word. It depends only on the two counts, and returns any input wavefunction with the scalar phase exp(iabm).")),
                    Paragraph(Text("A coherent unchanged-state reference then gives plus probability (1+cos(abm-theta))/2 for normalized input. This improves the operational requirement: the reference no longer needs to replay the reversed signal word. Coherent controlled execution and repeated preparations are still required."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("word-recombination-fringe"),
                DeclarationHandle.Create("D5/S3/Quantum/WeylChronology/GoldenWordInterferometry.plus_output_factorization"),
                H("The observable interference amplitude"),
                StatementSource.FromAuthor(Output()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The reference arm executes the reversed word. The signal arm has analyzer phase minus theta. After recombination, the output factorizes into the Ramsey coefficient and the common reference wavefunction.")),
                    Paragraph(Text("The accompanying normalized_output_probability theorem integrates the output intensity assuming unit reference norm. Thus the ideal probability is independent of the initial motional shape. It does not model detector noise, imperfect path closure, loss or finite-shot uncertainty.")),
                    Paragraph(Text("The experimental readout precedent is Fluehmann and Home (2020). Razian, Chang and Lau, arXiv:2604.06565v1, equations (4)-(5), supply a related 2026 ancilla-displacement proposal, not an experimental verification of golden control words."))),
                DescribeRole.Theorem))));

    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Wavefunctions() =>
        Seq(Mathbb, Grp(F.Id("C")), Caret, Grp(Reals()));
    private static Formula Phase(Formula t) => Call("exp", Seq(F.Id("i"), Cdot, Grp(t)));

    private static Formula CommonQuantifiers(Formula a, Formula b, Formula w, Formula f) =>
        Seq(Forall,Sp,a,Comma,b,Colon,Reals(),Comma,Esc,
            Forall,Sp,w,Colon,Call("List",F.Id("Bool")),Comma,Esc,
            Forall,Sp,f,Colon,Wavefunctions(),Comma,Esc);
    private static Formula Angle(Formula a, Formula b, Formula w) =>
        Seq(Num(2),Cdot,a,Cdot,b,Cdot,Call("magnusCenter",w));
    private static Formula Relative()
    {
        Formula a=F.Id("a"), b=F.Id("b"), w=F.Id("w"), f=F.Id("f");
        return Disp(Seq(CommonQuantifiers(a,b,w,f),Call("runWord",a,b,w,f),Eq,
            Phase(Angle(a,b,w)),Cdot,Call("runWord",a,b,Call("reverse",w),f)));
    }
    private static Formula Compensated()
    {
        Formula a=F.Id("a"), b=F.Id("b"), w=F.Id("w"), f=F.Id("f");
        return Disp(Seq(CommonQuantifiers(a,b,w,f),Call("endpointCompensatedWord",a,b,w,f),Eq,
            Phase(Seq(a,Cdot,b,Cdot,Call("magnusCenter",w))),Cdot,f));
    }
    private static Formula Output()
    {
        Formula t=F.Id("theta"), a=F.Id("a"), b=F.Id("b"), w=F.Id("w"), f=F.Id("f");
        return Disp(Seq(Forall,Sp,t,Colon,Reals(),Comma,Esc,
            CommonQuantifiers(a,b,w,f),Call("plusOutput",t,a,b,w,f),Eq,
            Call("plusAmplitude",t,Angle(a,b,w)),Cdot,
            Call("runWord",a,b,Call("reverse",w),f)));
    }
}
