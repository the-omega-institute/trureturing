using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.WeylChronology;

internal sealed class RamseyPhaseReadoutDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The Ramsey fringe is derived from a two-path amplitude and has explicit alias boundaries.",
        H("Ramsey Phase and Observation Kernels"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("ramsey-born-fringe"),
                DeclarationHandle.Create("D5/S3/Quantum/WeylChronology/RamseyPhaseReadout.plus_probability_formula"),
                H("The ideal plus-port probability"),
                StatementSource.FromAuthor(Fringe()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("The plus amplitude is (1+exp(i(phi-theta)))/2, including splitting and recombination. The probability is its squared complex modulus.")),
                    Paragraph(Text("Fluehmann and Home, Physical Review Letters 125, 043602 (2020), equation (3), experimentally use analyzer phases zero and pi/2 for real and imaginary characteristic-function data.")),
                    Paragraph(Text("The Lean file also proves the two-setting kernel agrees exactly with the wrapped complex phase, that the zero setting loses sign, and that two settings still have a full-turn alias. These equivalent readout presentations are not independent intrinsic capture gains."))),
                DescribeRole.Theorem))));

    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Wavefunctions() =>
        Seq(Mathbb, Grp(F.Id("C")), Caret, Grp(Reals()));
    private static Formula Phase(Formula t) => Call("exp", Seq(F.Id("i"), Cdot, Grp(t)));

    private static Formula Fringe()
    {
        Formula t=F.Id("theta"), p=F.Id("phi");
        return Disp(Seq(Forall,Sp,t,Comma,p,Colon,Reals(),Comma,Esc,
            Call("plusProbability",t,p),Eq,Frac,
            Grp(Num(1),Plus,Call("cos",Grp(p,Minus,t))),Grp(Num(2))));
    }
}
