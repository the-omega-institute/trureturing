using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.PrimeForms.Crossing;

internal sealed class ResonanceFactorsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The two exceptional resonance factors vanish identically exactly at alphabet value three.",
        H("The Resonance Factors Select Alphabet Value Three"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("resonance-factors-identically-zero-iff-three"),
                DeclarationHandle.Create(
                    "D5/S3/PrimeForms/Crossing/ResonanceFactors.resonance_factors_identically_zero_iff"),
                H("The two resonance factors are identically zero exactly when m equals three"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("m"), InMacro, Mathbb, Grp(F.Id("Z")), Comma, Esc,
                    Open, Forall, Sp, F.Id("p"), Comma, F.Id("r"), InMacro, Mathbb, Grp(F.Id("Z")),
                    Comma, Esc,
                    Open, D(2), Cdot, Sp, F.Id("r"), Cdot, Sp,
                    Open, F.Id("m"), Minus, D(3), Close, Cdot, Sp,
                    Open, D(2), F.Id("p"), Plus, F.Id("r"), Close, Eq, D(0), Sp, Land, Sp,
                    Minus, D(2), Cdot, Sp, F.Id("r"), Cdot, Sp,
                    Open, F.Id("m"), Minus, D(3), Close, Cdot, Sp,
                    Open, F.Id("p"), Plus, F.Id("r"), Close, Eq, D(0), Close,
                    Close, Sp, Iff, Sp, F.Id("m"), Eq, D(3)))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Residual E.67 isolates two exceptional deficit factors, "
                        + "2r(m-3)(2p+r) and -2r(m-3)(p+r). Their common linear factor m-3 "
                        + "shows immediately that m=3 makes both factors vanish for every integer p and r. "
                        + "Conversely, if both factors vanish identically, evaluating the first one at "
                        + "p=0 and r=1 gives 2(m-3)=0 in the integers, hence m=3.")),
                    Paragraph(Text(
                        "The Lean proof uses mathlib's integer zero-product characterization to cancel the "
                        + "nonzero factor 2 after this single evaluation. Local D5 and pinned-mathlib searches "
                        + "found no theorem for these specific factors; Loogle found only the generic "
                        + "Int.mul_eq_zero lemma, which the proof reuses.")),
                    Paragraph(Text(
                        "This theorem closes only the explicit alphabet-resonance clause of E.67. It does not "
                        + "formalize the remaining sixteen deficit branches, the block-length resonance "
                        + "ps-qr=(-1)^l p_(k-l-1), or the surrounding continued-fraction recurrence audit."))),
                DescribeRole.Theorem
            )),
        []));
}
