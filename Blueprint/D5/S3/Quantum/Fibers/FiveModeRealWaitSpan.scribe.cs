using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Fibers;

internal sealed class FiveModeRealWaitSpanDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual Five-Mode Waits Span the Real Symmetric Effects", H("Actual Five-Mode Waits Span the Real Symmetric Effects"),
        Blocks(Describe.Lean(
            DescribeId.Create("five-mode-generator-skew"),
            DeclarationHandle.Create("D5/S3/Quantum/Fibers/FiveModeRealWaitSpan.generator_skew"),
            H("The fixed generator is skew symmetric"),
            StatementSource.FromAuthor(Disp(Seq(C("transpose", F.Id("generator")), Eq,
                Minus, F.Id("generator")))), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("This coordinate identity is consumed by the waiting-span theorem and by the complex unitary realization of the same menu."))), DescribeRole.Lemma),
            Describe.Lean(
            DescribeId.Create("fivemoderealwaitspan"),
            DeclarationHandle.Create("D5/S3/Quantum/Fibers/FiveModeRealWaitSpan.five_mode_nonnegative_wait_span"),
            H("Actual Five-Mode Waits Span the Real Symmetric Effects"), StatementSource.FromAuthor(Disp(Seq(F.Id("waitSpan"), Eq, C("Sym", D(5), Seq(Mathbb, Grp(F.Id("R"))))))), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("The fixed real skew generator has rows (0,1,1,1,0), (-1,0,0,0,-1), (-1,0,0,0,0), (-1,0,0,0,-1), and (0,1,0,1,0). Its coordinate order is N, 2, 3, 5, 25. Only nonnegative real waiting times followed by a complete mode read enter the observation span.")),
                Paragraph(Text("The fifteen selected commutator jets have orders and modes (0,0) through (0,4), (1,0) through (1,3), (2,0) through (2,2), (3,0), (3,1), and (4,0). The fulfilled numerical premise symmetric_decomposition expresses every real symmetric matrix as a linear combination of these same-generator jets with exact coefficients. The theorem reduces the continuous span to this finite premise; waits_separate_real and actual_effect_span_eq in FiveModeRealResponse consume the resulting full nonnegative-time span on the proof path to the public five_mode_real_response_fiber theorem.")),
                Paragraph(Text("The analytic supplier NonnegativeConjugationSpan puts each jet in the closed span of actual nonnegative-time effects. The reverse inclusion uses skew symmetry and the transpose identity for matrix exponentials. Consequently the commutator spanning calculation determines the actual waiting-effect span; the menu only requires waiting and reading."))),
            DescribeRole.Theorem))));

    private static Formula C(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var i = 0; i < arguments.Length; i++)
        {
            if (i > 0) items.Add(Comma);
            items.Add(arguments[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
}
