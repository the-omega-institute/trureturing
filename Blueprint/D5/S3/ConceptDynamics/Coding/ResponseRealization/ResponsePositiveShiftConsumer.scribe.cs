using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding.ResponseRealization;

internal sealed class ResponsePositiveShiftConsumerDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Coding/ResponseRealization/ResponsePositiveShiftConsumer.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The constructed response-output positive word has its exact letter count and literal negative time correction on all histories.",
        H("The actual output word and its literal time correction"),
        Blocks(
            Paragraph(Text("Assume the finite discrete graph data, Essential G, TablePair G G a b c d and its actual SameTableConjugacy S as in ResponseTwoSidedConsumer. Set k=(a+c)+(b+d+1). word is terminalWord of the actual response terminal: forward source lifts, the terminal finite vertex-and-edge relabeling, and positive reverse target lifts. Its endpoints are exactly response G hG pair S and original G hG. No inverse-homeomorphism leaf is added to the positive word syntax.")),
            Paragraph(Text("terminal_letters gives 2*k letters. For the literal history equality, terminal_literal first gives minus incoming-left count minus outgoing-right count. response_profile gives those counts as a+c and b+d+1, including the completed first outgoing step. Thus on every response history z, numberedOutput(z)=time G (-k) (word.eval z). Composing with numbered_response_reduction yields original_centred on every original history.")),
            Paragraph(Text("The uncentred consequence is obtained locally: the future-block coordinates commute with every integer translation; substitute centred_eq_uncentred_negative into original_centred, apply Word.eval_time, and add the two integer displacements. The resulting displacement is literally -a-k, where k=(a+c)+(b+d+1).")),
            Paragraph(Text("OriginalPositiveWordAssembly uses word, word_letters and original_centred together with FullOutResponseIdentification.numberedLift_eq_tower_negative. It constructs a word on the original graph of length (a+b+1)+2*k and the same literal correction -a-k. This is the complete original-history factorization used in the arithmetic application.")),
            Describe.Remark(DescribeId.Create("response-realization-response-positive-shift-consumer-word"), DeclarationHandle.Create(Prefix + "word"), H("word"), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("The typed output word is terminalWord of the existing response terminal. It is consumed by output_literal and the original positive-word assembly, with exact endpoints retained.")))),
            Describe.Lean(DescribeId.Create("response-realization-response-positive-shift-consumer-word-letters"), DeclarationHandle.Create(Prefix + "word_letters"), H("word_letters"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Applies terminal_letters to that word, obtaining exactly 2*((a+c)+(b+d+1)). The original assembly uses this count together with the input tower length."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("response-realization-response-positive-shift-consumer-output-literal"), DeclarationHandle.Create(Prefix + "output_literal"), H("output_literal"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Uses the actual response_profile to rewrite terminal_literal to the correction -k on all response histories. original_centred consumes it; paired lengths alone are not its justification."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("response-realization-response-positive-shift-consumer-original-centred"), DeclarationHandle.Create(Prefix + "original_centred"), H("original_centred"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text("Composes output_literal with the existing numbered response equality on every original history. OriginalPositiveWordAssembly.positive_word explicitly uses it as the output half of the original-domain construction."))), DescribeRole.Theorem))));
}
