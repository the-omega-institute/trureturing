using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy.NamingWindow;

internal sealed class FutureWordInformationChainDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A recursively nested future word obeys the finite Shannon chain rule: its entropy is " +
        "the first-readout entropy plus one full-prefix conditional entropy for every later readout.",
        H("Future-Word Information Chain"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("marginalization-preserves-nonnegativity"),
                DeclarationHandle.Create(
                    "D5/S3/Entropy/NamingWindow/FutureWordInformationChain.marginal_nonnegative"),
                H("Marginalization preserves nonnegativity"),
                StatementSource.FromAuthor(Disp(Seq(
                    Open, Forall, Sp, F.Id("x"), Comma, Sp,
                    D(0), Sp, Leq, Sp, Call("p", F.Id("x")), Close,
                    Sp, Longrightarrow, Sp,
                    Forall, Sp, F.Id("i"), Comma, Sp,
                    D(0), Sp, Leq, Sp,
                    Call("marginal", F.Id("p"), F.Id("i")), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a finite second coordinate, the marginal mass at i is the sum of " +
                        "the joint masses p(i,j) over all j. If every joint mass is nonnegative, " +
                        "each term in that finite sum is nonnegative, so the marginal is too."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("conditioning-preserves-nonnegativity"),
                DeclarationHandle.Create(
                    "D5/S3/Entropy/NamingWindow/FutureWordInformationChain.conditional_nonnegative"),
                H("Conditioning preserves nonnegativity"),
                StatementSource.FromAuthor(Disp(Seq(
                    Open, Forall, Sp, F.Id("x"), Comma, Sp,
                    D(0), Sp, Leq, Sp, Call("p", F.Id("x")), Close,
                    Sp, Longrightarrow, Sp,
                    Forall, Sp, F.Id("i"), Comma, Sp, F.Id("j"), Comma, Sp,
                    D(0), Sp, Leq, Sp,
                    Call("conditional", F.Id("p"), F.Id("i"), F.Id("j")), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A conditional mass divides the nonnegative joint mass p(i,j) by the " +
                        "corresponding marginal mass. The preceding marginal result makes the " +
                        "denominator nonnegative, so real division preserves nonnegativity."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("first-readout-marginal-remains-nonnegative"),
                DeclarationHandle.Create(
                    "D5/S3/Entropy/NamingWindow/FutureWordInformationChain.firstReadoutMarginal_nonnegative"),
                H("The first-readout marginal remains nonnegative"),
                StatementSource.FromAuthor(Disp(Seq(
                    Open, Forall, Sp, F.Id("w"), Comma, Sp,
                    D(0), Sp, Leq, Sp, Call("p", F.Id("w")), Close,
                    Sp, Longrightarrow, Sp,
                    Forall, Sp, F.Id("o"), Comma, Sp,
                    D(0), Sp, Leq, Sp,
                    Call("firstReadoutMarginal", F.Id("p"), F.Id("o")), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The first-readout law is obtained by repeatedly marginalizing the final " +
                        "coordinate of the recursively nested word. Induction on the word depth, " +
                        "using preservation of nonnegativity at each marginalization, shows that " +
                        "every first-readout mass remains nonnegative.")),
                    Paragraph(Text(
                        "At depth zero the future word is just the readout alphabet, so the " +
                        "first-readout marginal is the original mass function."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("earlier-conditional-entropy-is-inherited-from-the-prefix"),
                DeclarationHandle.Create(
                    "D5/S3/Entropy/NamingWindow/FutureWordInformationChain.prefixConditionalEntropy_succ_of_lt"),
                H("Earlier conditional entropy is inherited from the prefix"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("j"), Sp, Lt, Sp, F.Id("n"), Sp, Longrightarrow, Sp,
                    Call("prefixConditionalEntropy", F.Id("p"), F.Id("j")),
                    Sp, Eq, Sp,
                    Call("prefixConditionalEntropy",
                        Call("marginal", F.Id("p")), F.Id("j")), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a word extended by one final readout, every conditional-entropy term " +
                        "strictly before the new last index depends only on the preceding prefix. " +
                        "Marginalizing away the final readout therefore leaves that earlier term " +
                        "unchanged."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("last-prefix-conditional-entropy-is-the-outer-term"),
                DeclarationHandle.Create(
                    "D5/S3/Entropy/NamingWindow/FutureWordInformationChain.prefixConditionalEntropy_succ_last"),
                H("The last prefix-conditional entropy is the outer term"),
                StatementSource.FromAuthor(Disp(Seq(
                    Call("prefixConditionalEntropy", F.Id("p"), F.Id("n")),
                    Sp, Eq, Sp,
                    Call("conditionalEntropy", F.Id("p")), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A successor future word is its length-n prefix paired with one final " +
                        "readout. At the new last index, the prefix-conditional term is exactly " +
                        "the conditional entropy of that outer joint pair."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("extending-a-word-appends-one-conditional-entropy"),
                DeclarationHandle.Create(
                    "D5/S3/Entropy/NamingWindow/FutureWordInformationChain.prefixConditionalEntropy_sum_succ"),
                H("Extending a word appends one conditional entropy"),
                StatementSource.FromAuthor(Disp(Seq(
                    Sum, Underscore, Grp(F.Id("j"), Sp, Lt, Sp,
                        F.Id("n"), Sp, Plus, Sp, D(1)), Sp,
                    Call("prefixConditionalEntropy", F.Id("p"), F.Id("j")),
                    Sp, Eq, Sp,
                    Sum, Underscore, Grp(F.Id("j"), Sp, Lt, Sp, F.Id("n")), Sp,
                    Call("prefixConditionalEntropy",
                        Call("marginal", F.Id("p")), F.Id("j")),
                    Sp, Plus, Sp, Call("conditionalEntropy", F.Id("p")), Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Splitting the range through the new last index separates the final " +
                        "summand from all earlier summands. The earlier terms are inherited from " +
                        "the marginalized prefix law, while the final term is the outer " +
                        "conditional entropy.")),
                    Paragraph(Text(
                        "Thus increasing the word depth by one extends the accumulated prefix " +
                        "information by exactly one conditional-entropy contribution."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("future-word-information-chain"),
                DeclarationHandle.Create(
                    "D5/S3/Entropy/NamingWindow/FutureWordInformationChain.future_word_information_chain"),
                H("Future-word entropy obeys the full information chain"),
                StatementSource.FromAuthor(Disp(Seq(
                    Begin, Grp(F.Id("gathered")),
                    Forall, Sp, F.Id("O"), Colon, Sp,
                    Operatorname, Grp(F.Id("Type")), Comma, Sp,
                    OpenBracket, Call("Fintype", F.Id("O")), CloseBracket, Comma, RowBreak, Grp(),
                    F.Id("n"), Colon, Sp, Mathbb, Grp(F.Id("N")), Comma, Sp,
                    F.Id("p"), Colon, Sp,
                    Call("FutureWord", F.Id("O"), F.Id("n")), Sp, To, Sp,
                    Mathbb, Grp(F.Id("R")), Comma, RowBreak, Grp(),
                    Open, Forall, Sp, F.Id("w"), Colon, Sp,
                    Call("FutureWord", F.Id("O"), F.Id("n")), Comma, Sp,
                    D(0), Sp, Leq, Sp, Call("p", F.Id("w")), Close,
                    Sp, Longrightarrow, Sp,
                    F.Id("H"), Open, F.Id("p"), Close,
                    Sp, Eq, Sp,
                    F.Id("H"), Open,
                    Call("firstReadoutMarginal", F.Id("p")), Close,
                    Sp, Plus, Sp,
                    Sum, Underscore, Grp(F.Id("j"), Sp, Lt, Sp, F.Id("n")), Sp,
                    Call("prefixConditionalEntropy", F.Id("p"), F.Id("j")), Dot,
                    End, Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A depth-n future word contains n+1 readouts as recursively nested " +
                        "prefix-output pairs. For any nonnegative mass function on that finite " +
                        "word type, its Shannon entropy equals the entropy of the fully " +
                        "marginalized first readout plus one conditional entropy for each later " +
                        "readout given its complete preceding prefix.")),
                    Paragraph(Text(
                        "The induction step applies the two-variable entropy chain rule to the " +
                        "outermost prefix-output pair. The induction hypothesis expands the " +
                        "prefix entropy, and the successor-sum identity appends the final " +
                        "conditional term.")),
                    Paragraph(Text(
                        "No normalization, nonempty-alphabet, or positive-mass assumption is " +
                        "needed. The depth-zero case has no later readouts, so its conditional " +
                        "sum is empty and the identity reduces to the entropy of the original " +
                        "readout law."))),
                DescribeRole.Theorem))));
}
