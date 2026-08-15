using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy.Forgetting;

internal sealed class CompletionEntropyMinimalityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A deterministic completion that factors through another has no more conditional "
            + "entropy under the same observation.",
        H("Conditional Entropy under Completion Factorization"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("factorized-completion-has-minimal-conditional-entropy"),
                DeclarationHandle.Create(
                    "D5/S3/Entropy/Forgetting/CompletionEntropyMinimality."
                    + "completion_conditional_entropy_le_of_factorization"),
                H("A factorized completion has no more conditional entropy"),
                StatementSource.FromAuthor(CompletionEntropyFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let p be a normalized nonnegative mass function on a finite initial-state "
                            + "carrier Y. The maps observation : Y -> O and otherCompletion : Y -> W "
                            + "give the observed and refined records. Suppose factor : W -> Z is "
                            + "surjective and completion = factor composed with otherCompletion. "
                            + "Then the conditional entropy of completion(Y) given observation(Y) "
                            + "is at most the conditional entropy of otherCompletion(Y) given the "
                            + "same observation.")),
                    Paragraph(Text(
                        "This factorization is the formal universal-property premise behind the "
                            + "source's minimal exact completion: every competing exact deterministic "
                            + "completion supplies a refinement from which the minimal completion is "
                            + "recovered deterministically. Surjectivity records that both finite "
                            + "completion carriers contain only reachable record values.")),
                    Paragraph(Text(
                        "The proof pushes the refined joint law through the first-coordinate-preserving "
                            + "map (o, w) -> (o, factor(w)). The imported deterministic-forgetting "
                            + "theorem lowers its joint entropy, while an explicit finite-sum identity "
                            + "shows that the observation marginal is unchanged. Applying the entropy "
                            + "chain rule to both joint laws cancels that common marginal and gives the "
                            + "claimed conditional-entropy inequality. Library and repository searches "
                            + "found no exact theorem to bind."))),
                DescribeRole.Theorem))));

    private static Formula CompletionEntropyFormula()
    {
        Formula p = F.Id("p");
        Formula observation = F.Id("observation");
        Formula other = F.Id("otherCompletion");
        Formula completion = F.Id("completion");
        Formula factor = F.Id("factor");
        Formula y = F.Id("Y");
        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Operatorname, Grp(F.Id("ProbabilityLaw")), Open, p, Close, Comma, RowBreak,
            Operatorname, Grp(F.Id("Surjective")), Open, factor, Close, Comma, RowBreak,
            completion, Sp, Eq, Sp, factor, Sp, Circ, Sp, other, Sp, Rightarrow, RowBreak,
            F.Id("H"), Underscore, Grp(p), Open,
            completion, Open, y, Close, Sp, Mid, Sp,
            observation, Open, y, Close, Close, Sp, Leq, Sp,
            F.Id("H"), Underscore, Grp(p), Open,
            other, Open, y, Close, Sp, Mid, Sp,
            observation, Open, y, Close, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
