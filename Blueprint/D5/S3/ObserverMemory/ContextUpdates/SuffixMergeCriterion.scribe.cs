using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.ContextUpdates;

internal sealed class SuffixMergeCriterionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A context update merges exactly when its retained suffix and next token agree.",
        H("Suffix Merge Criterion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("context-update-equality-criterion"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/ContextUpdates/SuffixMergeCriterion."
                    + "context_update_eq_iff"),
                H("Context updates agree exactly by coordinates"),
                StatementSource.FromAuthor(ContextUpdateFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A finite context is split into the oldest token and the suffix that "
                            + "survives the update. The update discards the oldest token, keeps "
                            + "the suffix, and appends the next token generated from both inputs.")),
                    Paragraph(Text(
                        "Two updated contexts are equal exactly when the retained suffixes are "
                            + "equal and the generated next tokens are equal. This is the two "
                            + "coordinate equality criterion for the successor pair.")),
                    Paragraph(Text(
                        "This closes qdo-v1 theorem/21.11, atom "
                            + "qdo-residual-1c0abd2fab1f49a70e36c7cd009f5e478bae52045c8aa330123e28c2c5f333ef. "
                            + "Pinned Mathlib provides the exact theorem Prod.mk_inj, which the "
                            + "Lean proof imports and applies directly. Repository search found "
                            + "no duplicate criterion; forward_merge_persistence already covers "
                            + "the source text's later-futures consequence after equality holds."))),
                DescribeRole.Theorem))));

    private static Formula ContextUpdateFormula()
    {
        Formula tokenType = F.Id("Token");
        Formula suffixType = F.Id("Suffix");
        Formula nextToken = F.Id("nextToken");
        Formula oldest = F.Id("a");
        Formula oldestPrime = Seq(F.Id("a"), Apos);
        Formula suffix = F.Id("s");
        Formula suffixPrime = Seq(F.Id("s"), Apos);
        Formula generatorType = new Formula.TypeArrow(
            tokenType,
            new Formula.TypeArrow(suffixType, tokenType));
        Formula leftContext = Seq(Open, oldest, Comma, Sp, suffix, Close);
        Formula rightContext = Seq(Open, oldestPrime, Comma, Sp, suffixPrime, Close);

        return Disp(Seq(
            Forall, Sp, tokenType, Comma, Sp, suffixType,
            Colon, Sp, Operatorname, Grp(F.Id("Type")), Comma, Esc,
            Forall, Sp, nextToken, Colon, Sp, generatorType, Comma, Esc,
            Forall, Sp, oldest, Comma, Sp, oldestPrime,
            Colon, Sp, tokenType, Comma, Sp,
            suffix, Comma, Sp, suffixPrime, Colon, Sp, suffixType, Comma, Esc,
            Call("contextUpdate", nextToken, leftContext), Sp, Eq, Sp,
            Call("contextUpdate", nextToken, rightContext), Sp, Iff, Sp,
            Open, suffix, Sp, Eq, Sp, suffixPrime, Sp, Land, Sp,
            Call("nextToken", oldest, suffix), Sp, Eq, Sp,
            Call("nextToken", oldestPrime, suffixPrime), Close, Dot));
    }
}
