using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy.Submodularity;

internal sealed class MutualInformationChainRuleDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For a finite joint law, the information in a pair of observations splits into the " +
            "information in the first observation and the remaining conditional information.",
        H("Mutual-Information Chain Rule"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("mutual-information-obeys-the-chain-rule"),
                DeclarationHandle.Create(
                    "D5/S3/Entropy/Submodularity/MutualInformationChainRule.mutual_information_chain_rule"),
                H("Mutual information obeys the chain rule"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("mutualInformation")), Open,
                    F.Id("p"), Close, Eq, Sp,
                    Operatorname, Grp(F.Id("mutualInformation")), Open,
                    F.Id("p"), Underscore, Grp(F.Id("XY")), Close, Plus, Sp,
                    Operatorname, Grp(F.Id("conditionalMutualInformation")), Open,
                    Operatorname, Grp(F.Id("yFirstLaw")), Open, F.Id("p"), Close, Close,
                    Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every pointwise nonnegative mass function on X times (Y times Z), " +
                        "the mutual information between X and the pair (Y,Z) is the mutual " +
                        "information between X and Y plus the conditional mutual information " +
                        "between X and Z given Y. Normalization is not needed for this identity.")),
                    Paragraph(Text(
                        "The proof expands both mutual-information terms and the conditional " +
                        "term into entropy defects. Reindexing the Y-pivoted law and commuting " +
                        "the projected coordinates makes every marginal and joint-entropy term " +
                        "cancel algebraically."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("adjoining-an-observation-does-not-decrease-information"),
                DeclarationHandle.Create(
                    "D5/S3/Entropy/Submodularity/MutualInformationChainRule.mutual_information_le_pair"),
                H("Adjoining an observation does not decrease information"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("mutualInformation")), Open,
                    F.Id("p"), Underscore, Grp(F.Id("XY")), Close, Leq, Sp,
                    Operatorname, Grp(F.Id("mutualInformation")), Open,
                    F.Id("p"), Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a normalized nonnegative law, adjoining Z to the observation Y " +
                        "cannot reduce the mutual information with X. The difference is exactly " +
                        "the conditional mutual information between X and Z given Y.")),
                    Paragraph(Text(
                        "The chain rule supplies the exact difference, while nonnegativity of " +
                        "conditional mutual information supplies its sign. No Markov assumption " +
                        "is required for this monotonicity statement."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("pair-information-equality-is-conditional-factorization"),
                DeclarationHandle.Create(
                    "D5/S3/Entropy/Submodularity/MutualInformationChainRule.mutual_information_pair_eq_iff_conditional_product"),
                H("Pair-information equality is conditional factorization"),
                StatementSource.FromAuthor(Disp(Seq(
                    Begin, Grp(F.Id("gathered")),
                    Operatorname, Grp(F.Id("mutualInformation")), Open,
                    F.Id("p"), Close, Eq, Sp,
                    Operatorname, Grp(F.Id("mutualInformation")), Open,
                    F.Id("p"), Underscore, Grp(F.Id("XY")), Close,
                    Sp, Iff, Sp, RowBreak,
                    Forall, Sp, F.Id("y"), Comma, Sp,
                    F.Id("p"), Underscore, Grp(F.Id("Y")), Open,
                    F.Id("y"), Close, Sp, Neq, Sp, D(0), Sp, Rightarrow, Sp,
                    F.Id("p"), Underscore,
                    Grp(F.Id("XZ"), Sp, Mid, Sp, F.Id("y")), Open,
                    F.Id("x"), Comma, Sp, F.Id("z"), Close, Eq, Sp,
                    F.Id("p"), Underscore,
                    Grp(F.Id("X"), Sp, Mid, Sp, F.Id("y")), Open,
                    F.Id("x"), Close, Times, Sp,
                    F.Id("p"), Underscore,
                    Grp(F.Id("Z"), Sp, Mid, Sp, F.Id("y")), Open,
                    F.Id("z"), Close, Dot,
                    End, Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The pair (Y,Z) carries exactly as much information about X as Y alone " +
                        "if and only if, on every Y-slice of nonzero mass, the conditional law " +
                        "of (X,Z) is the product of its X and Z marginals.")),
                    Paragraph(Text(
                        "By the chain rule, equality of the two mutual informations is equivalent " +
                        "to vanishing conditional mutual information given Y. The frozen equality " +
                        "case for conditional mutual information then turns vanishing into the " +
                        "displayed slicewise factorization."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("markov-data-processing-equality-is-reverse-conditional-factorization"),
                DeclarationHandle.Create(
                    "D5/S3/Entropy/Submodularity/MutualInformationChainRule.mutual_information_eq_of_markov_iff_conditional_product"),
                H("Markov data-processing equality is reverse conditional factorization"),
                StatementSource.FromAuthor(Disp(Seq(
                    Begin, Grp(F.Id("gathered")),
                    Operatorname, Grp(F.Id("Markov")), Open,
                    F.Id("X"), Comma, Sp, F.Id("Y"), Comma, Sp, F.Id("Z"), Close,
                    Sp, Rightarrow, Sp,
                    Open,
                    Operatorname, Grp(F.Id("mutualInformation")), Open,
                    F.Id("p"), Underscore, Grp(F.Id("XZ")), Close, Eq, Sp,
                    Operatorname, Grp(F.Id("mutualInformation")), Open,
                    F.Id("p"), Underscore, Grp(F.Id("XY")), Close,
                    Sp, Iff, Sp, RowBreak,
                    Forall, Sp, F.Id("z"), Comma, Sp,
                    F.Id("p"), Underscore, Grp(F.Id("Z")), Open,
                    F.Id("z"), Close, Sp, Neq, Sp, D(0), Sp, Rightarrow, Sp,
                    F.Id("p"), Underscore,
                    Grp(F.Id("XY"), Sp, Mid, Sp, F.Id("z")), Open,
                    F.Id("x"), Comma, Sp, F.Id("y"), Close, Eq, Sp,
                    F.Id("p"), Underscore,
                    Grp(F.Id("X"), Sp, Mid, Sp, F.Id("z")), Open,
                    F.Id("x"), Close, Times, Sp,
                    F.Id("p"), Underscore,
                    Grp(F.Id("Y"), Sp, Mid, Sp, F.Id("z")), Open,
                    F.Id("y"), Close, Close, Dot,
                    End, Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Under the X to Y to Z Markov hypothesis, equality in data processing " +
                        "holds exactly when X and Y are conditionally independent given every " +
                        "Z-value of nonzero mass. Thus lossless processing is characterized by " +
                        "a reverse conditional-product property.")),
                    Paragraph(Text(
                        "The Markov hypothesis makes the conditional mutual information given Y " +
                        "vanish. The established gap identity then equates the data-processing gap " +
                        "with conditional mutual information given Z, whose zero case is precisely " +
                        "the displayed factorization of the conditional (X,Y)-law."))),
                DescribeRole.Theorem))));
}
