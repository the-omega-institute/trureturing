using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy.Submodularity;

internal sealed class ConditionalMutualInformationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite conditional mutual information is the defect in conditional-entropy subadditivity and equals the strong-subadditivity entropy defect.",
        H("Conditional Mutual Information"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("conditional-mutual-information-is-the-conditional-entropy-defect"),
                DeclarationHandle.Create(
                    "D5/S3/Entropy/Submodularity/ConditionalMutualInformation.conditionalMutualInformation"),
                H("Conditional mutual information is the conditional-entropy defect"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("conditionalMutualInformation")),
                    Open, F.Id("p"), Close, Colon, Eq, Sp,
                    Operatorname, Grp(F.Id("conditionalEntropy")), Open,
                    F.Id("p"), Underscore, Grp(F.Id("XY")), Close, Plus, Sp,
                    Operatorname, Grp(F.Id("conditionalEntropy")), Open,
                    F.Id("p"), Underscore, Grp(F.Id("XZ")), Close, Minus, Sp,
                    Operatorname, Grp(F.Id("conditionalEntropy")), Open,
                    F.Id("p"), Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a mass function on the right-nested product X times (Y times Z), " +
                        "conditional mutual information is the amount by which the sum of the " +
                        "XY and XZ conditional entropies exceeds the conditional entropy of " +
                        "the full law. The projections are the public interfaces established " +
                        "by strong subadditivity."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("conditional-mutual-information-is-nonnegative"),
                DeclarationHandle.Create(
                    "D5/S3/Entropy/Submodularity/ConditionalMutualInformation.conditional_mutual_information_nonneg"),
                H("Conditional mutual information is nonnegative"),
                StatementSource.FromAuthor(Disp(Seq(
                    D(0), Leq, Sp,
                    Operatorname, Grp(F.Id("conditionalMutualInformation")),
                    Open, F.Id("p"), Close, Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every normalized nonnegative finite law, conditional-entropy " +
                        "subadditivity says that the defining defect is nonnegative. The proof " +
                        "is a direct restatement of the frozen conditionalEntropy_pair_le_add " +
                        "interface and does not repeat its slicewise argument."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("conditional-mutual-information-is-the-entropy-defect"),
                DeclarationHandle.Create(
                    "D5/S3/Entropy/Submodularity/ConditionalMutualInformation.conditional_mutual_information_eq_entropy_defect"),
                H("Conditional mutual information is the entropy defect"),
                StatementSource.FromAuthor(Disp(Seq(
                    Operatorname, Grp(F.Id("conditionalMutualInformation")),
                    Open, F.Id("p"), Close, Eq, Sp,
                    F.Id("H"), Open, F.Id("p"), Underscore, Grp(F.Id("XY")), Close,
                    Plus, Sp,
                    F.Id("H"), Open, F.Id("p"), Underscore, Grp(F.Id("XZ")), Close,
                    Minus, Sp, F.Id("H"), Open, F.Id("p"), Close,
                    Minus, Sp,
                    F.Id("H"), Open, F.Id("p"), Underscore, Grp(F.Id("X")), Close,
                    Dot))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Applying the entropy chain rule to the full law and both projections " +
                        "turns the conditional-entropy definition into the classical strong-" +
                        "subadditivity defect. Both projections have the same X marginal as " +
                        "the original law, so their marginal terms reduce to one surviving " +
                        "subtraction of H(X).")),
                    Paragraph(Text(
                        "This identity needs only pointwise nonnegativity; normalization is not " +
                        "used by the entropy chain rule. It adds neither an equality " +
                        "characterization nor a Markov data-processing statement."))),
                DescribeRole.Theorem))));
}
