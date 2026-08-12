using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy;

internal sealed class ConditioningReducesEntropyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For a finite normalized joint, conditioning on the first coordinate cannot increase the entropy of the second, in nats.",
        H("Conditioning Reduces Entropy"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("conditioning-cannot-increase-entropy"),
                DeclarationHandle.Create("D5/S3/Entropy/ConditioningReducesEntropy.conditional_entropy_le_marginal"),
                H("Conditioning cannot increase entropy"),
                StatementSource.FromAuthor(Disp(Seq(
                                    Begin, Grp(F.Id("gathered")),
                                    Forall, Sp, Iota, Comma, Sp, Kappa, Esc,
                                    OpenBracket,
                                    Operatorname, Grp(F.Id("Fintype")), Open, Iota, Close,
                                    CloseBracket, Sp,
                                    OpenBracket,
                                    Operatorname, Grp(F.Id("Fintype")), Open, Kappa, Close,
                                    CloseBracket, Comma, RowBreak,
                                    Forall, Sp, F.Id("p"), Colon, Sp,
                                    Iota, Times, Kappa, To, Sp, Mathbb, Grp(F.Id("R")), Comma, RowBreak,
                                    Open,
                                    Open,
                                    Forall, Sp, F.Id("i"), Comma, Sp, F.Id("j"), Comma, Sp,
                                    D(0), Le, Sp, F.Id("p"), Open,
                                    F.Id("i"), Comma, F.Id("j"), Close,
                                    Close, Sp, Land, Sp,
                                    Sum, Underscore, Grp(F.Id("i"), Comma, F.Id("j")),
                                    F.Id("p"), Open, F.Id("i"), Comma, F.Id("j"), Close, Eq, D(1),
                                    Close, Sp, Rightarrow, RowBreak,
                                    Operatorname, Grp(F.Id("conditionalEntropy")), Open, F.Id("p"), Close, Le,
                                    Operatorname, Grp(F.Id("shannonEntropy")), Open,
                                    Operatorname, Grp(F.Id("marginal")), Open,
                                    Open, F.Id("j"), Comma, F.Id("i"), Close, Mapsto, Sp,
                                    F.Id("p"), Open, F.Id("i"), Comma, F.Id("j"), Close,
                                    Close, Close, Dot,
                                    End, Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                                    Paragraph(Text(
                                        "Conditional entropy is the marginal-weighted average entropy of the " +
                                        "conditional slices. This theorem says that average does not exceed " +
                                        "the entropy of the second marginal: conditioning on the first " +
                                        "coordinate cannot increase the entropy of the second. The bound is on " +
                                        "the average over slices, not on any individual slice; an individual " +
                                        "conditional slice may well have higher entropy than the marginal.")),
                                    Paragraph(Text(
                                        "This theorem is a composition of three frozen ingredients: the entropy " +
                                        "chain rule, the mutual-information decomposition, and the " +
                                        "nonnegativity of mutual information. It rewrites mutual-information " +
                                        "nonnegativity with the two identities and closes the resulting linear " +
                                        "inequality; nothing is re-proved and nothing is defined here.")),
                                    Paragraph(Text(
                                        "The chain rule and the mutual-information decomposition need only " +
                                        "nonnegativity. Normalization is forced here by exactly one ingredient: " +
                                        "the nonnegativity of mutual information. The units are nats because " +
                                        "shannonEntropy uses Real.log.")),
                                    Paragraph(Text(
                                        "No equality condition is claimed: the case in which conditioning " +
                                        "leaves entropy unchanged, namely independence, is not characterized " +
                                        "here. The theorem says nothing about conditional mutual information " +
                                        "and nothing beyond two coordinates."))),
                DescribeRole.Theorem
            ))));
}
