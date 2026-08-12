using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy;

internal sealed class MutualInformationIndependenceDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite classical mutual information in nats vanishes exactly when the joint mass function is the product of its own marginals.",
        H("Vanishing Mutual Information Characterizes Independence"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("zero-mutual-information-characterizes-independence"),
                DeclarationHandle.Create("D5/S3/Entropy/MutualInformationIndependence.mutual_information_eq_zero_iff_product"),
                H("Zero mutual information characterizes independence"),
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
                                    F.Id("i"), Comma, F.Id("j"), Close, Close,
                                    Sp, Land, Sp,
                                    Sum, Underscore, Grp(F.Id("i"), Comma, F.Id("j")),
                                    F.Id("p"), Open, F.Id("i"), Comma, F.Id("j"), Close, Eq, D(1),
                                    Close, Sp, Rightarrow, RowBreak,
                                    Operatorname, Grp(F.Id("mutualInformation")), Open, F.Id("p"), Close,
                                    Eq, D(0), Sp, Leftrightarrow, Sp, RowBreak,
                                    F.Id("p"), Eq,
                                    Open,
                                    Open, F.Id("i"), Comma, F.Id("j"), Close, Mapsto, Sp,
                                    Operatorname, Grp(F.Id("marginal")), Open, F.Id("p"), Close,
                                    Open, F.Id("i"), Close,
                                    Operatorname, Grp(F.Id("marginal")), Open,
                                    Open, F.Id("j"), Comma, F.Id("i"), Close, Mapsto, Sp,
                                    F.Id("p"), Open, F.Id("i"), Comma, F.Id("j"), Close,
                                    Close, Open, F.Id("j"), Close,
                                    Close, Dot,
                                    End, Grp(F.Id("gathered"))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                                    Paragraph(Text(
                                        "The theorem states that mutual information vanishes exactly when the " +
                                        "joint mass function equals the product of its own two marginals, which " +
                                        "is the finite independence characterization. Its only hypotheses are " +
                                        "nonnegativity and normalization of the joint; no strict positivity is " +
                                        "assumed, and zero-mass cells are permitted. The units are nats because " +
                                        "mutualInformation uses the Real.log divergence. This module defines " +
                                        "nothing.")),
                                    Paragraph(Text(
                                        "This theorem closes the cluster: wave 16 supplied nonnegativity, wave " +
                                        "17b supplied vanishing on product laws, and the converse here makes " +
                                        "the independence characterization an if and only if. The proof applies " +
                                        "the frozen GibbsEquality.kl_divergence_eq_zero_iff theorem to the " +
                                        "product-of-marginals reference. Its three reference-law premises are " +
                                        "discharged here, not assumed: that product is shown nonnegative and " +
                                        "normalized, and the required absolute-continuity premise is proved by " +
                                        "showing that a zero reference cell forces the corresponding joint cell " +
                                        "to be zero. These are the same three discharges already performed by " +
                                        "the nonnegativity result.")),
                                    Paragraph(Text(
                                        "An audit of this program found that the nonnegativity theorem constrains " +
                                        "the reference not at all, since the bound holds for any admissible " +
                                        "reference, and that vanishing on products constrains it only on the " +
                                        "product submanifold. This converse constrains the reference wherever " +
                                        "mutual information vanishes.")),
                                    Paragraph(Text(
                                        "That is a stronger attestation, but it is not a full attestation of the " +
                                        "definition. A corrupted reference that agrees with the true reference " +
                                        "on every joint where the divergence vanishes would still escape this " +
                                        "characterization.")),
                                    Paragraph(Text(
                                        "Nothing is claimed about the rate at which mutual information grows " +
                                        "away from independence. No conditional independence statement is " +
                                        "proved, and nothing beyond two coordinates is asserted."))),
                DescribeRole.Theorem
            ))));
}
