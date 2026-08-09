using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy;

internal sealed class ConditionalEntropyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/Entropy/ConditionalEntropy",
            "Finite conditional entropy in nats is the marginal-weighted entropy of conditional slices and satisfies the entropy chain rule."),
        H("Conditional Entropy and Its Chain Rule"),
        Blocks(
            DocumentBlock.Describe.Definition(
                DescribeId.Create("conditional-entropy-is-marginal-weighted-slice-entropy"),
                H("Conditional entropy is marginal-weighted slice entropy"),
                LeanDefinition(
                    "D5/S3/Entropy/ConditionalEntropy.conditionalEntropy"),
                DescribeProvenance.RepoDerived(),
                Blocks(
                    Paragraph(Text(
                        "The definitions of marginal and conditional come from " +
                        "D5/S3/Divergence/ChainRule; conditionalEntropy is the only new " +
                        "definition here. It is introduced because the chain rule and queued " +
                        "conditional results all consume it, not speculatively. The units are " +
                        "nats because shannonEntropy uses Real.log."))),
                Disp(Seq(
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
                    Operatorname, Grp(F.Id("conditionalEntropy")), Open, F.Id("p"), Close,
                    Colon, Eq,
                    Sum, Underscore, Grp(F.Id("i")),
                    Operatorname, Grp(F.Id("marginal")), Open, F.Id("p"), Close,
                    Open, F.Id("i"), Close,
                    Operatorname, Grp(F.Id("shannonEntropy")), Open,
                    Operatorname, Grp(F.Id("conditional")), Open,
                    F.Id("p"), Comma, F.Id("i"), Close,
                    Close, Dot,
                    End, Grp(F.Id("gathered"))))
            ),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("joint-entropy-obeys-the-chain-rule"),
                H("Joint entropy obeys the chain rule"),
                LeanTheorem(
                    "D5/S3/Entropy/ConditionalEntropy.entropy_chain_rule"),
                Disp(Seq(
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
                    Forall, Sp, F.Id("i"), Comma, Sp, F.Id("j"), Comma, Sp,
                    D(0), Le, Sp, F.Id("p"), Open,
                    F.Id("i"), Comma, F.Id("j"), Close,
                    Close, Sp, Rightarrow, RowBreak,
                    Operatorname, Grp(F.Id("shannonEntropy")), Open, F.Id("p"), Close, Eq,
                    Operatorname, Grp(F.Id("shannonEntropy")), Open,
                    Operatorname, Grp(F.Id("marginal")), Open, F.Id("p"), Close,
                    Close, Plus,
                    Operatorname, Grp(F.Id("conditionalEntropy")), Open, F.Id("p"), Close,
                    Dot,
                    End, Grp(F.Id("gathered")))),
                DescribeProvenance.RepoDerived(),
                Blocks(
                    Paragraph(Text(
                        "The joint entropy splits into the marginal entropy plus the " +
                        "marginal-weighted average of the conditional slice entropies. This is " +
                        "the entropy-side counterpart of the frozen divergence chain rule.")),
                    Paragraph(Text(
                        "The hypotheses are deliberately minimal: nonnegativity alone. " +
                        "Normalization is not required, even though a reader may expect a " +
                        "probability distribution.")),
                    Paragraph(Text(
                        "When a marginal is zero, the conditional slice is a quotient by zero. " +
                        "That case is handled rather than excluded: nonnegativity forces every " +
                        "cell of such a slice to vanish, so the slice contributes nothing and " +
                        "the outer weight annihilates its term. No positivity is assumed " +
                        "anywhere.")),
                    Paragraph(Text(
                        "On the nonnegative domain, the chain rule pins conditionalEntropy as " +
                        "the difference between two independently attested entropies. A wrong " +
                        "weight, a wrong slice association, or a slipped index that changes the " +
                        "aggregate would break the equality. This pin constrains the aggregate " +
                        "only: a corruption that leaves the aggregate unchanged on every " +
                        "nonnegative joint would not be caught.")),
                    Paragraph(Text(
                        "This module proves no conditioning bound: the statement that " +
                        "conditioning cannot increase entropy is not proved here. It proves no " +
                        "conditional mutual information, no equality condition, and nothing " +
                        "beyond two coordinates.")))))));

    private static LeanDeclarationRef LeanDefinition(string value) =>
        LeanDeclarationRef.Create(
            value,
            expectedKind: LeanDeclarationKind.Definition,
            requireNoSorry: true);
}
