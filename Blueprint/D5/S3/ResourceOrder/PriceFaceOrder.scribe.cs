using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ResourceOrder;

internal sealed class PriceFaceOrderDocument : IScribeDocumentDefinition
{
    private const string LeanPrefix = "D5/S3/ResourceOrder/PriceFaceOrder.";

    private static Formula CostProfileType() => F.Seq(
        F.Operatorname, F.Grp(F.Id("CostProfile")), F.Open, F.Id("Cost"), F.Close);

    private static Formula PhysicalCostsType() => F.Seq(
        F.Operatorname, F.Grp(F.Id("PhysicalCosts")), F.Open, F.Id("Cost"), F.Close);

    private static Formula TaxReceiptType() => F.Seq(
        F.Operatorname, F.Grp(F.Id("TaxReceipt")), F.Open,
        F.Id("AlgorithmCost"), F.Comma, F.Sp, F.Id("RateCost"), F.Comma, F.Sp,
        F.Id("PhysicalCost"), F.Comma, F.Sp, F.Id("HeatCost"), F.Close);

    private static Formula Display(Formula formula) => F.Disp(formula);

    private static Formula TradeReceipt(bool witness) => F.Seq(
        F.Operatorname, F.Grp(F.Id("tradeReceipt")), F.Open, F.Id(witness ? "true" : "false"), F.Close);

    private static Formula PriceFace() => F.Seq(
        F.Operatorname, F.Grp(F.Id("priceFace")), F.Open,
        F.Id("validWitness"), F.Comma, F.Sp, F.Id("receipt"), F.Comma, F.Sp,
        F.Id("left"), F.Comma, F.Sp, F.Id("right"), F.Close);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The price face carries a genuine two-direction preorder of tax receipts.",
        H("Order and Incomparability in the Price Face"),
        Blocks(
            Paragraph(Text(
                "The frozen PriceFace module introduced the cost-profile, physical-cost, and "
                + "tax-receipt layers together with the priceFace set, but it proved nothing. "
                + "This module supplies its first theorems and closes the open left by the frozen "
                + "doc comment, which says verbatim, \"This definition does not assert that the face "
                + "has more than one independent cost direction.\" The concrete face has two "
                + "independent directions.")),
            Paragraph(Text(
                "The new preorder instances reuse the frozen module's LE relation. They add only "
                + "reflexivity and transitivity, so the symbol <= has the same meaning in both "
                + "modules; the structure is extended rather than shadowed. At the profile layer, "
                + "eventual domination compares all sufficiently large scales.")),
            Paragraph(Text(
                "The order is proved to be a preorder rather than merely described as one. The "
                + "constant-zero profile and the profile that spikes to one at scale zero dominate "
                + "each other eventually, although they are unequal. The concrete trade receipts "
                + "then exchange forward time against forward space, yielding two distinct "
                + "incomparable minimal elements of the price face.")),
            Paragraph(Text(
                "The reachability lemmas make the set-theoretic boundary explicit: membership in "
                + "priceFace supplies a valid witness, and the face is empty when no valid witness "
                + "exists. Every authored display below is legal because the current projector has "
                + "no pinned projectable statement fixture for these declarations; construction "
                + "records a ProjectionGap for each one.")),
            Describe.Lean(
                DescribeId.Create("cost-profile-eventual-domination-is-transitive"),
                DeclarationHandle.Create(LeanPrefix + "costProfile_preorder_trans"),
                H("Eventual domination of cost profiles is transitive"),
                StatementSource.FromAuthor(Display(F.Seq(
                    F.Forall, F.Sp, F.Id("Cost"), F.Sp, F.InMacro, F.Sp,
                    F.Operatorname, F.Grp(F.Id("Type")), F.Comma, F.Sp,
                    F.Forall, F.Sp, F.Id("left"), F.Comma, F.Sp, F.Id("middle"), F.Comma,
                    F.Sp, F.Id("right"), F.Sp, F.InMacro, F.Sp, CostProfileType(), F.Comma,
                    F.Sp, F.Id("left"), F.Leq, F.Sp, F.Id("middle"), F.Sp,
                    F.Rightarrow, F.Sp, F.Id("middle"), F.Leq, F.Sp, F.Id("right"),
                    F.Sp, F.Rightarrow, F.Sp, F.Id("left"), F.Leq, F.Sp, F.Id("right")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every preordered cost type, eventual domination composes: a profile no "
                    + "greater than a second profile, followed by the second no greater than a third, "
                    + "makes the first no greater than the third."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("physical-cost-order-is-transitive"),
                DeclarationHandle.Create(LeanPrefix + "physicalCosts_preorder_trans"),
                H("The physical-cost order is transitive"),
                StatementSource.FromAuthor(Display(F.Seq(
                    F.Forall, F.Sp, F.Id("Cost"), F.Sp, F.InMacro, F.Sp,
                    F.Operatorname, F.Grp(F.Id("Type")), F.Comma, F.Sp,
                    F.Forall, F.Sp, F.Id("left"), F.Comma, F.Sp, F.Id("middle"), F.Comma,
                    F.Sp, F.Id("right"), F.Sp, F.InMacro, F.Sp, PhysicalCostsType(), F.Comma,
                    F.Sp, F.Id("left"), F.Leq, F.Sp, F.Id("middle"), F.Sp,
                    F.Rightarrow, F.Sp, F.Id("middle"), F.Leq, F.Sp, F.Id("right"),
                    F.Sp, F.Rightarrow, F.Sp, F.Id("left"), F.Leq, F.Sp, F.Id("right")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The four componentwise comparisons of forward time, forward space, reverse "
                    + "time, and reverse space compose independently. Their conjunction is exactly "
                    + "the transitivity law for PhysicalCosts."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("tax-receipt-componentwise-order-is-transitive"),
                DeclarationHandle.Create(LeanPrefix + "taxReceipt_preorder_trans"),
                H("The componentwise tax-receipt order is transitive"),
                StatementSource.FromAuthor(Display(F.Seq(
                    F.Forall, F.Sp, F.Id("AlgorithmCost"), F.Comma, F.Sp,
                    F.Id("RateCost"), F.Comma, F.Sp, F.Id("PhysicalCost"), F.Comma, F.Sp,
                    F.Id("HeatCost"), F.Sp, F.InMacro, F.Sp,
                    F.Operatorname, F.Grp(F.Id("Type")), F.Comma, F.Sp,
                    F.Forall, F.Sp, F.Id("left"), F.Comma, F.Sp, F.Id("middle"), F.Comma,
                    F.Sp, F.Id("right"), F.Sp, F.InMacro, F.Sp, TaxReceiptType(), F.Sp,
                    F.Rightarrow, F.Sp, F.Id("left"), F.Sp, F.Leq, F.Sp, F.Id("middle"),
                    F.Sp, F.Rightarrow, F.Sp, F.Id("middle"), F.Sp, F.Leq, F.Sp,
                    F.Id("right"), F.Sp, F.Rightarrow, F.Sp, F.Id("left"), F.Sp,
                    F.Leq, F.Sp, F.Id("right")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At the receipt layer, the algorithm costs, rate, four physical profiles, and "
                    + "heat cost are ordered componentwise. Transitivity is obtained by composing "
                    + "each field and therefore introduces no new relation beyond the frozen LE."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("forward-time-and-space-trades-are-incomparable-in-one-direction"),
                DeclarationHandle.Create(LeanPrefix + "trade_true_not_le_false"),
                H("The forward trade receipt is not below the reverse trade receipt"),
                StatementSource.FromAuthor(Display(F.Seq(
                    F.Neg, F.Open, TradeReceipt(true), F.Sp, F.Leq, F.Sp,
                    TradeReceipt(false), F.Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The receipt with the forward-time and forward-space assignment exchanged in "
                    + "the true branch cannot be below the false branch: its forward-space profile "
                    + "would require the constantly-one function to be eventually no greater than "
                    + "the constantly-zero function."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("reverse-time-and-space-trades-are-incomparable-in-the-other-direction"),
                DeclarationHandle.Create(LeanPrefix + "trade_false_not_le_true"),
                H("The reverse trade receipt is not below the forward trade receipt"),
                StatementSource.FromAuthor(Display(F.Seq(
                    F.Neg, F.Open, TradeReceipt(false), F.Sp, F.Leq, F.Sp,
                    TradeReceipt(true), F.Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The converse comparison fails for the dual reason: the reverse branch would "
                    + "force its constantly-one forward-time profile below the constantly-zero "
                    + "profile. Thus neither trade can be purchased at a weakly lower receipt."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("eventual-cost-profile-order-is-not-antisymmetric"),
                DeclarationHandle.Create(LeanPrefix + "costProfile_eventual_order_not_antisymmetric"),
                H("Eventual cost-profile domination is not antisymmetric"),
                StatementSource.FromAuthor(Display(F.Seq(
                    F.Id("zeroProfile"), F.Sp, F.Leq, F.Sp, F.Id("spikeProfile"), F.Sp,
                    F.Land, F.Sp, F.Id("spikeProfile"), F.Sp, F.Leq, F.Sp, F.Id("zeroProfile"),
                    F.Sp, F.Land, F.Sp, F.Id("zeroProfile"), F.Sp, F.Neq, F.Sp,
                    F.Id("spikeProfile")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The constantly-zero profile and the profile that equals one only at scale zero "
                    + "dominate each other eventually, but evaluation at scale zero separates them. "
                    + "This explicit witness proves that the eventual order is a preorder and not a "
                    + "partial order."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("the-concrete-trade-face-has-two-incomparable-minima"),
                DeclarationHandle.Create(LeanPrefix + "trade_face_two_incomparable_minima"),
                H("The concrete trade face has two distinct incomparable minima"),
                StatementSource.FromAuthor(Display(F.Seq(
                    TradeReceipt(true), F.Sp, F.InMacro, F.Sp,
                    F.Id("tradeFace"), F.Sp, F.Land, F.Sp,
                    TradeReceipt(false), F.Sp, F.InMacro, F.Sp,
                    F.Id("tradeFace"), F.Sp, F.Land, F.Sp,
                    TradeReceipt(true), F.Sp, F.Neq, F.Sp, TradeReceipt(false),
                    F.Sp, F.Land, F.Sp, F.Neg, F.Open, TradeReceipt(true), F.Sp,
                    F.Leq, F.Sp, TradeReceipt(false), F.Close, F.Sp, F.Land, F.Sp,
                    F.Neg, F.Open, TradeReceipt(false), F.Sp, F.Leq, F.Sp,
                    TradeReceipt(true), F.Close))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Both concrete receipts are reachable from valid Boolean witnesses and are "
                    + "minimal among the reachable receipts. They are distinct because their forward "
                    + "time profiles differ, while the preceding two lemmas prove mutual "
                    + "incomparability. A face with one minimal element would be a point; this pair "
                    + "earns the name price face by exhibiting two independent cost directions."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("price-face-membership-implies-valid-witness-reachability"),
                DeclarationHandle.Create(LeanPrefix + "priceFace_mem_reachable"),
                H("Membership in the price face implies reachability by a valid witness"),
                StatementSource.FromAuthor(Display(F.Seq(
                    F.Forall, F.Sp, F.Id("Object"), F.Comma, F.Sp, F.Id("Witness"), F.Comma,
                    F.Sp, F.Id("AlgorithmCost"), F.Comma, F.Sp, F.Id("RateCost"), F.Comma,
                    F.Sp, F.Id("PhysicalCost"), F.Comma, F.Sp, F.Id("HeatCost"), F.Sp,
                    F.InMacro, F.Sp, F.Operatorname, F.Grp(F.Id("Type")), F.Comma, F.Sp,
                    F.Forall, F.Sp, F.Id("candidate"), F.Sp, F.InMacro, F.Sp,
                    TaxReceiptType(), F.Comma,
                    F.Sp, F.Id("candidate"), F.Sp, F.InMacro, F.Sp, PriceFace(),
                    F.Sp, F.Rightarrow, F.Sp, F.Exists, F.Sp,
                    F.Id("witness"), F.Comma, F.Sp, F.Id("validWitness"), F.Open,
                    F.Id("witness"), F.Comma, F.Sp, F.Id("left"), F.Comma, F.Sp,
                    F.Id("right"), F.Close, F.Sp, F.Land, F.Sp,
                    F.Id("receipt"), F.Open, F.Id("witness"), F.Close, F.Eq, F.Sp,
                    F.Id("candidate")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The first coordinate of the Minimal predicate is exactly the reachability "
                    + "condition. Consequently, any candidate lying in priceFace comes from some "
                    + "witness accepted by the supplied validity predicate."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("price-face-is-empty-when-no-valid-witness-exists"),
                DeclarationHandle.Create(LeanPrefix + "priceFace_eq_empty_of_no_valid"),
                H("The price face is empty when no valid witness exists"),
                StatementSource.FromAuthor(Display(F.Seq(
                    F.Neg, F.Exists, F.Sp, F.Id("witness"), F.Comma, F.Sp,
                    F.Id("validWitness"), F.Open, F.Id("witness"), F.Comma, F.Sp,
                    F.Id("left"), F.Comma, F.Sp, F.Id("right"), F.Close, F.Sp,
                    F.Rightarrow, F.Sp, PriceFace(), F.Sp, F.Eq, F.Sp, F.Emptyset))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If the validity predicate has no witness for the two objects, the preceding "
                    + "reachability result rules out every possible member of priceFace. Set extensionality "
                    + "then identifies the face with the empty set."))),
                DescribeRole.Theorem)
        )));
}
