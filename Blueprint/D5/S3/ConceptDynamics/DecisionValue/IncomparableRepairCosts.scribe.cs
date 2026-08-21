using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DecisionValue;

internal sealed class IncomparableRepairCostsDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite two-repair cost face has two distinct Pareto-minimal incomparable receipts.",
        H("Incomparable Repair Costs"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("incomparable-repairs-have-no-unique-cost-choice"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/DecisionValue/IncomparableRepairCosts."
                        + "incomparable_repairs_no_unique_choice"),
                H("Incomparable repairs have no unique cost choice"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The finite Bool witness represents two repairs. Their imported tax receipts "
                            + "are distinct minimal elements of the same valid cost face, while neither "
                            + "receipt is componentwise below the other.")),
                    Paragraph(Text(
                        "Thus the formal cost order exposes a Pareto tradeoff: one repair improves one "
                            + "coordinate while the other improves the opposing coordinate. No unique "
                            + "choice follows from this order alone; an external priority rule would be "
                            + "additional structure.")),
                    Paragraph(Text(
                        "The Lean declaration is a direct wrapper around the existing frozen theorem "
                            + "`PriceFaceOrder.trade_face_two_incomparable_minima`; no ethical predicate "
                            + "or domain-specific responsibility notion is encoded."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula TheoremFormula()
    {
        Formula first = Apply(F.Id("tradeReceipt"), F.Id("true"));
        Formula second = Apply(F.Id("tradeReceipt"), F.Id("false"));
        Formula face = F.Id("tradeFace");
        return Disp(Seq(
            first, Sp, InMacro, Sp, face, Sp, Land, Sp,
            second, Sp, InMacro, Sp, face, Sp, Land, Sp,
            first, Sp, Neq, Sp, second, Sp, Land, Sp,
            Neg, Open, first, Sp, Le, Sp, second, Close, Sp, Land, Sp,
            Neg, Open, second, Sp, Le, Sp, first, Close, Dot));
    }
}
