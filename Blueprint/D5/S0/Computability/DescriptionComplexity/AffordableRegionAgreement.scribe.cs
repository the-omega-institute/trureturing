using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability.DescriptionComplexity;

internal sealed class AffordableRegionAgreementDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An affordable finite-region patch forces agreement for a loss-minimal candidate.",
        H("Affordable Region Agreement"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("affordable-region-agreement"),
                DeclarationHandle.Create(
                    "D5/S0/Computability/DescriptionComplexity/AffordableRegionAgreement.affordable_region_agreement"),
                H("Affordable regions contain no remaining disagreement"),
                StatementSource.FromAuthor(AffordableFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The candidate and truth are total functions on the natural numbers. "
                        + "A finite record fixes their observed values, while a finite region P "
                        + "specifies the values replaced by the truth function.")),
                    Paragraph(Text(
                        "The patch-cost premise bounds the corrected function by the candidate "
                        + "complexity plus price(P) and a fixed overhead. The accounting premise "
                        + "makes the natural-number subtraction explicit, so an affordable patch "
                        + "remains within the stated budget and stays consistent with the record.")),
                    Paragraph(Text(
                        "Loss is valued in an arbitrary preorder. Correcting a genuine disagreement "
                        + "on a nonempty region, while changing nothing outside it, is assumed to "
                        + "strictly lower loss. This contradicts candidate minimality among all "
                        + "record-consistent functions within budget, forcing pointwise agreement.")),
                    Paragraph(Text(
                        "Pinned Mathlib has no universal-machine or description-complexity theorem "
                        + "with these semantics. The proof therefore exposes cost and loss behavior "
                        + "as hypotheses and reuses only finite-set patching, natural arithmetic, "
                        + "and preorder contradiction."))),
                DescribeRole.Theorem)),
        []));

    private static Formula Typeclass(string name, Formula argument) =>
        Seq(OpenBracket, Operatorname, Grp(F.Id(name)), Open, argument, Close, CloseBracket);

    private static Formula Apply(Formula function, Formula argument) =>
        Seq(function, Open, argument, Close);

    private static Formula AffordableFormula()
    {
        Formula outputType = F.Id("Output"), lossType = F.Id("Loss");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula finsetNaturals = Call("Finset", naturals);
        Formula truth = F.Id("truth"), candidate = F.Id("g");
        Formula record = F.Id("record"), region = F.Id("P");
        Formula complexity = F.Id("complexity"), price = F.Id("price");
        Formula budget = F.Id("budget"), overhead = F.Id("overhead");
        Formula loss = F.Id("loss"), n = F.Id("n"), h = F.Id("h");
        Formula functionType = Seq(naturals, Sp, To, Sp, outputType);
        Formula truthAt(Formula index) =>
            Seq(Operatorname, Grp(truth), Open, index, Close);
        Formula candidateAt(Formula index) => Apply(candidate, index);
        Formula hAt(Formula index) => Apply(h, index);
        Formula complexityOf(Formula function) =>
            Seq(Operatorname, Grp(complexity), Open, function, Close);
        Formula priceOf(Formula finiteRegion) =>
            Seq(Operatorname, Grp(price), Open, finiteRegion, Close);
        Formula lossOf(Formula function) =>
            Seq(Operatorname, Grp(loss), Open, function, Close);
        Formula inRegion = Seq(n, Sp, InMacro, Sp, region);
        Formula patched = Seq(Open, n, Colon, Sp, naturals, Sp, Mapsto, Sp,
            Call("ite", inRegion, truthAt(n), candidateAt(n)), Close);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, outputType, Comma, Sp, lossType, Colon, Sp, type,
            Comma, RowBreak, Grp(),
            Typeclass("Preorder", lossType), Comma, RowBreak, Grp(),
            Forall, Sp, truth, Comma, Sp, candidate, Colon, Sp, functionType,
            Comma, RowBreak, Grp(),
            Forall, Sp, record, Comma, Sp, region, Colon, Sp, finsetNaturals,
            Comma, RowBreak, Grp(),
            Forall, Sp, complexity, Colon, Sp,
            Open, functionType, Close, Sp, To, Sp, naturals, Comma, Sp,
            Forall, Sp, price, Colon, Sp, finsetNaturals, Sp, To, Sp, naturals,
            Comma, RowBreak, Grp(),
            Forall, Sp, budget, Comma, Sp, overhead, Colon, Sp, naturals,
            Comma, Sp, Forall, Sp, loss, Colon, Sp,
            Open, functionType, Close, Sp, To, Sp, lossType, Comma, RowBreak, Grp(),
            Open, Forall, Sp, n, Colon, Sp, naturals, Comma, Sp,
            n, Sp, InMacro, Sp, record, Sp, Rightarrow, Sp,
            candidateAt(n), Sp, Eq, Sp, truthAt(n), Close,
            Comma, RowBreak, Grp(),
            complexityOf(patched), Sp, Leq, Sp,
            complexityOf(candidate), Sp, Plus, Sp, priceOf(region), Sp, Plus, Sp, overhead,
            Comma, RowBreak, Grp(),
            complexityOf(candidate), Sp, Plus, Sp, overhead, Sp, Leq, Sp, budget,
            Comma, RowBreak, Grp(),
            Open, Forall, Sp, h, Colon, Sp, functionType, Comma, Sp,
            Call("Nonempty", region), Sp, Rightarrow, Sp,
            Open, Forall, Sp, n, Colon, Sp, naturals, Comma, Sp,
            Neg, Sp, Open, inRegion, Close, Sp, Rightarrow, Sp,
            hAt(n), Sp, Eq, Sp, candidateAt(n), Close, Sp, Rightarrow, Sp,
            Open, Forall, Sp, n, Colon, Sp, naturals, Comma, Sp,
            inRegion, Sp, Rightarrow, Sp, hAt(n), Sp, Eq, Sp, truthAt(n), Close,
            Sp, Rightarrow, Sp,
            Open, Exists, Sp, n, Colon, Sp, naturals, Comma, Sp,
            inRegion, Sp, Land, Sp, candidateAt(n), Sp, Neq, Sp, truthAt(n), Close,
            Sp, Rightarrow, Sp, lossOf(h), Sp, Lt, Sp, lossOf(candidate), Close,
            Comma, RowBreak, Grp(),
            Open, Forall, Sp, h, Colon, Sp, functionType, Comma, Sp,
            Open, Forall, Sp, n, Colon, Sp, naturals, Comma, Sp,
            n, Sp, InMacro, Sp, record, Sp, Rightarrow, Sp,
            hAt(n), Sp, Eq, Sp, truthAt(n), Close, Sp, Rightarrow, Sp,
            complexityOf(h), Sp, Leq, Sp, budget, Sp, Rightarrow, Sp,
            lossOf(candidate), Sp, Leq, Sp, lossOf(h), Close,
            Comma, RowBreak, Grp(),
            Operatorname, Grp(F.Id("price")), Open, F.Id("P"), Close,
            Sp, Leq, Sp, F.Id("budget"), Sp, Minus, Sp,
            Operatorname, Grp(F.Id("complexity")), Open, F.Id("g"), Close,
            Sp, Minus, Sp, F.Id("overhead"), Sp, Rightarrow, Sp,
            Forall, Sp, F.Id("n"), Sp, InMacro, Sp, F.Id("P"),
            Comma, Esc, F.Id("g"), Open, F.Id("n"), Close,
            Sp, Eq, Sp, Operatorname, Grp(F.Id("truth")),
            Open, F.Id("n"), Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
