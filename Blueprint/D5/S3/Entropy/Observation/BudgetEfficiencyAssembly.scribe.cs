using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy.Observation;

internal sealed class BudgetEfficiencyAssemblyDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Entropy/Observation/BudgetEfficiencyAssembly."
            + "budget_efficiency_assembly";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Refinement information, innovation counts, and finite closure-spectrum memory budgets "
            + "are assembled on the canonical finite carriers.",
        H("Budget and Efficiency Assembly"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("budget-efficiency-assembly"),
                DeclarationHandle.Create(Declaration),
                H("Refinement gain, innovation budget, and closure-spectrum telescope"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The finite past/future law and deterministic fine-to-coarse readout use "
                            + "the canonical predictive-memory and refinement-gain definitions. "
                            + "The first conjunct is the imported exact decomposition and its "
                            + "nonnegativity.")),
                    Paragraph(Text(
                        "A nonnegative summable innovation sequence with a total budget H obeys "
                            + "the canonical threshold-count bound. The final conjunct applies "
                            + "the finite observation quotient and complete-future quotient to "
                            + "the closure-spectrum log telescope; the endpoint is the realized "
                            + "readout image, not an arbitrary codomain complement.")),
                    Paragraph(Text(
                        "No new probability law, quotient, or resolution object is declared. "
                            + "The finite/infinite quotient bridge is proved locally from the "
                            + "existing future relations and the pinned quotient-range "
                            + "equivalence."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                items.Add(Comma);
                items.Add(Sp);
            }

            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Call(Formula name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(name), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                items.Add(Comma);
                items.Add(Sp);
            }

            items.Add(arguments[index]);
        }

        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Type() => Seq(Operatorname, Grp(F.Id("Type")));

    private static Formula RealType() => Seq(Mathbb, Grp(F.Id("R")));

    private static Formula NatType() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula Fintype(Formula carrier) =>
        Seq(OpenBracket, Operatorname, Grp(F.Id("Fintype")), Open, carrier, Close,
            CloseBracket);

    private static Formula Typed(Formula name, Formula type) =>
        Seq(name, Colon, Sp, type);

    private static Formula TheoremFormula()
    {
        Formula pType = F.Id("P");
        Formula fType = F.Id("F");
        Formula fineType = F.Id("Fine");
        Formula coarseType = F.Id("Coarse");
        Formula xType = F.Id("X");
        Formula qType = F.Id("Q");
        Formula p = F.Id("p");
        Formula z = F.Id("z");
        Formula fine = F.Id("fine");
        Formula forget = F.Id("forget");
        Formula innovation = F.Id("innovation");
        Formula h = F.Id("H");
        Formula epsilon = F.Id("epsilon");
        Formula update = F.Id("update");
        Formula readout = F.Id("readout");
        Formula k = F.Id("k");
        Formula law = Seq(
            Open, Forall, Sp, z, Colon, Sp, Call("Prod", pType, fType), Comma, Sp,
            D(0), Sp, Leq, Sp, Call("p", z), Close, Sp, Land, Sp,
            Sum, Underscore, Grp(z), Sp, Call("p", z), Sp, Eq, Sp, D(1));
        Formula first = Seq(
            Call("predictiveMemory", p, Call("comp", forget, fine)), Sp, Minus, Sp,
            Call("predictiveMemory", p, fine), Sp, Eq, Sp,
            Call("refinementGain", p, fine, forget), Sp, Land, Sp,
            D(0), Sp, Leq, Sp, Call("refinementGain", p, fine, forget));
        Formula second = Seq(
            Call("ncard", Call("thresholdSet", epsilon, innovation)), Sp, Leq, Sp,
            Call("divide", h, epsilon));
        Formula third = Seq(
            Sum, Underscore, Grp(Seq(k, InMacro, Call("range", Call("stabilityDepth", update, readout)))),
            Sp, Call("logIncrement", update, readout, k), Sp, Eq, Sp,
            Call("log", Call("completeClassCount", update, readout)), Sp, Minus, Sp,
            Call("log", Call("readoutImageCard", readout)));

        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, pType, Comma, Sp, fType, Comma, Sp, fineType, Comma, Sp,
                coarseType, Comma, Sp, xType, Comma, Sp, qType, Colon, Sp, Type(), Comma),
            Seq(Grp(), Fintype(pType), Sp, Fintype(fType), Sp, Fintype(fineType), Sp,
                Fintype(coarseType), Sp, Fintype(xType), Comma),
            Seq(Typed(p, Seq(Call("Prod", pType, fType), Sp, To, Sp, RealType())), Comma, Sp,
                law, Sp, Rightarrow),
            Seq(Typed(fine, Seq(pType, Sp, To, Sp, fineType)), Comma, Sp,
                Typed(forget, Seq(fineType, Sp, To, Sp, coarseType)), Comma),
            Seq(Typed(innovation, Seq(NatType(), Sp, To, Sp, RealType())), Comma, Sp,
                Typed(h, RealType()), Comma, Sp, Typed(epsilon, RealType()), Comma),
            Seq(Open, Forall, Sp, Typed(k, NatType()), Comma, Sp,
                D(0), Sp, Leq, Sp, Call(innovation, k), Close, Sp, Land, Sp,
                Call("Summable", innovation), Sp, Land, Sp,
                Call("tsum", innovation), Sp, Leq, Sp, h,
                Sp, Land, Sp, D(0), Sp, Lt, Sp, epsilon, Comma),
            Seq(Typed(update, Seq(xType, Sp, To, Sp, xType)), Comma, Sp,
                Typed(readout, Seq(xType, Sp, To, Sp, qType)), Rightarrow),
            Seq(Open, first, Close, Sp, Land, Sp, Open, second, Close, Sp, Land, Sp,
                Open, third, Close, Dot)
        ]));
    }
}
