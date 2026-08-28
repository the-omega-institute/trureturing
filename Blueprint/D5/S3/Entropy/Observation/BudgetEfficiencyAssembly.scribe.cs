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

    private static Formula Call(string name, params Formula[] arguments) =>
        Call(F.Id(name), arguments);

    private static Formula QualifiedCall(string prefix, string name, params Formula[] arguments) =>
        Seq(Operatorname, Grp(F.Id(prefix)), Dot, F.Id(name), Open,
            CallArguments(arguments), Close);

    private static Formula CallArguments(Formula[] arguments)
    {
        var items = new List<Formula>();
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                items.Add(Comma);
                items.Add(Sp);
            }

            items.Add(arguments[index]);
        }

        return Seq([.. items]);
    }

    private static Formula Type() => Seq(Operatorname, Grp(F.Id("Type")));

    private static Formula RealType() => Seq(Mathbb, Grp(F.Id("R")));

    private static Formula NatType() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Prod(Formula left, Formula right) =>
        Call("Prod", left, right);

    private static Formula Entropy(Formula value) =>
        Seq(F.Id("H"), Open, value, Close);

    private static Formula Fintype(Formula carrier) =>
        Seq(OpenBracket, Operatorname, Grp(F.Id("Fintype")), Open, carrier, Close,
            CloseBracket);

    private static Formula Typed(Formula name, Formula type) =>
        Seq(name, Colon, Sp, type);

    private static Formula TheoremFormula()
    {
        Formula pType = F.Id("P");
        Formula fType = F.Id("F");
        Formula xType = F.Id("X");
        Formula qType = F.Id("Q");
        Formula cFamily = F.Id("C");
        Formula natural = NatType();
        Formula real = RealType();
        Formula p = F.Id("p");
        Formula z = F.Id("z");
        Formula n = F.Id("n");
        Formula epsilon = F.Id("epsilon");
        Formula mass = F.Id("mass");
        Formula h = F.Id("h");
        Formula g = F.Id("g");
        Formula eta = F.Id("eta");
        Formula q = F.Id("q");
        Formula forget = F.Id("forget");
        Formula hrefine = F.Id("hrefine");
        Formula update = F.Id("update");
        Formula readout = F.Id("readout");
        Formula k = F.Id("k");
        Formula successor = Seq(n, Plus, D(1));
        Formula cN = Call("C", n);
        Formula cSucc = Call("C", successor);
        Formula qN = Call("q", n);
        Formula qSucc = Call("q", successor);
        Formula massDefinition = Seq(
            Typed(mass, Arrow(pType, real)), Sp, Eq, Sp, Call("marginal", p), Comma);
        Formula hDefinition = Seq(
            Typed(h, Arrow(natural, real)), Sp, Eq, Sp,
            Seq(F.Id("fun"), Sp, n, Mapsto, Sp,
                Call("conditionalEntropy", Call("completionLaw", mass, qN, qSucc))), Comma);
        Formula gDefinition = Seq(
            Typed(g, Arrow(natural, real)), Sp, Eq, Sp,
            Seq(F.Id("fun"), Sp, n, Mapsto, Sp,
                Call("refinementGain", p, qSucc, Call("forget", n))), Comma);
        Formula etaDefinition = Seq(
            Typed(eta, Arrow(natural, real)), Sp, Eq, Sp,
            Seq(F.Id("fun"), Sp, n, Mapsto, Sp,
                Call("if", EqExpr(Call("h", n), D(0)), D(0),
                    Seq(Call("g", n), Sp, Slash, Sp, Call("h", n)))), Comma);
        Formula hp = Seq(
            Open, Forall, Sp, z, Colon, Sp, Prod(pType, fType), Comma, Sp,
            D(0), Sp, Leq, Sp, Call("p", z), Close, Sp, Land, Sp,
            Sum, Underscore, Grp(z), Sp, Call("p", z), Sp, Eq, Sp, D(1));
        Formula refine = Seq(
            Forall, Sp, n, Colon, Sp, natural, Comma, Sp,
            Call("q", n), Sp, Eq, Sp,
            Call("comp", Call("forget", n), Call("q", successor)));
        Formula closure = Seq(
            Sum, Underscore, Grp(Seq(k, InMacro,
                Call("range", Call("observationStabilityDepth", update, readout)))),
            Sp, Grp(Seq(
                Call("log", Call("observationClassCount", update, readout,
                    Seq(k, Plus, D(1)))), Sp, Minus, Sp,
                Call("log", Call("observationClassCount", update, readout, k)))),
            Sp, Eq, Sp,
            Call("log", Call("infiniteObservationClassCount", update, readout)),
            Sp, Minus, Sp,
            Call("log", QualifiedCall("Nat", "card", QualifiedCall("Set", "range", readout))));
        Formula first = Seq(
            Forall, Sp, n, Colon, Sp, natural, Comma, Sp,
            Open, D(0), Sp, Leq, Sp, Call("g", n), Sp, Land, Sp,
            Call("g", n), Sp, Leq, Sp, Call("h", n), Sp, Land, Sp,
            Open, D(0), Sp, Lt, Sp, Call("h", n), Rightarrow, Sp,
            Call("eta", n), Sp, Eq, Sp,
            Call("g", n), Sp, Slash, Sp, Call("h", n), Close, Sp, Land, Sp,
            Open, Call("h", n), Sp, Eq, Sp, D(0), Rightarrow, Sp,
            Call("eta", n), Sp, Eq, Sp, D(0), Close, Close);
        Formula second = Seq(
            Call("Summable", h), Sp, Land, Sp,
            Seq(Sum, Underscore, Grp(n), Caret, Grp(Infty), Sp,
                Call("h", n)), Sp, Leq, Sp, Entropy(mass), Sp, Land, Sp,
            Forall, Sp, epsilon, Colon, Sp, real, Comma, Sp,
            Open, D(0), Sp, Lt, Sp, epsilon, Rightarrow, Sp,
            Call("ncard", Seq(OpenBrace, n, InMacro, Sp, natural, Sp, Mid, Sp,
                epsilon, Sp, Leq, Sp, Call("h", n), CloseBrace)), Sp, Leq, Sp,
            Seq(Entropy(mass), Sp, Slash, Sp, epsilon), Close);

        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, pType, Comma, Sp, fType, Comma, Sp, xType, Comma, Sp,
                qType, Colon, Sp, Type(), Comma),
            Seq(Typed(cFamily, Arrow(natural, Type())), Comma, Sp,
                Fintype(pType), Sp, Fintype(fType), Sp, Fintype(xType), Comma),
            Seq(Typed(F.Id("fintypeC"), Seq(Forall, Sp, n, Colon, Sp, natural,
                Comma, Sp, Fintype(cN))), Comma),
            Seq(Typed(p, Arrow(Prod(pType, fType), real)), Comma, Sp,
                Typed(F.Id("hp"), hp), Comma),
            Seq(Typed(q, Seq(Forall, Sp, n, Colon, Sp, natural, Comma, Sp,
                Arrow(pType, cN))), Comma, Sp,
                Typed(forget, Seq(Forall, Sp, n, Colon, Sp, natural, Comma, Sp,
                    Arrow(cSucc, cN))), Comma),
            Seq(Typed(hrefine, refine), Comma, Sp,
                Typed(update, Arrow(xType, xType)), Comma, Sp,
                Typed(readout, Arrow(xType, qType)), Rightarrow),
            Seq(massDefinition, RowBreak, Grp(), hDefinition, RowBreak, Grp(),
                gDefinition, RowBreak, Grp(), etaDefinition, RowBreak, Grp(),
                Open, first, Close, Sp, Land, Sp, Open, second, Close, Sp, Land, Sp,
                Open, closure, Close, Dot)
        ]));
    }

    private static Formula EqExpr(Formula left, Formula right) =>
        Seq(left, Sp, Eq, Sp, right);
}
