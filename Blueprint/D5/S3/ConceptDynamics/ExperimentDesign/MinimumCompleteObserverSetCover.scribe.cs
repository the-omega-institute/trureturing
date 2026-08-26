using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.ExperimentDesign;

internal sealed class MinimumCompleteObserverSetCoverDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Minimum-cost complete finite observer families are exactly minimum-cost set covers.",
        H("Minimum Complete Observers as Set Cover"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("minimum-complete-observer-is-set-cover"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/ExperimentDesign/"
                        + "MinimumCompleteObserverSetCover."
                        + "minimum_complete_observer_is_set_cover"),
                H("The minimum complete observer problem is weighted set cover"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The finite state carrier is X = Fin n. Its unordered-pair universe "
                            + "contains exactly distinct state pairs, and the detector set for "
                            + "observer i contains the pairs on which its readout differs.")),
                    Paragraph(Text(
                        "For each finite observer selection J, C(J) is the sum of the supplied "
                            + "real candidate costs. No positivity assumption is added: the "
                            + "theorem compares the same objective over two extensionally equal "
                            + "feasible families.")),
                    Paragraph(Text(
                        "The imported finite experiment cover criterion identifies joint-readout "
                            + "injectivity with coverage of the full distinct-pair universe. It "
                            + "therefore transports both feasibility of J and its cost comparison "
                            + "against every feasible candidate K."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        Apply(Seq(Operatorname, Grp(F.Id(name))), arguments);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Pair(Formula left, Formula right) =>
        Seq(OpenBrace, left, Comma, Sp, right, CloseBrace);

    private static Formula TheoremFormula()
    {
        Formula natural = Seq(Mathbb, Grp(F.Id("N")));
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula type = Call("Type");
        Formula size = F.Id("n");
        Formula observerType = F.Id("I");
        Formula output = F.Id("O");
        Formula cost = F.Id("c");
        Formula readout = F.Id("q");
        Formula selected = F.Id("J");
        Formula candidate = F.Id("K");
        Formula observer = F.Id("i");
        Formula left = F.Id("x");
        Formula right = F.Id("y");
        Formula stateType = Call("Fin", size);
        Formula pairUniverse = new Formula.Subscript(F.Id("U"), F.Id("X"));
        Formula detector = new Formula.Subscript(F.Id("D"), observer);
        Formula selectedType = Call("Finset", observerType);

        Formula universeDefinition = Seq(
            pairUniverse, Colon, Eq, Sp,
            OpenBrace, Pair(left, right), Sp, Mid, Sp,
            left, Comma, Sp, right, Sp, InMacro, Sp, stateType, Comma, Sp,
            left, Sp, Neq, Sp, right, CloseBrace);
        Formula detectorDefinition = Seq(
            Forall, Sp, observer, Sp, InMacro, Sp, observerType, Comma, Sp,
            detector, Colon, Eq, Sp,
            OpenBrace, Pair(left, right), Sp, InMacro, Sp, pairUniverse,
            Sp, Mid, Sp,
            Apply(Apply(readout, observer), left), Sp, Neq, Sp,
            Apply(Apply(readout, observer), right), CloseBrace);

        Formula selectionCost(Formula selection) => Seq(
            Sum, Underscore,
            Grp(observer, Sp, InMacro, Sp, selection), Sp,
            Apply(cost, observer));
        Formula costDefinition = Seq(
            Forall, Sp, selected, Sp, InMacro, Sp, selectedType, Comma, Sp,
            Call("C", selected), Colon, Eq, Sp, selectionCost(selected));
        Formula identifies(Formula selection) =>
            Call("Injective", Call("jointReadout", Call("restrict", readout, selection)));
        Formula covers(Formula selection) => Equal(
            pairUniverse,
            Call("Union", Seq(observer, Sp, InMacro, Sp, selection), detector));
        Formula costAt(Formula selection) => Call("C", selection);

        Formula minimumComplete = Seq(
            identifies(selected), Sp, Land, Sp,
            Open, Forall, Sp, Typed(candidate, selectedType), Comma, Sp,
            identifies(candidate), Sp, Rightarrow, Sp,
            costAt(selected), Sp, Leq, Sp, costAt(candidate), Close);
        Formula minimumCover = Seq(
            covers(selected), Sp, Land, Sp,
            Open, Forall, Sp, Typed(candidate, selectedType), Comma, Sp,
            covers(candidate), Sp, Rightarrow, Sp,
            costAt(selected), Sp, Leq, Sp, costAt(candidate), Close);

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, Typed(size, natural), Comma, Sp,
                Typed(observerType, type), Comma, Sp,
                Typed(output, Arrow(observerType, type)), Comma),
            Seq(
                Typed(cost, Arrow(observerType, real)), Comma, Sp,
                readout, Colon, Sp, Forall, Sp,
                Typed(observer, observerType), Comma, Sp,
                stateType, Sp, To, Sp, Apply(output, observer), Comma),
            Seq(Typed(selected, selectedType), Comma),
            Seq(F.Id("X"), Colon, Eq, Sp, stateType, Comma, Sp, universeDefinition, Comma),
            Seq(detectorDefinition, Comma, Sp, costDefinition, Comma),
            Seq(Open, minimumComplete, Close, Sp, Iff, Sp),
            Seq(Open, minimumCover, Close, Dot),
        ]));
    }
}
