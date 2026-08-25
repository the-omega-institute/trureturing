using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Diagonal.Probability;

internal sealed class LinearMarginConcentrationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Diagonal listings satisfy the corrected linear-margin bound and concentrate at the typical distance density.",
        H("Linear Margin and Typical Distance Density"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("linear-margin-and-typical-density-concentration"),
                DeclarationHandle.Create(
                    "D5/S0/Diagonal/Probability/LinearMarginConcentration."
                        + "linear_margin_concentration"),
                H("Linear margins concentrate at the nonzero-choice density"),
                StatementSource.FromAuthor(MainFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For a finite value type Y of cardinality at least two, a self-map f, "
                            + "and a lower density alpha strictly between zero and (card(Y)-1)/card(Y), "
                            + "the first conjunct gives the corrected finite KL-Chernoff bound for every "
                            + "finite address type satisfying the displayed threshold restriction.")),
                    Paragraph(Text(
                        "The second conjunct states that the corrected bound tends to zero. The third "
                            + "states that the actual probability of any row missing the linear margin "
                            + "also tends to zero, which is the asymptotically almost-sure linear escape "
                            + "clause. The fourth quantifies over every upper density between the typical "
                            + "density and one and states two-sided concentration of the minimum-distance "
                            + "density.")),
                    Paragraph(Text(
                        "The proof directly combines the four frozen diagonal-margin theorems. It "
                            + "introduces no replacement probability, distance, divergence, or carrier. "
                            + "The displayed probability names abbreviate the finite uniform cardinality "
                            + "ratios written explicitly in the Lean statement."))),
                DescribeRole.Theorem)),
        [
            DocumentEdge.Dependency.Create(GidRef.Create("D5/S0/Diagonal/TypicalDensity")),
        ]));

    private static Formula MainFormula()
    {
        Formula value = F.Id("Y");
        Formula address = F.Id("A");
        Formula map = F.Id("f");
        Formula alpha = F.Id("alpha");
        Formula alphaHi = F.Id("beta");
        Formula cardY = Call("card", value);
        Formula cardA = Call("card", address);
        Formula typical = new Formula.Fraction(Subtract(cardY, D(1)), cardY);
        Formula adjusted = new Formula.Fraction(
            Multiply(alpha, cardA),
            Subtract(cardA, D(1)));
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula finiteBound = Seq(
            Forall, Sp, address, Colon, Sp, type, Comma, Sp,
            Open, Call("Fintype", address), Sp, Land, Sp,
            D(2), Sp, Leq, Sp, cardA, Sp, Land, Sp,
            adjusted, Sp, Lt, Sp, typical, Close, Sp, Rightarrow, Sp,
            Call("marginFailureProbability", map, alpha), Sp, Leq, Sp,
            Call("linearMarginBound", cardY, alpha, cardA));
        Formula boundLimit = Limit(
            Call("linearMarginBound", cardY, alpha, address), address);
        Formula failureLimit = Limit(
            Call("marginFailureProbability", map, alpha), address);
        Formula densityLimit = Seq(
            Forall, Sp, alphaHi, Sp, InMacro, Sp, real, Comma, Sp,
            Open, typical, Sp, Lt, Sp, alphaHi, Sp, Land, Sp,
            alphaHi, Sp, Lt, Sp, D(1), Close, Sp, Rightarrow, Sp,
            Limit(
                Call("typicalDensityFailureProbability", map, alpha, alphaHi),
                address));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, value, Colon, Sp, type, Comma, Sp,
            map, Colon, Sp, new Formula.TypeArrow(value, value), Comma, Sp,
            alpha, Sp, InMacro, Sp, real, Comma, RowBreak, Grp(),
            Open, Call("Fintype", value), Sp, Land, Sp,
            D(2), Sp, Leq, Sp, cardY, Sp, Land, Sp,
            D(0), Sp, Lt, Sp, alpha, Sp, Land, Sp,
            alpha, Sp, Lt, Sp, typical, Close, Sp, Rightarrow, RowBreak, Grp(),
            Open, finiteBound, Close, Sp, Land, RowBreak, Grp(),
            Open, boundLimit, Close, Sp, Land, RowBreak, Grp(),
            Open, failureLimit, Close, Sp, Land, RowBreak, Grp(),
            Open, densityLimit, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }

    private static Formula Limit(Formula body, Formula index) =>
        Seq(Lim, Underscore, Grp(index, To, Infty), body, Eq, D(0));
}
