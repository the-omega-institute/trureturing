using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.PredictionFactors;

internal sealed class ConditionalProbabilityProfileMinimalityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complete conditional probability profile is the minimal predictive concept.",
        H("Conditional Probability Profile Minimality"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("conditional-probability-profile-is-minimal"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/PredictionFactors/ConditionalProbabilityProfileMinimality."
                        + "conditional_probability_profile_is_minimal"),
                H("Conditional probability profiles form the minimal sufficient concept"),
                StatementSource.FromAuthor(MinimalityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A probability kernel K assigns every finite source state its complete "
                            + "conditional law in PMF(Y). An interface r is predictively "
                            + "sufficient when K factors as Kbar after r.")),
                    Paragraph(Text(
                        "The realized conditional-law concept is the canonical range "
                            + "factorization of K. Every sufficient interface induces a unique "
                            + "map from its realized image onto this concept, and that map "
                            + "agrees with Kbar on every realized interface value.")),
                    Paragraph(Text(
                        "Composing the induced map with inclusion into PMF(Y) recovers K itself. "
                            + "Thus the canonical object retains the whole conditional "
                            + "probability profile, rather than selecting one future outcome.")),
                    Paragraph(Text(
                        "The final public clause states the corresponding separation law: two "
                            + "states with different conditional distributions cannot share an "
                            + "interface value in any sufficient concept."))),
                DescribeRole.Theorem))));

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

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

    private static Formula MinimalityFormula()
    {
        Formula stateType = F.Id("X");
        Formula futureType = F.Id("Y");
        Formula interfaceType = F.Id("B");
        Formula kernel = F.Id("K");
        Formula readout = F.Id("r");
        Formula predictor = F.Id("Kbar");
        Formula factor = F.Id("phi");
        Formula state = F.Id("s");
        Formula left = F.Id("x");
        Formula right = Seq(F.Id("x"), Apos);
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula laws = Call("PMF", futureType);
        Formula readoutRange = Call("range", readout);
        Formula kernelRange = Call("range", kernel);
        Formula readoutProjection = Call("rangeFactorization", readout);
        Formula kernelProjection = Call("rangeFactorization", kernel);
        Formula inclusion = Seq(Operatorname, Grp(F.Id("val")));

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp,
            Typed(Seq(stateType, Comma, Sp, futureType, Comma, Sp, interfaceType), type),
            Comma, RowBreak, Grp(),
            OpenBracket, Operatorname, Grp(F.Id("Fintype")), Open, stateType, Close,
            CloseBracket, Comma, RowBreak, Grp(),
            Typed(kernel, new Formula.TypeArrow(stateType, laws)), Comma, Sp,
            Typed(readout, new Formula.TypeArrow(stateType, interfaceType)), Comma,
            RowBreak, Grp(),
            Typed(predictor, new Formula.TypeArrow(interfaceType, laws)), Comma, Sp,
            kernel, Sp, Eq, Sp, predictor, Sp, Circ, Sp, readout,
            Sp, Rightarrow, RowBreak, Grp(),
            Open, Exists, Bang, Sp, factor, Colon, Sp,
            new Formula.TypeArrow(readoutRange, kernelRange), Comma, RowBreak, Grp(),
            kernelProjection, Sp, Eq, Sp, factor, Sp, Circ, Sp, readoutProjection,
            Sp, Land, RowBreak, Grp(),
            Open, Forall, Sp, Typed(state, readoutRange), Comma, Sp,
            Call("val", Apply(factor, state)), Sp, Eq, Sp,
            Apply(predictor, Call("val", state)), Close, Sp, Land, RowBreak, Grp(),
            kernel, Sp, Eq, Sp, inclusion, Sp, Circ, Sp, factor,
            Sp, Circ, Sp, readoutProjection, Close, Sp, Land, RowBreak, Grp(),
            Forall, Sp, Typed(Seq(left, Comma, Sp, right), stateType), Comma, Sp,
            Apply(kernel, left), Sp, Neq, Sp, Apply(kernel, right), Sp, Rightarrow, Sp,
            Apply(readout, left), Sp, Neq, Sp, Apply(readout, right), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
