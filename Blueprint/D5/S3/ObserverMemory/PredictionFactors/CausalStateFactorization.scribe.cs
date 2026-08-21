using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.PredictionFactors;

internal sealed class CausalStateFactorizationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Predictively sufficient interfaces uniquely factor onto the causal-state image.",
        H("Causal State Factorization"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("predictive-sufficiency-induces-the-causal-state-factor"),
                DeclarationHandle.Create(
                    "D5/S3/ObserverMemory/PredictionFactors/CausalStateFactorization."
                        + "causal_state_factorization"),
                H("Predictive sufficiency induces the unique causal-state factor"),
                StatementSource.FromAuthor(FactorizationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let K assign a future law to each past and let r be an interface. "
                            + "Predictive sufficiency supplies a predictor Kbar on interface "
                            + "values such that K equals Kbar after r.")),
                    Paragraph(Text(
                        "The canonical causal-state map is the range factorization of K. The "
                            + "theorem constructs its unique factor through the realized image "
                            + "of r and states publicly that this factor agrees with Kbar on every "
                            + "realized interface value.")),
                    Paragraph(Text(
                        "Consequently two pasts with different future laws cannot have the same "
                            + "interface value. Using the realized image is essential: without "
                            + "surjectivity of r, Kbar may take additional values away from that "
                            + "image, so its whole image need not equal the image of K.")),
                    Paragraph(Text(
                        "The proof directly applies the repository's exact inductive sufficiency "
                            + "criterion. Pinned Mathlib supplies rangeFactorization, its "
                            + "surjectivity theorem, and uniqueness after composition with a "
                            + "surjection."))),
                DescribeRole.Theorem))));

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Apply(Formula function, params Formula[] arguments)
    {
        var items = new List<Formula> { function, Open };
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

    private static Formula FactorizationFormula()
    {
        Formula pastType = F.Id("P");
        Formula interfaceType = F.Id("R");
        Formula lawType = F.Id("L");
        Formula interfaceMap = F.Id("r");
        Formula futureLaw = F.Id("K");
        Formula predictor = F.Id("Kbar");
        Formula factor = F.Id("phi");
        Formula state = F.Id("s");
        Formula past = F.Id("p");
        Formula pastPrime = Seq(F.Id("p"), Apos);
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula interfaceRange = Call("range", interfaceMap);
        Formula lawRange = Call("range", futureLaw);
        Formula interfaceProjection = Call("rangeFactorization", interfaceMap);
        Formula lawProjection = Call("rangeFactorization", futureLaw);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp,
            Typed(Seq(pastType, Comma, Sp, interfaceType, Comma, Sp, lawType), type),
            Comma, RowBreak, Grp(),
            Typed(interfaceMap, new Formula.TypeArrow(pastType, interfaceType)), Comma, Sp,
            Typed(futureLaw, new Formula.TypeArrow(pastType, lawType)), Comma, Sp,
            Typed(predictor, new Formula.TypeArrow(interfaceType, lawType)), Comma, RowBreak, Grp(),
            futureLaw, Sp, Eq, Sp, predictor, Sp, Circ, Sp, interfaceMap,
            Sp, Rightarrow, RowBreak, Grp(),
            Open, Exists, Bang, Sp, factor, Colon, Sp,
            new Formula.TypeArrow(interfaceRange, lawRange), Comma, RowBreak, Grp(),
            lawProjection, Sp, Eq, Sp, factor, Sp, Circ, Sp, interfaceProjection,
            Sp, Land, RowBreak, Grp(),
            Forall, Sp, Typed(state, interfaceRange), Comma, Sp,
            Call("val", Apply(factor, state)), Sp, Eq, Sp,
            Apply(predictor, Call("val", state)), Close, Sp, Land, RowBreak, Grp(),
            Forall, Sp, Typed(Seq(past, Comma, Sp, pastPrime), pastType), Comma, Sp,
            Apply(futureLaw, past), Sp, Neq, Sp, Apply(futureLaw, pastPrime),
            Sp, Rightarrow, Sp,
            Apply(interfaceMap, past), Sp, Neq, Sp, Apply(interfaceMap, pastPrime), Dot,
            End, Grp(F.Id("gathered"))));
    }
}
