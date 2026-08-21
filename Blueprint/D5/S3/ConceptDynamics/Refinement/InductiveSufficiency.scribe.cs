using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Refinement;

internal sealed class InductiveSufficiencyDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite history determines a prediction exactly when the prediction factors through its image.",
        H("Inductive Sufficiency"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("finite-history-factorization-is-the-inductive-sufficiency-criterion"),
                DeclarationHandle.Create(
                    "D5/S3/ConceptDynamics/Refinement/InductiveSufficiency."
                        + "inductive_sufficiency_criterion"),
                H("Finite-history factorization is the inductive sufficiency criterion"),
                StatementSource.FromAuthor(SufficiencyFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let h map source states to their realized finite histories and let K be "
                            + "a future prediction. The repository relation Refines K "
                            + "(rangeFactorization h) says exactly that there is a map Kbar from "
                            + "the realized image of h to predictions such that K equals Kbar after "
                            + "the canonical range factorization. The theorem identifies this image "
                            + "factorization with constancy of K on every fiber of h.")),
                    Paragraph(Text(
                        "The negated criterion is included in the theorem rather than left as prose. "
                            + "Failure of factorization is equivalent to the existence of two source "
                            + "states x and y with the same finite history and different predictions. "
                            + "Thus repeated past data alone does not force repeated future behavior; "
                            + "the displayed descent condition is the explicit premise that does.")),
                    Paragraph(Text(
                        "This statement covers the source's factorization equivalence, its image-valued "
                            + "factor Kbar, the same-history/different-prediction witness, and both clauses "
                            + "of the final Hume display. The listed examples of additional premises "
                            + "(finite-state stability, stationarity, Markov completion, analyticity, "
                            + "causal closure, a complexity bound, and mechanism invariance) are not "
                            + "separate formal claims because the source gives them no definitions; they "
                            + "remain explanatory examples of conditions that could establish descent.")),
                    Paragraph(Text(
                        "The repository supplies the exact ConceptDynamics.Refines relation. Pinned "
                            + "Mathlib supplies the exact Function.FactorsThrough predicate and the "
                            + "image-valued Set.rangeFactorization map; all are reused directly. Repository "
                            + "and pinned-source searches found no single theorem combining the image "
                            + "factorization equivalence with the explicit failure witnesses."))),
                DescribeRole.Theorem))));

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

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula SufficiencyFormula()
    {
        Formula sourceType = F.Id("X");
        Formula historyType = F.Id("H");
        Formula predictionType = F.Id("Y");
        Formula history = F.Id("h");
        Formula predict = F.Id("K");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula type = Seq(Operatorname, Grp(F.Id("Type")));
        Formula rangeFactorization = Apply(
            Seq(Operatorname, Grp(F.Id("rangeFactorization"))), history);
        Formula fiberConstant = Apply(
            Seq(Operatorname, Grp(F.Id("FactorsThrough"))), predict, history);
        Formula imageFactor = Apply(
            Seq(Operatorname, Grp(F.Id("Refines"))), predict, rangeFactorization);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp,
            Typed(Seq(sourceType, Comma, Sp, historyType, Comma, Sp, predictionType), type),
            Comma, RowBreak,
            Typed(history, new Formula.TypeArrow(sourceType, historyType)), Comma, Sp,
            Typed(predict, new Formula.TypeArrow(sourceType, predictionType)), Comma, RowBreak,
            Open, fiberConstant, Sp, Leftrightarrow, Sp, imageFactor,
            Close, Sp, Land, RowBreak,
            Open, Neg, imageFactor, Sp, Leftrightarrow, Sp,
            Exists, Sp, Typed(Seq(x, Comma, Sp, y), sourceType), Comma, Sp,
            Apply(history, x), Sp, Eq, Sp, Apply(history, y), Sp, Land, Sp,
            Apply(predict, x), Sp, Neq, Sp, Apply(predict, y), Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
