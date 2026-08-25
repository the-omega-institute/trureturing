using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ObserverMemory.RefinementDescent;

internal sealed class PredictiveSufficiencyDescentDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete-future quotient classes carry a well-defined update and readout, "
            + "with a unique pair of induced maps making both projection squares commute.",
        H("Predictive Sufficiency Descent with Unique Induced Maps"),
        Blocks(Describe.Lean(
            DescribeId.Create("predictive-sufficiency-descent-well-defined-unique"),
            DeclarationHandle.Create(
                "D5/S3/ObserverMemory/RefinementDescent/PredictiveSufficiencyDescent."
                    + "predictive_sufficiency_descent_well_defined_unique"),
            H("Well-defined quotient dynamics and unique commuting induced maps"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The state carrier is the canonical quotient by equality of every "
                        + "future readout. If two representatives have the same completion "
                        + "projection, their updated projections and current readouts agree.")),
                Paragraph(Text(
                    "The public existential-unique clause exposes a pair consisting of an "
                        + "update on the completed state and a readout from it. Each component "
                        + "commutes with the canonical projection, and quotient surjectivity "
                        + "forces this pair to be unique.")),
                Paragraph(Text(
                    "The imported PredictionCompletion declarations construct the quotient, "
                        + "projection, quotient update, and quotient readout. The withdrawn "
                        + "all-computation-rule receipt is not reused as a wrapper.")),
                Paragraph(Text(
                    "Repository search found no existing theorem with both representative "
                        + "well-definedness and pair uniqueness at this generality; pinned "
                        + "Mathlib supplies Quotient.exact and Quotient.mk_surjective."))),
            DescribeRole.Theorem))));

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula And(params Formula[] formulas)
    {
        Formula result = formulas[^1];
        for (var index = formulas.Length - 2; index >= 0; index--)
            result = new Formula.Logic(formulas[index], FormulaLogicOperator.And, result);
        return result;
    }

    private static Formula Implies(Formula hypothesis, Formula conclusion) =>
        new Formula.Logic(hypothesis, FormulaLogicOperator.Implies, conclusion);

    private static Formula EqualTo(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Subscript(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));

    private static Formula TheoremFormula()
    {
        Formula xType = F.Id("X");
        Formula oType = F.Id("O");
        Formula update = F.Id("update");
        Formula readout = F.Id("readout");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula completed = Call("CompletedState", update, readout);
        Formula projection = F.Id("completionProjection");
        Formula quotientUpdate = F.Id("completionUpdate");
        Formula quotientReadout = F.Id("completionReadout");
        Formula projectionAt(Formula state) =>
            Apply(projection, update, readout, state);
        Formula updateProjection(Formula state) =>
            projectionAt(Apply(update, state));
        Formula representativeWellDefined = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("x", xType), Bound("y", xType)],
            Implies(
                EqualTo(projectionAt(x), projectionAt(y)),
                And(
                    EqualTo(updateProjection(x), updateProjection(y)),
                    EqualTo(Apply(readout, x), Apply(readout, y)))));

        Formula induced = F.Id("induced");
        Formula inducedUpdate = Subscript(induced, D(1));
        Formula inducedReadout = Subscript(induced, D(2));
        Formula commutingSquares = And(
            new Formula.Bind(
                FormulaQuantifier.ForAll,
                FormulaIdentifier.Create("x"),
                xType,
                EqualTo(
                    Apply(inducedUpdate, projectionAt(x)),
                    updateProjection(x))),
            new Formula.Bind(
                FormulaQuantifier.ForAll,
                FormulaIdentifier.Create("x"),
                xType,
                EqualTo(
                    Apply(inducedReadout, projectionAt(x)),
                    Apply(readout, x))));
        Formula inducedType = Call(
            "Prod",
            Arrow(completed, completed),
            Arrow(completed, oType));
        Formula existsUnique = Seq(
            Exists, Bang, Sp, induced, Colon, Sp, inducedType, Comma, Esc,
            commutingSquares);

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("X", Seq(Operatorname, Grp(F.Id("Type")))),
                Bound("O", Seq(Operatorname, Grp(F.Id("Type")))),
                Bound("update", Arrow(xType, xType)),
                Bound("readout", Arrow(xType, oType)),
            ],
            And(representativeWellDefined, existsUnique)));
    }
}
