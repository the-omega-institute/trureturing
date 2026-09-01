using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Completion;

internal sealed class ClosureNonimplicationTripleDocument : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Observer/Completion/ClosureNonimplicationTriple."
            + "closure_nonimplication_triple";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Prediction, operational, classical-answer, and self-description closure are separated "
            + "by three concrete observer constructions.",
        H("Three Closure Nonimplications"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("three-closure-nonimplications"),
                DeclarationHandle.Create(Declaration),
                H("Prediction, operation, classical answers, and self-description separate"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "On the two-address cyclic carrier, the constant Unit readout is "
                            + "prediction-stable at depth zero. Its deterministic readout "
                            + "projection together with the cyclic shift generates a proper "
                            + "subalgebra: every generator commutes with the shift, whereas the "
                            + "frozen clock-shift commutator is nonzero.")),
                    Paragraph(Text(
                        "The second countermodel applies the frozen nontrivial-window theorem: "
                            + "the canonical clock and shift generate the full matrix algebra, "
                            + "but that generated algebra has no unital complex character.")),
                    Paragraph(Text(
                        "The third countermodel applies the frozen rank-one-context theorem. "
                            + "Its projector-trace readout is injective on the complete matrix "
                            + "carrier, while a Boolean evaluator indexed twice by that same "
                            + "carrier and a fixed-point-free twist exhibit an escaped diagonal.")),
                    Paragraph(Text(
                        "Repository search found the three exact component owners but no "
                            + "whole-statement owner. Pinned Mathlib supplied only the generic "
                            + "commutation lemma for elements of a generated algebra."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula two = D(2);
        Formula one = D(1);
        Formula complex = F.Id("Complex");
        Formula state = Call("ZMod", two);
        Formula matrix = Call("Matrix", state, state, complex);
        Formula tomographyIndex = Call("Fin", one);
        Formula tomographyMatrix =
            Call("Matrix", tomographyIndex, tomographyIndex, complex);
        Formula point = F.Id("x");
        Formula update = Seq(Open, point, Sp, Mapsto, Sp, point, Sp, Minus, Sp, D(1), Close);
        Formula readout = Seq(Open, point, Sp, Mapsto, Sp, F.Id("unit"), Close);
        Formula projection = Call("deterministicProjection", readout, F.Id("unit"));
        Formula shift = Call("shiftMatrix", two);
        Formula poorOperationalAlgebra = new Formula.Relation(
            Call("AlgebraAdjoin", complex, Call("pair", projection, shift)),
            FormulaRelationOperator.NotEqual,
            Call("top", matrix));
        Formula predictionCountermodel = And(
            Call("predictionStableAt", update, readout, D(0)),
            poorOperationalAlgebra);

        Formula windowAlgebra = Call("windowGeneratedAlgebra", two);
        Formula operationalCountermodel = And(
            Equal(windowAlgebra, Call("top", matrix)),
            Call("IsEmpty", Call("ComplexAlgHom", windowAlgebra, complex)));

        Formula context = F.Id("context");
        Formula evaluation = F.Id("evaluation");
        Formula twist = F.Id("twist");
        Formula y = F.Id("y");
        Formula a = F.Id("a");
        Formula diagonal = Seq(
            Open, a, Sp, Mapsto, Sp,
            Call("twist", Call("evaluation", a, a)), Close);
        Formula diagonalCountermodel = new Formula.BindMany(
            FormulaQuantifier.Exists,
            [Bound("context", Arrow(Call("Fin", two), Call("RankOneContext", one)))],
            And(
                Call("Injective", Call("contextReadout", context)),
                new Formula.BindMany(
                    FormulaQuantifier.Exists,
                    [
                        Bound("evaluation", Arrow(tomographyMatrix,
                            Arrow(tomographyMatrix, F.Id("Bool")))),
                        Bound("twist", Arrow(F.Id("Bool"), F.Id("Bool"))),
                    ],
                    And(
                        new Formula.BindMany(
                            FormulaQuantifier.ForAll,
                            [Bound("y", F.Id("Bool"))],
                            NotEqual(Call("twist", y), y)),
                        new Formula.Not(new Formula.Relation(
                            diagonal,
                            FormulaRelationOperator.MemberOf,
                            Call("range", evaluation)))))));

        return F.Disp(And(
            predictionCountermodel,
            And(operationalCountermodel, diagonalCountermodel)));
    }

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);
}
