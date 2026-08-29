using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Adelic;

internal sealed class ToroidalTemperednessCriterionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The strip-native Riemann hypothesis is equivalent to temperedness of every "
            + "nontrivial toroidal Eisenstein parameter.",
        H("Toroidal Temperedness Criterion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("rh-iff-all-toroidal-eisenstein-tempered"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Adelic/ToroidalTemperednessCriterion."
                        + "rh_iff_all_toroidal_eisenstein_tempered"),
                H("RH is equivalent to toroidal Eisenstein temperedness"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The left side is the canonical nontrivial strip-zero formulation. "
                            + "On the right, toroidal invisibility is stated directly by "
                            + "vanishing of every completed-zeta-times-twist period.")),
                    Paragraph(Text(
                        "Pointwise twist nonvanishing makes simultaneous period vanishing "
                            + "equivalent to a completed-zeta zero. The frozen completed-zeta "
                            + "zero-locus theorem then identifies exactly the strip zeros.")),
                    Paragraph(Text(
                        "The normalized principal-series parameter is s minus one half. Its "
                            + "real part vanishes exactly on the critical line, which is the "
                            + "displayed temperedness condition."))),
                DescribeRole.Theorem))));

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new Formula.BoundVariable(FormulaIdentifier.Create(name), domain);

    private static Formula EqualTo(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula NotEqualTo(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula TheoremFormula()
    {
        Formula type = Call("Type");
        Formula complex = Call("Complex");
        Formula indexType = F.Id("Index");
        Formula point = F.Id("s");
        Formula index = F.Id("i");
        Formula twist = F.Id("T");
        Formula half = new Formula.Fraction(D(1), D(2));
        Formula twistAtPoint = Apply(Apply(twist, index), point);
        Formula completedAtPoint = Call("completedRiemannZeta", point);

        Formula nonvanishing = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("s", complex)],
            new Formula.BindMany(
                FormulaQuantifier.Exists,
                [Bound("i", indexType)],
                NotEqualTo(twistAtPoint, D(0))));
        Formula stripRh = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("s", complex)],
            Implies(
                Call("IsNontrivialZero", point),
                EqualTo(Call("Re", point), half)));
        Formula invisible = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("i", indexType)],
            EqualTo(
                Seq(completedAtPoint, Sp, Times, Sp, twistAtPoint),
                D(0)));
        Formula tempered = EqualTo(
            Call("Re", Seq(point, Sp, Minus, Sp, half)),
            D(0));
        Formula allToroidalTempered = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("s", complex)],
            Implies(invisible, tempered));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [
                Bound("Index", type),
                Bound("T", Arrow(indexType, Arrow(complex, complex))),
            ],
            Implies(
                nonvanishing,
                new Formula.Logic(
                    stripRh,
                    FormulaLogicOperator.Iff,
                    allToroidalTempered))));
    }
}
