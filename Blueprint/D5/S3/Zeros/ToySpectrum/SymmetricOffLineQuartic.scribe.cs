using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros.ToySpectrum;

internal sealed class SymmetricOffLineQuarticDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An entire function exists whose nonempty zero set has full reflection and "
            + "conjugation symmetry while every zero remains off the critical line.",
        H("Symmetric Off-Line Quartic"),
        Blocks(Describe.Lean(
            DescribeId.Create("a-fully-symmetric-off-line-entire-function-exists"),
            DeclarationHandle.Create(
                "D5/S3/Zeros/ToySpectrum/SymmetricOffLineQuartic."
                    + "symmetric_off_line_entire_exists"),
            H("A fully symmetric off-line entire function exists"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The witness is the centered quartic from the family theorem at unit "
                        + "transverse and vertical displacements. It is complex differentiable "
                        + "everywhere and has an explicit zero, so the zero-set clauses are not "
                        + "vacuous.")),
                Paragraph(Text(
                    "Reflection invariance and conjugation covariance of the quartic imply "
                        + "invariance of its zero set under both generators. Every zero has real "
                        + "part different from the critical abscissa; applying a hypothetical "
                        + "universal localization implication to the same nonempty zero set gives "
                        + "the displayed contradiction."))),
            DescribeRole.Theorem)),
        []));

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new Formula.BoundVariable(FormulaIdentifier.Create(name), domain);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula EqualTo(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula NotEqualTo(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula TheoremFormula()
    {
        Formula complex = Call("Complex");
        Formula functionType = Seq(
            Open,
            new Formula.TypeArrow(complex, complex),
            Close);
        Formula witness = F.Id("F");
        Formula general = F.Id("G");
        Formula s = F.Id("s");
        Formula critical = Call("criticalAbscissa");
        Formula witnessAtS = Apply(witness, s);
        Formula generalAtS = Apply(general, s);

        Formula witnessEntire = Call("Differentiable", complex, witness);
        Formula witnessNonempty = new Formula.BindMany(
            FormulaQuantifier.Exists,
            [Bound("s", complex)],
            EqualTo(witnessAtS, D(0)));
        Formula witnessReflection = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("s", complex)],
            Implies(
                EqualTo(witnessAtS, D(0)),
                EqualTo(Apply(witness, Seq(D(1), Sp, Minus, Sp, s)), D(0))));
        Formula witnessConjugation = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("s", complex)],
            Implies(
                EqualTo(witnessAtS, D(0)),
                EqualTo(Apply(witness, Call("conj", s)), D(0))));
        Formula witnessOffLine = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("s", complex)],
            Implies(
                EqualTo(witnessAtS, D(0)),
                NotEqualTo(Call("Re", s), critical)));

        Formula generalEntire = Call("Differentiable", complex, general);
        Formula generalNonempty = new Formula.BindMany(
            FormulaQuantifier.Exists,
            [Bound("s", complex)],
            EqualTo(generalAtS, D(0)));
        Formula generalReflection = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("s", complex)],
            Implies(
                EqualTo(generalAtS, D(0)),
                EqualTo(Apply(general, Seq(D(1), Sp, Minus, Sp, s)), D(0))));
        Formula generalConjugation = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("s", complex)],
            Implies(
                EqualTo(generalAtS, D(0)),
                EqualTo(Apply(general, Call("conj", s)), D(0))));
        Formula generalLocalization = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("s", complex)],
            Implies(
                EqualTo(generalAtS, D(0)),
                EqualTo(Call("Re", s), critical)));
        Formula boxedNonimplication = new Formula.Not(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("G", functionType)],
            Implies(
                generalEntire,
                Implies(
                    generalNonempty,
                    Implies(
                        generalReflection,
                        Implies(generalConjugation, generalLocalization))))));

        Formula witnessProperties = And(
            witnessEntire,
            And(
                witnessNonempty,
                And(
                    witnessReflection,
                    And(
                        witnessConjugation,
                        And(witnessOffLine, boxedNonimplication)))));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.Exists,
            [Bound("F", functionType)],
            witnessProperties));
    }
}
