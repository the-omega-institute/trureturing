using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ArithUnits;

internal sealed class CyclicPlaneAffineCommutatorDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ArithUnits/CyclicPlaneAffineCommutator.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Affine commutators and translation rigidity modulo 157.",
        H("Affine Commutators and Translation Rigidity Modulo 157"),
        Blocks(
            Theorem(
                "affine-commutator-translation",
                "affine_commutator_translation_invariant",
                "The affine commutator is a translation",
                CommutatorFormula(),
                "The two compositions have the same multiplier six. Comparing their "
                    + "constant terms turns equality of their invariant images into "
                    + "invariance under translation by 2(c-d)."),
            Theorem(
                "distinct-center-cardinality-divisibility",
                "card_dvd_of_distinct_center_affine_invariant",
                "Distinct centers force cardinality divisibility by 157",
                DivisibilityFormula(),
                "For distinct centers the commutator translation is nonzero. The degree-zero "
                    + "translation moment vanishes in characteristic 157, so the finite-set "
                    + "cardinality is zero modulo 157."),
            Theorem(
                "distinct-center-classification",
                "distinct_center_affine_classification",
                "Distinct-center invariant supports are empty or full",
                ClassificationFormula(),
                "A subset of the 157-element field has cardinality at most 157. Combining "
                    + "this bound with 157-divisibility leaves only the empty and full sets."),
            Theorem(
                "distinct-center-thirteen-obstruction",
                "no_thirteen_element_distinct_center_affine_invariant",
                "Thirteen elements cannot support distinct affine centers",
                ThirteenFormula(),
                "The divisibility theorem immediately rules out cardinality thirteen. This "
                    + "is the affine noncommutation consequence used by the projective-plane "
                    + "application."),
            Paragraph(Text(
                "The module isolates the affine group commutator and its additive orbit "
                    + "consequence. It does not formalize the First Multiplier Theorem, the "
                    + "Singer correspondence, or arbitrary projective-plane nonexistence.")))));

    private static DocumentBlock.Describe Theorem(
        string id, string declaration, string heading, Formula formula, string paragraph) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(heading),
            StatementSource.FromAuthor(Disp(formula)),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(paragraph))),
            DescribeRole.Theorem);

    private static Formula CommutatorFormula()
    {
        Formula d = F.Id("D");
        Formula c = F.Id("c");
        Formula e = F.Id("d");
        Formula assumptions = And(
            Equal(Image(d, Call("affineDouble", c)), d),
            Equal(Image(d, Call("affineTriple", e)), d));
        Formula conclusion = Equal(
            Image(d, AddMap(Multiply(Num(2), Sub(c, e)))), d);
        return ForAll(
            [Bound("D", Finset(ZMod(Num(157)))), Bound("c", ZMod(Num(157))),
                Bound("d", ZMod(Num(157)))],
            Implies(assumptions, conclusion));
    }

    private static Formula DivisibilityFormula()
    {
        Formula d = F.Id("D");
        Formula c = F.Id("c");
        Formula e = F.Id("d");
        Formula assumptions = And(
            Equal(Image(d, Call("affineDouble", c)), d),
            And(
                Equal(Image(d, Call("affineTriple", e)), d),
                NotEqual(c, e)));
        return ForAll(
            [Bound("D", Finset(ZMod(Num(157)))), Bound("c", ZMod(Num(157))),
                Bound("d", ZMod(Num(157)))],
            Implies(assumptions,
                new Formula.Relation(Num(157), FormulaRelationOperator.Divides, Card(d))));
    }

    private static Formula ClassificationFormula()
    {
        Formula d = F.Id("D");
        Formula c = F.Id("c");
        Formula e = F.Id("d");
        Formula assumptions = And(
            Equal(Image(d, Call("affineDouble", c)), d),
            And(Equal(Image(d, Call("affineTriple", e)), d), NotEqual(c, e)));
        Formula target = Or(
            Equal(d, Call("emptyFinset")),
            Equal(d, Call("univFinset", ZMod(Num(157)))));
        return ForAll(
            [Bound("D", Finset(ZMod(Num(157)))), Bound("c", ZMod(Num(157))),
                Bound("d", ZMod(Num(157)))],
            Implies(assumptions, target));
    }

    private static Formula ThirteenFormula()
    {
        Formula d = F.Id("D");
        Formula c = F.Id("c");
        Formula e = F.Id("d");
        Formula assumptions = And(
            Equal(Card(d), Num(13)),
            And(
                Equal(Image(d, Call("affineDouble", c)), d),
                And(Equal(Image(d, Call("affineTriple", e)), d), NotEqual(c, e))));
        return ForAll(
            [Bound("D", Finset(ZMod(Num(157)))), Bound("c", ZMod(Num(157))),
                Bound("d", ZMod(Num(157)))],
            Implies(assumptions, F.Id("False")));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);

    private static Formula Image(Formula set, Formula map) => Call("image", set, map);
    private static Formula AddMap(Formula shift) => Call("translateBy", shift);
    private static Formula Card(Formula set) => Call("card", set);
    private static Formula Finset(Formula type) => Call("Finset", type);
    private static Formula ZMod(Formula modulus) => Call("ZMod", modulus);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula ForAll(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Or(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Or, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
}
