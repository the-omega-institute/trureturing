using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ArithUnits;

internal sealed class AffineGroupCommutatorRigidityDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ArithUnits/AffineGroupCommutatorRigidity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Affine group commutators and support rigidity in prime residue fields.",
        H("Affine Group Commutators and Support Rigidity in Prime Residue Fields"),
        Blocks(
            Theorem(
                "commutator-formula",
                "centeredAffine_commutator_formula",
                "The affine commutator is a translation",
                CommutatorFormula(),
                "The two centered affine compositions have equal multiplier and differ by "
                    + "the translation (a-1)(b-1)(c-d)."),
            Theorem(
                "commutator-zero",
                "commutatorShift_eq_zero_iff",
                "Centered affine maps commute only in the degenerate cases",
                CommutatorZeroFormula(),
                "In a prime residue field, vanishing of the commutator is equivalent to "
                    + "a trivial multiplier, b trivial, or equal centers."),
            Theorem(
                "translation-invariance",
                "affine_commutator_translation_invariant",
                "Invariant supports inherit the commutator translation",
                TranslationFormula(),
                "Equality of the two invariant images transports the ring identity to a "
                    + "Finset translation action."),
            Theorem(
                "cardinality-divisibility",
                "card_dvd_of_nontrivial_distinct_center_affine_invariant",
                "Nontrivial distinct centers force p-divisibility",
                DivisibilityFormula(),
                "A nonzero translation in characteristic p annihilates the degree-zero "
                    + "moment, so p divides the support cardinality."),
            Theorem(
                "prime-field-classification",
                "distinct_center_affine_classification",
                "Prime-field invariant supports are empty or full",
                ClassificationFormula(),
                "The p-divisibility conclusion and the p-element field-size bound leave "
                    + "only the empty and universal supports."),
            Theorem(
                "cardinality-exclusion",
                "no_card_not_dvd_of_nontrivial_distinct_center_affine_invariant",
                "Cardinalities outside the p-divisible class are impossible",
                ExclusionFormula(),
                "The divisibility theorem immediately excludes any prescribed cardinality "
                    + "that is not divisible by p."),
            Paragraph(Text(
                "This package isolates the affine group commutator and its arithmetic "
                    + "support consequence for every prime residue field. It does not "
                    + "claim that the two multipliers generate the full multiplicative "
                    + "group or formalize a projective-plane existence theorem.")))));

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
        Formula a = F.Id("a");
        Formula b = F.Id("b");
        Formula c = F.Id("c");
        Formula d = F.Id("d");
        Formula x = F.Id("x");
        Formula left = Call("centeredAffine", a, c,
            Call("centeredAffine", b, d, x));
        Formula right = Add(
            Call("centeredAffine", b, d,
                Call("centeredAffine", a, c, x)),
            Call("commutatorShift", a, b, c, d));
        return ForAll(
            [Bound("p", F.Id("Nat")), Bound("a", Call("ZMod", F.Id("p"))),
                Bound("b", Call("ZMod", F.Id("p"))), Bound("c", Call("ZMod", F.Id("p"))),
                Bound("d", Call("ZMod", F.Id("p"))), Bound("x", Call("ZMod", F.Id("p")))],
            Equal(left, right));
    }

    private static Formula CommutatorZeroFormula()
    {
        Formula a = F.Id("a");
        Formula b = F.Id("b");
        Formula c = F.Id("c");
        Formula d = F.Id("d");
        Formula target = Or(Equal(a, Num(1)), Or(Equal(b, Num(1)), Equal(c, d)));
        return ForAll(
            [Bound("p", F.Id("Nat")), Bound("a", Call("ZMod", F.Id("p"))),
                Bound("b", Call("ZMod", F.Id("p"))), Bound("c", Call("ZMod", F.Id("p"))),
                Bound("d", Call("ZMod", F.Id("p")))],
            Iff(Equal(Call("commutatorShift", a, b, c, d), Num(0)), target));
    }

    private static Formula TranslationFormula()
    {
        Formula d = F.Id("D");
        Formula a = F.Id("a");
        Formula b = F.Id("b");
        Formula c = F.Id("c");
        Formula e = F.Id("d");
        Formula assumptions = And(
            Equal(Image(d, Call("centeredAffine", a, c)), d),
            Equal(Image(d, Call("centeredAffine", b, e)), d));
        Formula target = Equal(
            Image(d, AddMap(Call("commutatorShift", a, b, c, e))), d);
        return ForAll(
            [Bound("p", F.Id("Nat")), Bound("D", Finset(Call("ZMod", F.Id("p")))),
                Bound("a", Call("ZMod", F.Id("p"))), Bound("b", Call("ZMod", F.Id("p"))),
                Bound("c", Call("ZMod", F.Id("p"))), Bound("d", Call("ZMod", F.Id("p")))],
            Implies(assumptions, target));
    }

    private static Formula DivisibilityFormula()
    {
        Formula d = F.Id("D");
        Formula a = F.Id("a");
        Formula b = F.Id("b");
        Formula c = F.Id("c");
        Formula e = F.Id("d");
        Formula assumptions = And(
            Equal(Image(d, Call("centeredAffine", a, c)), d),
            And(Equal(Image(d, Call("centeredAffine", b, e)), d),
                And(And(NotEqual(a, Num(1)), NotEqual(b, Num(1))), NotEqual(c, e))));
        return ForAll(
            [Bound("p", F.Id("Nat")), Bound("D", Finset(Call("ZMod", F.Id("p")))),
                Bound("a", Call("ZMod", F.Id("p"))), Bound("b", Call("ZMod", F.Id("p"))),
                Bound("c", Call("ZMod", F.Id("p"))), Bound("d", Call("ZMod", F.Id("p")))],
            Implies(assumptions,
                new Formula.Relation(F.Id("p"), FormulaRelationOperator.Divides, Card(d))));
    }

    private static Formula ClassificationFormula()
    {
        Formula d = F.Id("D");
        Formula a = F.Id("a");
        Formula b = F.Id("b");
        Formula c = F.Id("c");
        Formula e = F.Id("d");
        Formula assumptions = And(
            Equal(Image(d, Call("centeredAffine", a, c)), d),
            And(Equal(Image(d, Call("centeredAffine", b, e)), d),
                And(And(NotEqual(a, Num(1)), NotEqual(b, Num(1))), NotEqual(c, e))));
        Formula target = Or(Equal(d, Call("emptyFinset")),
            Equal(d, Call("univFinset", Call("ZMod", F.Id("p")))));
        return ForAll(
            [Bound("p", F.Id("Nat")), Bound("D", Finset(Call("ZMod", F.Id("p")))),
                Bound("a", Call("ZMod", F.Id("p"))), Bound("b", Call("ZMod", F.Id("p"))),
                Bound("c", Call("ZMod", F.Id("p"))), Bound("d", Call("ZMod", F.Id("p")))],
            Implies(assumptions, target));
    }

    private static Formula ExclusionFormula()
    {
        Formula d = F.Id("D");
        Formula a = F.Id("a");
        Formula b = F.Id("b");
        Formula c = F.Id("c");
        Formula e = F.Id("d");
        Formula assumptions = And(
            Equal(Card(d), F.Id("n")),
            And(Equal(Image(d, Call("centeredAffine", a, c)), d),
                And(Equal(Image(d, Call("centeredAffine", b, e)), d),
                    And(And(NotEqual(a, Num(1)), NotEqual(b, Num(1))),
                        And(NotEqual(c, e),
                            new Formula.Not(new Formula.Relation(
                                F.Id("p"), FormulaRelationOperator.Divides, F.Id("n"))))))));
        return ForAll(
            [Bound("p", F.Id("Nat")), Bound("n", F.Id("Nat")),
                Bound("D", Finset(Call("ZMod", F.Id("p")))),
                Bound("a", Call("ZMod", F.Id("p"))), Bound("b", Call("ZMod", F.Id("p"))),
                Bound("c", Call("ZMod", F.Id("p"))), Bound("d", Call("ZMod", F.Id("p")))],
            Implies(assumptions, F.Id("False")));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);

    private static Formula Image(Formula set, Formula map) => Call("image", set, map);
    private static Formula AddMap(Formula shift) => Call("translateBy", shift);
    private static Formula Card(Formula set) => Call("card", set);
    private static Formula Finset(Formula type) => Call("Finset", type);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Or(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Or, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, right);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula ForAll(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
}
