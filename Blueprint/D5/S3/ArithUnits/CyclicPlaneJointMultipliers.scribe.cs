using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ArithUnits;

internal sealed class CyclicPlaneJointMultipliersDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ArithUnits/CyclicPlaneJointMultipliers.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Joint multiplier-two and multiplier-three orbit classification modulo 157.",
        H("Joint Multiplier Orbits Modulo 157"),
        Blocks(
            Theorem(
                "joint-nonzero-orbit-divisibility",
                "joint_nonzero_card_dvd",
                "Joint nonzero orbit cardinality is divisible by 156",
                JointDivisibilityFormula(),
                "The two invariant unit actions give divisibility by 52 and 78. "
                    + "Their least common multiple is 156, so the nonzero support "
                    + "is a union of joint-orbit packets of that size."),
            Theorem(
                "joint-cardinality-residue",
                "joint_invariant_cardinality_residue",
                "Joint invariant cardinalities have residue zero or one",
                JointResidueFormula(),
                "Zero is the only possible exceptional fixed point. Splitting on its "
                    + "membership converts nonzero divisibility into the two displayed "
                    + "cardinality residues."),
            Theorem(
                "joint-invariant-classification",
                "joint_invariant_classification",
                "The joint invariant subsets are exactly four sets",
                JointClassificationFormula(),
                "The nonzero part has at most 156 elements and has cardinality divisible "
                    + "by 156; the zero-present case is shifted by one. This gives the "
                    + "empty set, the singleton zero, the nonzero field, and the full field."),
            Paragraph(Text(
                "This is a joint group-action consequence of the verified multiplier "
                    + "periods. It does not formalize the First Multiplier Theorem, the "
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

    private static Formula JointDivisibilityFormula()
    {
        Formula s = F.Id("S");
        Formula assumptions = And(
            Equal(ImageMul(s, Num(2)), s),
            Equal(ImageMul(s, Num(3)), s));
        Formula conclusion = new Formula.Relation(
            Num(156), FormulaRelationOperator.Divides,
            Call("card", Call("eraseZero", s)));
        return ForAll(
            [Bound("S", Finset(ZMod(Num(157))))],
            Implies(assumptions, conclusion));
    }

    private static Formula JointResidueFormula()
    {
        Formula s = F.Id("S");
        Formula assumptions = And(
            Equal(ImageMul(s, Num(2)), s),
            Equal(ImageMul(s, Num(3)), s));
        Formula conclusion = new Formula.Relation(
            new Formula.Modulo(Card(s), Num(156)),
            FormulaRelationOperator.MemberOf,
            new Formula.SetLiteral([Num(0), Num(1)]));
        return ForAll(
            [Bound("S", Finset(ZMod(Num(157))))],
            Implies(assumptions, conclusion));
    }

    private static Formula JointClassificationFormula()
    {
        Formula s = F.Id("S");
        Formula assumptions = And(
            Equal(ImageMul(s, Num(2)), s),
            Equal(ImageMul(s, Num(3)), s));
        Formula target = Or(
            Equal(s, Call("emptyFinset")),
            Or(
                Equal(s, new Formula.SetLiteral([Num(0)])),
                Or(
                    Equal(s, Call("nonzeroField", ZMod(Num(157)))),
                    Equal(s, Call("univFinset", ZMod(Num(157)))))));
        return ForAll(
            [Bound("S", Finset(ZMod(Num(157))))],
            Implies(assumptions, target));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula ForAll(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    private static Formula Relation(
        Formula left, FormulaRelationOperator relation, Formula right) =>
        new Formula.Relation(left, relation, right);

    private static Formula Equal(Formula left, Formula right) =>
        Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Or(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Or, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula ZMod(Formula modulus) => Call("ZMod", modulus);
    private static Formula Finset(Formula type) => Call("Finset", type);
    private static Formula Card(Formula set) => Call("card", set);
    private static Formula ImageMul(Formula set, Formula multiplier) =>
        Call("imageMul", set, multiplier);
}
