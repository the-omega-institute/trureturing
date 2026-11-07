using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ArithUnits;

internal sealed class CyclicPlaneThreeMultiplierObstructionDocument
    : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ArithUnits/CyclicPlaneThreeMultiplierObstruction.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The multiplier-three orbit obstruction modulo 157.",
        H("The Multiplier-Three Obstruction Modulo 157"),
        Blocks(
            Theorem(
                "order-of-three-modulo-157",
                "orderOf_three_zmod157",
                "Three has multiplicative order 78 modulo 157",
                OrderThree157Formula(),
                "Kernel-checked modular powers establish exponent 78 and exclude the proper "
                    + "prime-divisor exponents required by the finite-order criterion."),
            Theorem(
                "three-invariant-cardinality-residue",
                "card_of_invariant_under_mul_three",
                "Three-invariant cardinalities have residue zero or one",
                InvariantCardinalityFormula(),
                "The nonzero part is a union of free cyclic orbits of length 78. Splitting "
                    + "on whether zero is present leaves exactly the residues zero and one "
                    + "for the full set."),
            Theorem(
                "multiplier-three-obstruction",
                "multiplier_three_obstruction",
                "No thirteen-element affine multiplier-three relation exists modulo 157",
                ObstructionFormula(),
                "Translation by the affine fixed point conjugates a putative relation to "
                    + "pure three-invariance without changing cardinality. The resulting "
                    + "residue 13 contradicts the zero-or-one residue theorem modulo 78."),
            Paragraph(Text(
                "This module records the multiplier-three arithmetic that was previously "
                    + "only externally checked. It does not formalize the First Multiplier "
                    + "Theorem bridge, the Singer correspondence, or nonexistence of an "
                    + "arbitrary projective plane of order twelve.")))));

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

    private static Formula OrderThree157Formula() =>
        Equal(Call("orderOf", Typed(Num(3), ZMod(Num(157)))), Num(78));

    private static Formula InvariantCardinalityFormula()
    {
        Formula s = F.Id("S");
        Formula invariant = Equal(ImageMul(s, Num(3)), s);
        Formula residue = Relation(
            new Formula.Modulo(Card(s), Num(78)),
            FormulaRelationOperator.MemberOf,
            new Formula.SetLiteral([Num(0), Num(1)]));
        return ForAll([Bound("S", Finset(ZMod(Num(157))))], Implies(invariant, residue));
    }

    private static Formula ObstructionFormula()
    {
        Formula d = F.Id("D");
        Formula g = F.Id("g");
        Formula conclusion = NotEqual(ImageMul(d, Num(3)), ImageAdd(d, g));
        return ForAll(
            [Bound("D", Finset(ZMod(Num(157)))), Bound("g", ZMod(Num(157)))],
            Implies(Equal(Card(d), Num(13)), conclusion));
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

    private static Formula NotEqual(Formula left, Formula right) =>
        Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula ZMod(Formula modulus) => Call("ZMod", modulus);
    private static Formula Finset(Formula type) => Call("Finset", type);
    private static Formula Card(Formula set) => Call("card", set);
    private static Formula ImageMul(Formula set, Formula multiplier) =>
        Call("imageMul", set, multiplier);
    private static Formula ImageAdd(Formula set, Formula shift) =>
        Call("imageAdd", set, shift);
}
