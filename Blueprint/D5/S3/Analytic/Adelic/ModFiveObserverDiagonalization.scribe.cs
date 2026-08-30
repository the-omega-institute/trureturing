using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Adelic;

internal sealed class ModFiveObserverDiagonalizationDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Analytic/Adelic/ModFiveObserverDiagonalization."
            + "mod_five_observer_diagonalization";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The reflected Hurwitz sectors modulo five split into trivial and quadratic channels.",
        H("Mod-Five Observer Diagonalization"),
        Blocks(Describe.Lean(
            DescribeId.Create("mod-five-observer-diagonalization"),
            DeclarationHandle.Create(Declaration),
            H("Hadamard separation of the two reflected residue sectors"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The first channel is the sum of the Hurwitz zeta terms at residues one "
                        + "and four modulo five. The second channel uses residues two and "
                        + "three. Both are constructed with the canonical map from ZMod 5 "
                        + "to the unit additive circle.")),
                Paragraph(Text(
                    "The canonical quadratic character modulo five has values zero, one, "
                        + "minus one, minus one, and one. Consequently the sum and difference "
                        + "of the channels are the trivial and quadratic Dirichlet L-functions.")),
                Paragraph(Text(
                    "The unnormalized two-by-two Hadamard matrix packages the two scalar "
                        + "identities. The trivial-character clause records that restoring the "
                        + "deleted Euler factor at five gives the Riemann zeta channel.")),
                Paragraph(Text(
                    "The point s = 1 is excluded because the pointwise trivial-character "
                        + "Euler-factor identity is used away from its pole."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula s = F.Id("s");
        Formula h1 = Apply(new Formula.Subscript(F.Id("H"), D(1)), s);
        Formula h2 = Apply(new Formula.Subscript(F.Id("H"), D(2)), s);
        Formula scale = new Formula.Power(D(5), Seq(Minus, s));
        Formula zeta = Call("riemannZeta", s);
        Formula deletedFactor = Seq(
            Open, D(1), Sp, Minus, Sp, scale, Close, Sp, Times, Sp, zeta);
        Formula trivialL = Call("LFunctionTrivChar", D(5), s);
        Formula quadraticCharacter = F.Id("modFiveQuadraticCharacter");
        Formula quadraticL = Call("LFunction", quadraticCharacter, s);
        Formula sumChannel = Seq(
            scale, Sp, Times, Sp, Open, h1, Sp, Plus, Sp, h2, Close);
        Formula differenceChannel = Seq(
            scale, Sp, Times, Sp, Open, h1, Sp, Minus, Sp, h2, Close);
        Formula leftVector = Call("vec2", deletedFactor, quadraticL);
        Formula rightVector = Seq(
            scale, Sp, Times, Sp,
            Call(
                "mulVec",
                F.Id("modFiveObserverHadamard"),
                Call("vec2", h1, h2)));
        Formula characterValues = And(
            EqualTo(Apply(quadraticCharacter, D(0)), D(0)),
            And(
                EqualTo(Apply(quadraticCharacter, D(1)), D(1)),
                And(
                    EqualTo(Apply(quadraticCharacter, D(2)), Seq(Minus, D(1))),
                    And(
                        EqualTo(Apply(quadraticCharacter, D(3)), Seq(Minus, D(1))),
                        EqualTo(Apply(quadraticCharacter, D(4)), D(1))))));
        Formula conclusions = And(
            EqualTo(sumChannel, deletedFactor),
            And(
                EqualTo(differenceChannel, quadraticL),
                And(
                    EqualTo(leftVector, rightVector),
                    And(
                        EqualTo(sumChannel, trivialL),
                        And(EqualTo(trivialL, deletedFactor), characterValues)))));

        return Disp(new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create("s"), complex)],
            Implies(NotEqualTo(s, D(1)), conclusions)));
    }

    private static Formula EqualTo(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula NotEqualTo(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula Apply(Formula function, Formula argument) =>
        new Formula.Apply(function, [argument]);

    private static Formula Call(string name, params Formula[] arguments)
    {
        var pieces = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                pieces.Add(Comma);
                pieces.Add(Sp);
            }

            pieces.Add(arguments[index]);
        }

        pieces.Add(Close);
        return Seq([.. pieces]);
    }
}
