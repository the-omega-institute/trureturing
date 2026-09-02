using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.PrimeForms.GoldenEuler;

internal sealed class ModFiveLocalEulerFactorDocument
    : IScribeDocumentDefinition
{
    private const string Handle =
        "D5/S3/PrimeForms/GoldenEuler/ModFiveLocalEulerFactor.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The mod-five local observer determinant splits into its even and odd channel factors.",
        H("Mod-Five Local Euler Factor"),
        Blocks(Describe.Lean(
            DescribeId.Create("mod-five-local-euler-factor"),
            DeclarationHandle.Create(Handle + "mod_five_local_observer_determinant"),
            H("The two canonical observer channels give the two local factors"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The imported golden local branch operator is the canonical sum of "
                        + "the even projection and the quadratic-character-weighted odd "
                        + "projection. No second operator definition is introduced here.")),
                Paragraph(Text(
                    "Its generic inverse determinant is the product denominator. "
                        + "Substituting the prime scale gives the Riemann and quadratic "
                        + "Dirichlet local factors.")),
                Paragraph(Text(
                    "The imported even and odd channels are complementary. The same "
                        + "operator acts by one on every even-channel vector and by the "
                        + "mod-five character on every odd-channel vector, so their "
                        + "one-dimensional inverse determinants are the displayed factors."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula complex = Call("Complex");
        Formula primes = Seq(F.Id("Nat"), Dot, F.Id("Primes"));
        Formula finTwo = Call("Fin", D(2));
        Formula branchSpace = Call("BranchSpace");
        Formula matrixTwo = Call("Matrix", finTwo, finTwo, complex);
        Formula p = F.Id("p");
        Formula x = F.Id("x");
        Formula s = F.Id("s");
        Formula chi = F.Id("chi");
        Formula localOperator = F.Id("localObserverOperator");
        Formula primeScale = F.Id("primeScale");
        Formula value = F.Id("value");
        Formula evenChannel = F.Id("evenChannel");
        Formula oddChannel = F.Id("oddChannel");
        Formula identityTwo = Call("identityMatrix", finTwo, complex);
        Formula characterDefinition = Call(
            "cast",
            complex,
            Call("legendreSym", D(5), p));
        Formula localOperatorDefinition = Call("goldenLocalBranchOperator", p);
        Formula primeScaleDefinition = new Formula.Power(
            Call("cast", complex, p),
            Seq(Minus, s));

        Formula EulerDeterminant(Formula scale, Formula op, Formula identity) => Call(
            "det",
            Subtract(identity, Call("smul", scale, op)));
        Formula Inverse(Formula input) => Call("inverse", input);
        Formula OneMinus(Formula input) => Subtract(D(1), input);
        Formula CharacterFactor(Formula scale) =>
            OneMinus(Multiply(chi, scale));

        Formula genericDeterminant = Equal(
            Inverse(EulerDeterminant(x, localOperator, identityTwo)),
            new Formula.Fraction(
                D(1),
                Multiply(OneMinus(x), CharacterFactor(x))));
        Formula specializedDeterminant = Equal(
            Inverse(EulerDeterminant(primeScale, localOperator, identityTwo)),
            Multiply(
                Inverse(OneMinus(primeScale)),
                Inverse(CharacterFactor(primeScale))));
        Formula complementaryChannels = Call("IsCompl", evenChannel, oddChannel);
        Formula evenAction = ForAll(
            [Bound("value", branchSpace)],
            Implies(
                Call("mem", value, evenChannel),
                Equal(Call("mulVec", localOperator, value), value)));
        Formula oddAction = ForAll(
            [Bound("value", branchSpace)],
            Implies(
                Call("mem", value, oddChannel),
                Equal(
                    Call("mulVec", localOperator, value),
                    Call("smul", chi, value))));
        Formula conclusion = All(
            genericDeterminant,
            specializedDeterminant,
            complementaryChannels,
            evenAction,
            oddAction);

        return Disp(ForAll(
            [
                Bound("p", primes),
                Bound("x", complex),
                Bound("s", complex),
            ],
            Seq(
                Let(chi, complex, characterDefinition),
                Let(localOperator, matrixTwo, localOperatorDefinition),
                Let(primeScale, complex, primeScaleDefinition),
                conclusion)));
    }

    private static Formula Let(Formula name, Formula type, Formula value) =>
        Seq(
            Operatorname, Grp(F.Id("let")), Sp,
            name, Colon, Sp, type, Sp, Eq, Sp, value, Comma, Sp);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    private static Formula All(params Formula[] clauses)
    {
        Formula result = clauses[^1];
        for (var index = clauses.Length - 2; index >= 0; index--)
            result = And(clauses[index], result);
        return result;
    }

    private static Formula.BoundVariable Bound(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);

    private static Formula ForAll(
        Formula.BoundVariable[] variables,
        Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
}
