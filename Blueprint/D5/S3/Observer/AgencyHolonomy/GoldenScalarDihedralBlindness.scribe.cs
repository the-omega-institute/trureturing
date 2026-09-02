using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.AgencyHolonomy;

internal sealed class GoldenScalarDihedralBlindnessDocument
    : IScribeDocumentDefinition
{
    private const string Handle =
        "D5/S3/Observer/AgencyHolonomy/GoldenScalarDihedralBlindness.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Golden-unit scalar completion is blind to ordered prime-word dihedral holonomy.",
        H("Golden Scalar Dihedral Blindness"),
        Blocks(Describe.Lean(
            DescribeId.Create("golden-scalar-dihedral-blindness"),
            DeclarationHandle.Create(Handle + "golden_scalar_dihedrally_blind"),
            H("The complete scalar world does not recover dihedral holonomy"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "The rapidity carrier uses Mathlib's infinite dihedral group. "
                        + "Its rotation r(-1) is the positive golden regulator boost, "
                        + "and its reflection sr(0) negates rapidity.")),
                Paragraph(Text(
                    "Each unramified prime contributes the proper boost followed by "
                        + "reflection exactly when its imported golden character is "
                        + "negative. The ordered product is the source prime holonomy.")),
                Paragraph(Text(
                    "The imported lattice-zeta owner supplies reflection and one period. "
                        + "Integral periodicity gives invariance under every dihedral "
                        + "normal form. A split-inert word and its reverse have unequal "
                        + "holonomies but identical complete scalar worlds, ruling out a "
                        + "decoder that recovers every word holonomy."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula integers = F.Seq(F.Mathbb, F.Grp(F.Id("Z")));
        Formula reals = F.Seq(F.Mathbb, F.Grp(F.Id("R")));
        Formula complexes = F.Seq(F.Mathbb, F.Grp(F.Id("C")));
        Formula pair = F.Seq(integers, F.Sp, F.Times, F.Sp, integers);
        Formula dihedral = Call("DihedralGroup", F.D(0));
        Formula prime = Call("UnramifiedPrime");
        Formula wordType = Call("List", prime);
        Formula worldType = Arrow(complexes, complexes);
        Formula a = F.Id("a");
        Formula b = F.Id("b");
        Formula alpha = F.Id("alpha");
        Formula eta = F.Id("eta");
        Formula s = F.Id("s");
        Formula g = F.Id("g");
        Formula word = F.Id("w");
        Formula first = F.Id("w1");
        Formula second = F.Id("w2");
        Formula recover = F.Id("R");
        Formula pairValue = F.Seq(F.Open, a, F.Comma, F.Sp, b, F.Close);
        Formula sigmaPlusAtPair = Call("sigmaPlus", pairValue);
        Formula sigmaMinusAtPair = Call("sigmaMinus", pairValue);
        Formula nonzeroCarrier = F.Seq(
            F.Grp(pair), F.Sp, F.Setminus, F.Sp,
            F.OpenBrace, F.Open, F.D(0), F.Comma, F.Sp, F.D(0), F.Close,
            F.CloseBrace);
        Formula formDefinition = F.Seq(
            Call("exp", eta), F.Sp, F.Times, F.Sp,
            Pow(sigmaPlusAtPair, F.D(2)),
            F.Sp, F.Plus, F.Sp,
            Call("exp", F.Seq(F.Minus, eta)), F.Sp, F.Times, F.Sp,
            Pow(sigmaMinusAtPair, F.D(2)));
        Formula zetaDefinition = F.Seq(
            F.Sum, F.Underscore,
            F.Grp(alpha, F.Sp, F.InMacro, F.Sp, nonzeroCarrier), F.Sp,
            Pow(
                Call("anisotropicForm", eta, alpha),
                F.Seq(F.Minus, s)));

        Formula Holonomy(Formula value) =>
            Call("goldenPrimeHolonomy", value);
        Formula Act(Formula element, Formula rapidity) =>
            Call("act", element, rapidity);
        Formula Zeta(Formula spectral, Formula rapidity) =>
            Call("goldenUnitZeta", spectral, rapidity);
        Formula World(Formula rapidity, Formula value) =>
            Call("completedWorld", rapidity, value);

        Formula completedWorldDefinition = Lambda(
            eta,
            reals,
            Lambda(
                word,
                wordType,
                Lambda(
                    s,
                    complexes,
                    Zeta(s, Act(Holonomy(word), eta)))));
        Formula invariance = ForAll(
            [
                Bound("s", complexes),
                Bound("eta", reals),
                Bound("g", dihedral),
            ],
            Equal(Zeta(s, Act(g, eta)), Zeta(s, eta)));
        Formula decoderRecoversAllWords = Exists(
            [Bound("R", Arrow(worldType, dihedral))],
            ForAll(
                [Bound("w", wordType)],
                Equal(Apply(recover, World(eta, word)), Holonomy(word))));
        Formula noDecoder = ForAll(
            [Bound("eta", reals)],
            new Formula.Not(decoderRecoversAllWords));
        Formula nontrivialHolonomy = Exists(
            [Bound("w1", wordType), Bound("w2", wordType)],
            NotEqual(Holonomy(first), Holonomy(second)));
        Formula sameScalarWorld = ForAll(
            [
                Bound("eta", reals),
                Bound("w1", wordType),
                Bound("w2", wordType),
            ],
            Equal(World(eta, first), World(eta, second)));

        return F.Disp(new Formula.Aligned([
            F.Seq(
                F.Id("sigmaPlus"), F.Colon, F.Sp, pair, F.Sp, F.To, F.Sp,
                reals, F.Comma, F.Sp, sigmaPlusAtPair, F.Sp, F.Colon, F.Eq,
                F.Sp, a, F.Sp, F.Plus, F.Sp, b, F.Sp, F.Times, F.Sp,
                F.Varphi, F.Comma),
            F.Seq(
                F.Id("sigmaMinus"), F.Colon, F.Sp, pair, F.Sp, F.To, F.Sp,
                reals, F.Comma, F.Sp, sigmaMinusAtPair, F.Sp, F.Colon, F.Eq,
                F.Sp, a, F.Sp, F.Plus, F.Sp, b, F.Sp, F.Times, F.Sp,
                F.Psi, F.Comma),
            F.Seq(
                F.Id("anisotropicForm"), F.Colon, F.Sp, reals, F.Sp, F.To,
                F.Sp, pair, F.Sp, F.To, F.Sp, reals, F.Comma, F.Sp,
                Call("anisotropicForm", eta, pairValue), F.Sp, F.Colon,
                F.Eq, F.Sp, formDefinition, F.Comma),
            F.Seq(
                F.Id("goldenUnitZeta"), F.Colon, F.Sp, complexes, F.Sp, F.To,
                F.Sp, reals, F.Sp, F.To, F.Sp, complexes, F.Comma, F.Sp,
                Zeta(s, eta), F.Sp, F.Colon, F.Eq, F.Sp, zetaDefinition,
                F.Comma),
            F.Seq(
                Let(
                    F.Id("completedWorld"),
                    Arrow(reals, Arrow(wordType, worldType)),
                    completedWorldDefinition),
                All(invariance, noDecoder, nontrivialHolonomy, sameScalarWorld),
                F.Dot),
        ]));
    }

    private static Formula Let(Formula name, Formula type, Formula value) =>
        F.Seq(
            F.Operatorname, F.Grp(F.Id("let")), F.Sp,
            name, F.Colon, F.Sp, type, F.Sp, F.Eq, F.Sp, value, F.Comma, F.Sp);

    private static Formula Lambda(Formula name, Formula type, Formula body) =>
        F.Seq(F.Open, name, F.Colon, F.Sp, type, F.Sp, F.Mapsto, F.Sp, body, F.Close);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);

    private static Formula All(params Formula[] clauses)
    {
        Formula result = clauses[^1];
        for (var index = clauses.Length - 2; index >= 0; index--)
        {
            result = And(clauses[index], result);
        }

        return result;
    }

    private static Formula.BoundVariable Bound(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);

    private static Formula ForAll(
        Formula.BoundVariable[] variables,
        Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    private static Formula Exists(
        Formula.BoundVariable[] variables,
        Formula body) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [.. variables], body);

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Pow(Formula value, Formula exponent) =>
        F.Seq(value, F.Caret, F.Grp(exponent));
}
