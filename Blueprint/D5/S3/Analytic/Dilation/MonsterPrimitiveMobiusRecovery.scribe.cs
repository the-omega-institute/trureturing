using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Dilation;

internal sealed class MonsterPrimitiveMobiusRecoveryDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Mobius inversion recovers the full bivariate Monster primitive heat series.",
        H("Monster Primitive Mobius Recovery"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("monster-primitive-mobius-recovery"),
                DeclarationHandle.Create(
                    "D5/S3/Analytic/Dilation/MonsterPrimitiveMobiusRecovery."
                        + "monster_primitive_mobius_recovery"),
                H("Bivariate formal Mobius recovery"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let c be the Monster coefficient function and let D be a bivariate "
                            + "formal power series over the rationals with constant coefficient "
                            + "one. The series H_c has coefficient c(mn) at p^m q^n for positive "
                            + "m and n, and L_D is the formal series -log D.")),
                    Paragraph(Text(
                        "The hypothesis is the full bivariate formal-series identity (126.2), "
                            + "using simultaneous substitution of p^k and q^k. The conclusion is "
                            + "the boxed full-series identity (126.3), not a coefficient-family "
                            + "surrogate.")),
                    Paragraph(Text(
                        "Positive exponent pairs are canonically equivalent to a primitive "
                            + "coprime ray and a positive dilation degree. Pinned Mathlib then "
                            + "supplies scalar divisor-sum Mobius inversion on every ray; formal "
                            + "power-series extensionality reassembles the bivariate equality."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula naturals = F.Seq(F.Mathbb, F.Grp(F.Id("N")));
        Formula integers = F.Seq(F.Mathbb, F.Grp(F.Id("Z")));
        Formula rationals = F.Seq(F.Mathbb, F.Grp(F.Id("Q")));
        Formula p = F.Id("p"), q = F.Id("q");
        Formula m = F.Id("m"), n = F.Id("n"), k = F.Id("k");
        Formula heat = new Formula.Subscript(F.Id("H"), F.Id("c"));
        Formula logarithm = new Formula.Subscript(F.Id("L"), F.Id("D"));
        Formula series = F.Seq(
            rationals,
            F.OpenBracket, F.OpenBracket,
            p, F.Comma, F.Sp, q,
            F.CloseBracket, F.CloseBracket);
        Formula coefficientFunction = new Formula.TypeArrow(naturals, integers);
        Formula normalizedDenominators = F.Seq(
            F.OpenBrace,
            F.Id("F"), F.Sp, F.InMacro, F.Sp, series,
            F.Sp, F.Mid, F.Sp,
            F.OpenBracket, Pow(p, F.D(0)), Pow(q, F.D(0)), F.CloseBracket,
            F.Id("F"), F.Sp, F.Eq, F.Sp, F.D(1),
            F.CloseBrace);

        Formula Equal(Formula left, Formula right) =>
            new Formula.Relation(left, FormulaRelationOperator.Equal, right);
        Formula Multiply(Formula left, Formula right) =>
            new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
        Formula Implies(Formula left, Formula right) =>
            new Formula.Logic(left, FormulaLogicOperator.Implies, right);
        Formula.BoundVariable Bound(string name, Formula domain) =>
            new(FormulaIdentifier.Create(name), domain);

        Formula heatAt(Formula first, Formula second) =>
            new Formula.Apply(heat, [first, second]);
        Formula logarithmAt(Formula first, Formula second) =>
            new Formula.Apply(logarithm, [first, second]);
        Formula heatDefinition = F.Seq(
            F.Sum, F.Underscore,
            F.Grp(m, F.Comma, F.Sp, n, F.Sp, F.Ge, F.Sp, F.D(1)), F.Sp,
            Call("c", F.Seq(m, n)), F.Sp,
            Pow(p, m), F.Sp, Pow(q, n));
        Formula logDefinition = F.Seq(
            F.Minus, F.Log, F.Open, Call("D", p, q), F.Close);
        Formula expansionSum = F.Seq(
            F.Sum, F.Underscore, F.Grp(k, F.Ge, F.D(1)), F.Sp,
            Multiply(new Formula.Fraction(F.D(1), k),
                heatAt(Pow(p, k), Pow(q, k))));
        Formula recoverySum = F.Seq(
            F.Sum, F.Underscore, F.Grp(k, F.Ge, F.D(1)), F.Sp,
            Multiply(
                new Formula.Fraction(F.Seq(F.Mu, F.Open, k, F.Close), k),
                logarithmAt(Pow(p, k), Pow(q, k))));
        Formula expansion = Equal(logarithmAt(p, q), expansionSum);
        Formula recovery = Equal(heatAt(p, q), recoverySum);
        Formula theorem = new Formula.BindMany(
            FormulaQuantifier.ForAll,
            [Bound("c", coefficientFunction), Bound("D", normalizedDenominators)],
            Implies(expansion, recovery));

        return F.Disp(new Formula.Aligned([
            F.Seq(heatAt(p, q), F.Sp, F.Colon, F.Eq, F.Sp, heatDefinition, F.Comma),
            F.Seq(logarithmAt(p, q), F.Sp, F.Colon, F.Eq, F.Sp, logDefinition, F.Comma),
            theorem,
        ]));
    }

    private static Formula Call(string name, params Formula[] arguments)
    {
        var pieces = new List<Formula> { F.Operatorname, F.Grp(F.Id(name)), F.Open };
        for (int index = 0; index < arguments.Length; index++)
        {
            if (index > 0)
            {
                pieces.Add(F.Comma);
                pieces.Add(F.Sp);
            }

            pieces.Add(arguments[index]);
        }

        pieces.Add(F.Close);
        return F.Seq([.. pieces]);
    }

    private static Formula Pow(Formula value, Formula exponent) =>
        F.Seq(value, F.Caret, F.Grp(exponent));
}
