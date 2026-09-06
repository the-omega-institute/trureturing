using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.PatternAvoidance;

internal sealed class RotationSumPowerPatternAvoidanceDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/PatternAvoidance/RotationSumPowerPatternAvoidance.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Powers of direct sums of cyclic rotations admit an exact 2143-avoidance criterion.",
        H("Rotation-Sum Power Pattern Avoidance"),
        Blocks(
            Node(
                "rotation-sum-permutation",
                "rotationSumPerm",
                "Direct sum of cyclic rotations",
                RotationSumPermFormula(),
                "For a list d of block sizes, e is the canonical finSigmaFinEquiv "
                    + "flattening from block-tagged positions to the finite interval. "
                    + "The subscript displays its two implicit Mathlib parameters. "
                    + "The defining expression conjugates sigmaCongrRight of the "
                    + "rotations finRotate(d_i) by e, hence is the direct sum of the "
                    + "rotations epsilon_(d_i) on Fin(sum_i d_i). "
                    + "In the displayed defining formula, mod is natural-number remainder "
                    + "and finRotate(m) is the atom rotation epsilon_m.",
                DescribeRole.Definition,
                RotationFormula()),
            Node(
                "contains-pattern-2143",
                "Contains2143",
                "Containment of the pattern 2143",
                Contains2143Formula(),
                "The six displayed inequalities are the defining expression: four "
                    + "increasing positions whose values have relative order 2143.",
                DescribeRole.Definition),
            Node(
                "rotation-sum-power-avoids-2143-iff",
                "rotationSumPerm_pow_avoids_2143_iff",
                "All-power 2143-avoidance criterion",
                PowerCriterionFormula(F.Id("r")),
                "Every block has positive size. The powered direct sum avoids 2143 "
                    + "exactly when at most one index has block size not dividing r. "
                    + "The proof uses the unique cyclic cut in each block: one block "
                    + "cannot contain both required descents, while any two nonidentity "
                    + "blocks supply them. This repository theorem resolves the "
                    + "all-power criterion motivated by Archer and Bourne's 2143 conjecture. "
                    + "The conjecture and the proved avoider-composition bijection are due to "
                    + "Archer and Bourne (2026), arXiv:2505.05218, DOI 10.46298/dmtcs.17199. "
                    + "The counting equality follows only by combining the cube criterion with "
                    + "that paper's proved bijection. This module does not formalize the bijection "
                    + "or the counting equality; the counting bridge remains residual-open.",
                DescribeRole.Theorem),
            Node(
                "rotation-sum-cube-avoids-2143-iff",
                "rotationSumPerm_cube_avoids_2143_iff",
                "Cube 2143-avoidance criterion",
                CubeCriterionFormula(),
                "At exponent three, a positive block size divides the exponent exactly "
                    + "when it is one or three. This is the composition condition in the "
                    + "Archer-Bourne conjecture. The conjecture and the proved avoider-composition "
                    + "bijection are due to Archer and Bourne (2026), arXiv:2505.05218, "
                    + "DOI 10.46298/dmtcs.17199. The counting equality follows only by combining "
                    + "the cube criterion with that paper's proved bijection. This module does "
                    + "not formalize the bijection or the counting equality; the counting bridge "
                    + "remains residual-open.",
                DescribeRole.Theorem))));

    private static DocumentBlock.Describe Node(
        string id,
        string declaration,
        string title,
        Formula statement,
        string explanation,
        DescribeRole role,
        Formula? definingExpression = null) =>
        Describe.Lean(
            DescribeId.Create(id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.FromAuthor(statement),
            AssessedProvenance.FromRepo(),
            definingExpression is null
                ? Blocks(Paragraph(Text(explanation)))
                : Blocks(Paragraph(Text(explanation)), new DocumentBlock.DisplayFormula(definingExpression)),
            role);

    private static Formula RotationSumPermFormula()
    {
        Formula d = F.Id("d");
        Formula i = F.Id("i");
        Formula flattening = new Formula.Subscript(F.Id("finSigmaFinEquiv"), Seq(
            Call("length", d), Comma, Sp,
            Parenthesized(Seq(i, Colon, Sp, FinIndices(d), Sp, Mapsto, Sp, Part(d, i)))));
        Formula taggedRotation = Call("sigmaCongrRight", Seq(
            i, Sp, Mapsto, Sp, Call("finRotate", Part(d, i))));
        Formula conjugate = Seq(
            flattening, Sp, Circ, Sp, taggedRotation, Sp, Circ, Sp,
            Call("symm", flattening));

        return Disp(Seq(
            Forall, Sp, d, Colon, Sp, Call("List", Naturals()), Comma, Sp,
            Call("rotationSumPerm", d), Colon, Sp,
            Call("Perm", Call("Fin", SumParts(d, i))), Sp,
            Colon, Eq, Sp, conjugate, Dot));
    }

    private static Formula RotationFormula()
    {
        Formula m = F.Id("m");
        Formula x = F.Id("x");
        return Disp(Seq(
            Forall, Sp, m, Colon, Sp, Naturals(), Comma, Sp,
            Forall, Sp, x, Colon, Sp, Call("Fin", m), Comma, Sp,
            Equal(Call("val", Apply(Call("finRotate", m), x)),
                new Formula.Modulo(Add(Call("val", x), D(1)), m)), Dot));
    }

    private static Formula Contains2143Formula()
    {
        Formula n = F.Id("n");
        Formula f = F.Id("f");
        Formula a = F.Id("a");
        Formula b = F.Id("b");
        Formula c = F.Id("c");
        Formula e = F.Id("e");
        Formula domain = Call("Fin", n);
        Formula inequalities = Seq(
            a, Sp, Lt, Sp, b, Sp, Land, Sp,
            b, Sp, Lt, Sp, c, Sp, Land, Sp,
            c, Sp, Lt, Sp, e, Sp, Land, Sp,
            Apply(f, b), Sp, Lt, Sp, Apply(f, a), Sp, Land, Sp,
            Apply(f, a), Sp, Lt, Sp, Apply(f, e), Sp, Land, Sp,
            Apply(f, e), Sp, Lt, Sp, Apply(f, c));

        return Disp(Seq(
            Forall, Sp, n, Colon, Sp, Naturals(), Comma, Sp,
            Forall, Sp, f, Colon, Sp, domain, Sp, To, Sp, domain, Comma, Sp,
            Call("Contains2143", f), Sp, Iff, Sp,
            Exists, Sp, a, Comma, Sp, b, Comma, Sp, c, Comma, Sp, e,
            Colon, Sp, domain, Comma, Sp,
            Parenthesized(inequalities), Dot));
    }

    private static Formula PowerCriterionFormula(Formula exponent)
    {
        Formula d = F.Id("d");
        Formula r = exponent;
        Formula i = F.Id("i");
        Formula positiveParts = Seq(
            Forall, Sp, i, Colon, Sp, FinIndices(d), Comma, Sp,
            D(0), Sp, Lt, Sp, Part(d, i));
        Formula avoidance = Seq(
            Neg, Sp, Call("Contains2143",
                new Formula.Power(Call("rotationSumPerm", d), r)));
        Formula exceptional = Seq(
            OpenBrace, i, Sp, InMacro, Sp, FinIndices(d), Sp, Colon, Sp,
            Neg, Sp, Part(d, i), Sp, Mid, Sp, r, CloseBrace);
        Formula bound = Seq(Call("card", exceptional), Sp, Leq, Sp, D(1));

        return Disp(Seq(
            Forall, Sp, d, Colon, Sp, Call("List", Naturals()), Comma, Sp,
            Forall, Sp, r, Colon, Sp, Naturals(), Comma, Sp,
            Parenthesized(positiveParts), Sp, Implies, Sp,
            Parenthesized(Seq(
                Parenthesized(avoidance), Sp, Leftrightarrow, Sp,
                Parenthesized(bound))), Dot));
    }

    private static Formula CubeCriterionFormula()
    {
        Formula d = F.Id("d");
        Formula i = F.Id("i");
        Formula positiveParts = Seq(
            Forall, Sp, i, Colon, Sp, FinIndices(d), Comma, Sp,
            D(0), Sp, Lt, Sp, Part(d, i));
        Formula avoidance = Seq(
            Neg, Sp, Call("Contains2143",
                new Formula.Power(Call("rotationSumPerm", d), D(3))));
        Formula exceptional = Seq(
            OpenBrace, i, Sp, InMacro, Sp, FinIndices(d), Sp, Colon, Sp,
            Part(d, i), Sp, Neq, Sp, D(1), Sp, Land, Sp,
            Part(d, i), Sp, Neq, Sp, D(3), CloseBrace);
        Formula bound = Seq(Call("card", exceptional), Sp, Leq, Sp, D(1));

        return Disp(Seq(
            Forall, Sp, d, Colon, Sp, Call("List", Naturals()), Comma, Sp,
            Parenthesized(positiveParts), Sp, Implies, Sp,
            Parenthesized(Seq(
                Parenthesized(avoidance), Sp, Leftrightarrow, Sp,
                Parenthesized(bound))), Dot));
    }

    private static Formula SumParts(Formula d, Formula i) => Seq(
        new Formula.Subscript(Sum, Seq(i, Sp, InMacro, Sp, FinIndices(d))), Sp,
        Part(d, i));

    private static Formula FinIndices(Formula d) =>
        Call("Fin", Call("length", d));

    private static Formula Part(Formula d, Formula i) =>
        new Formula.Subscript(d, Call("val", i));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Parenthesized(Formula value) =>
        Seq(Open, value, Close);

    private static Formula Naturals() =>
        Seq(Mathbb, Grp(F.Id("N")));
}
