using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.PrimeForms;

internal sealed class ErdosStrausResidueReductionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/PrimeForms/ErdosStrausResidueReduction.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integral and reciprocal formulations connect five explicit families to a reduction modulo twenty-four.",
        H("Erdos--Straus Residue Reduction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("erdos-straus-solvability"),
                DeclarationHandle.Create(Prefix + "ESSolvable"),
                H("Division-free Erdos--Straus solvability"),
                StatementSource.FromAuthor(SolvabilityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "A natural n is solvable when positive natural denominators x, y, and z satisfy the integer equation obtained by clearing denominators."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("integer-reciprocal-scaling"),
                DeclarationHandle.Create(Prefix + "es_integer_reciprocal_scaling"),
                H("Reciprocal equivalence and positive scaling"),
                StatementSource.FromAuthor(IntegerReciprocalScalingFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every natural n, integer solvability is equivalent to the existence of positive natural denominators satisfying the rational reciprocal equation.")),
                    Paragraph(Text(
                        "A solution for n scales to one for nm for every positive natural multiplier m by multiplying all three denominators by m."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("mod-twenty-four-reduction"),
                DeclarationHandle.Create(Prefix + "es_mod_24_reduction"),
                H("Reduction to one residue class modulo twenty-four"),
                StatementSource.FromAuthor(ModTwentyFourReductionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every n at least two, a residue other than one modulo twenty-four is routed through one of the five frozen witness families and is therefore solvable.")),
                    Paragraph(Text(
                        "The second conjunct states that any natural with residue one modulo twenty-four satisfies none of the five family predicates. This theorem does not assert the six-class modulus-840 reduction or the full Erdos--Straus conjecture."))),
                DescribeRole.Theorem))));

    private static Formula SolvabilityFormula()
    {
        Formula n = F.Id("n"); Formula x = F.Id("x");
        Formula y = F.Id("y"); Formula z = F.Id("z");
        return Disp(Seq(
            Forall, Sp, Typed(n, Naturals()), Comma, RowBreak, Grp(),
            Call("ESSolvable", n), Sp, Iff, Sp,
            Exists, Sp, x, Comma, Sp, y, Comma, Sp, z, Sp, InMacro, Sp, Naturals(),
            Comma, RowBreak, Grp(),
            Conjunction(Positive(x), Positive(y), Positive(z), IntegerEquation(n, x, y, z)),
            Dot));
    }

    private static Formula IntegerReciprocalScalingFormula()
    {
        Formula n = F.Id("n"); Formula m = F.Id("m");
        Formula x = F.Id("x"); Formula y = F.Id("y"); Formula z = F.Id("z");
        Formula rationalExistence = Seq(
            Exists, Sp, x, Comma, Sp, y, Comma, Sp, z, Sp, InMacro, Sp, Naturals(),
            Comma, RowBreak, Grp(),
            Conjunction(Positive(x), Positive(y), Positive(z),
                ReciprocalEquation(n, x, y, z)));
        Formula equivalence = Quantified(
            [n], IffFormula(Call("ESSolvable", n), rationalExistence));
        Formula scaling = Quantified(
            [n, m],
            ImpliesFormula(
                Conjunction(Call("ESSolvable", n), LessOrEqual(D(1), m)),
                Call("ESSolvable", Product(n, m))));
        return Disp(Seq(ParenthesizedConjunction(equivalence, scaling), Dot));
    }

    private static Formula ModTwentyFourReductionFormula()
    {
        Formula n = F.Id("n");
        Formula solved = Quantified(
            [n],
            ImpliesFormula(
                Conjunction(LessOrEqual(D(2), n),
                    NotEqual(new Formula.Modulo(n, D(2, 4)), D(1))),
                Call("ESSolvable", n)));
        Formula excluded = Quantified(
            [n],
            ImpliesFormula(
                ResidueEquality(n, D(2, 4), D(1)),
                Seq(Neg, Sp, Parenthesized(Disjunction(
                    Divides(D(2), n),
                    Divides(D(3), n),
                    ResidueEquality(n, D(3), D(2)),
                    ResidueEquality(n, D(4), D(3)),
                    ResidueEquality(n, D(8), D(5)))))));
        return Disp(Seq(ParenthesizedConjunction(solved, excluded), Dot));
    }

    private static Formula ReciprocalEquation(Formula n, Formula x, Formula y, Formula z) =>
        Equal(
            new Formula.Fraction(D(4), n),
            Sum(new Formula.Fraction(D(1), x),
                new Formula.Fraction(D(1), y),
                new Formula.Fraction(D(1), z)));

    private static Formula IntegerEquation(Formula n, Formula x, Formula y, Formula z) =>
        Equal(
            Product(D(4), x, y, z),
            Product(n, Parenthesized(Sum(Product(x, y), Product(x, z), Product(y, z)))));

    private static Formula Quantified(Formula[] variables, Formula conclusion)
    {
        List<Formula> items = [Forall, Sp];
        AddSeparated(items, variables, Comma);
        items.Add(Sp); items.Add(InMacro); items.Add(Sp); items.Add(Naturals());
        items.Add(Comma); items.Add(RowBreak); items.Add(Grp()); items.Add(conclusion);
        return Seq([.. items]);
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        Seq(Operatorname, Grp(F.Id(name)), Open, Joined(arguments, Comma), Close);

    private static Formula Typed(Formula value, Formula type) => Seq(value, Sp, InMacro, Sp, type);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Positive(Formula value) => Seq(D(0), Sp, Lt, Sp, value);
    private static Formula LessOrEqual(Formula left, Formula right) => Seq(left, Sp, Leq, Sp, right);
    private static Formula NotEqual(Formula left, Formula right) => Seq(left, Sp, Neq, Sp, right);
    private static Formula Equal(Formula left, Formula right) => Seq(left, Sp, Eq, Sp, right);
    private static Formula Divides(Formula left, Formula right) => Seq(left, Sp, Mid, Sp, right);
    private static Formula IffFormula(Formula left, Formula right) =>
        Seq(Parenthesized(left), Sp, Leftrightarrow, Sp, Parenthesized(right));
    private static Formula ImpliesFormula(Formula premise, Formula conclusion) =>
        Seq(Parenthesized(premise), Sp, Rightarrow, RowBreak, Grp(), Parenthesized(conclusion));
    private static Formula ResidueEquality(Formula value, Formula modulus, Formula residue) =>
        Equal(new Formula.Modulo(value, modulus), residue);
    private static Formula Conjunction(Formula first, params Formula[] rest) =>
        Joined([first, .. rest], Land);
    private static Formula ParenthesizedConjunction(Formula first, params Formula[] rest) =>
        Joined([Parenthesized(first), .. rest.Select(Parenthesized)], Land);
    private static Formula Disjunction(Formula first, params Formula[] rest) =>
        Joined([first, .. rest], Lor);
    private static Formula Product(Formula first, params Formula[] rest) =>
        Joined([first, .. rest], Cdot);
    private static Formula Sum(Formula first, params Formula[] rest) =>
        Joined([first, .. rest], Plus);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Joined(Formula[] values, Formula separator)
    {
        List<Formula> items = [];
        AddSeparated(items, values, separator);
        return Seq([.. items]);
    }

    private static void AddSeparated(List<Formula> items, Formula[] values, Formula separator)
    {
        for (int index = 0; index < values.Length; index++)
        {
            if (index > 0) { items.Add(Sp); items.Add(separator); items.Add(Sp); }
            items.Add(values[index]);
        }
    }
}
