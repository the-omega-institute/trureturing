using System.Collections.Immutable;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class StephanOddPartPowerDifferenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/StephanOddPartPowerDifference.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Arith/stephan2010a181666");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Stephan's odd-part power characterization is equivalent to the A023758 difference form.",
        H("Stephan's A181666 Odd-Part Characterization"),
        Blocks(
            Paragraph(Text(
                "All variables are natural numbers, including zero. The named operator "
                    + "ordCompl[2] is Mathlib's 2-adic odd complement: it removes the full "
                    + "power of two from its argument, so ordCompl[2] n is the odd part of n. "
                    + "The displayed equations use natural-number addition, multiplication and "
                    + "powers only; no natural-number quotient is hidden in either predicate.")),
            Describe.Lean(
                DescribeId.Create("a181666-in-a181666"),
                DeclarationHandle.Create(Prefix + "InA181666"),
                H("Membership in A181666"),
                StatementSource.FromAuthor(InA181666Formula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The predicate records exactly the OEIS name for A181666: the odd part "
                        + "of n has the form (4^k - 1)/3 for a positive exponent. It is written "
                        + "as 3 times the odd part plus one equals 4^k, which is an equivalent "
                        + "division-free expression over the natural numbers."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("a181666-is-a023758-div-three"),
                DeclarationHandle.Create(Prefix + "IsA023758DivThree"),
                H("The A023758 quotient predicate"),
                StatementSource.FromAuthor(IsA023758DivThreeFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The predicate describes a positive difference of powers of two divided "
                        + "by three without using natural subtraction: j is strictly below i "
                        + "and 3n plus 2^j equals 2^i. The strict inequality excludes the zero "
                        + "difference that would arise from i = j."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("a181666-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The two descriptions are equivalent"),
                StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For every n at least one, the two predicates are equivalent. From an "
                        + "odd-part witness k, the 2-adic exponent j of n and the exponent "
                        + "j + 2k give the required difference of powers. Conversely, a pair "
                        + "i > j with 3n + 2^j = 2^i has an even gap by reducing the equality "
                        + "modulo three; divisibility by three then isolates an odd quotient. "
                        + "The odd-complement decomposition recovers that quotient and the "
                        + "same exponent k. The positive-index hypothesis aligns the theorem "
                        + "with the source sequences, while the proof itself also makes both "
                        + "predicates false at n = 0."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("oeis-a181666-stephan-odd-part-power-difference"),
                    ResolutionKind.Proved)))));

    private static Formula InA181666Formula()
    {
        Formula n = F.Id("n");
        Formula k = F.Id("k");
        Formula oddPart = OrdCompl(n);
        Formula body = Exists("k", Nat(), And(
            LessEqual(D(1), k),
            Equal(Add(Mul(D(3), oddPart), D(1)), Power(D(4), k))));
        return Disp(ForAll("n", Equal(Call("InA181666", n), body)));
    }

    private static Formula IsA023758DivThreeFormula()
    {
        Formula n = F.Id("n");
        Formula i = F.Id("i");
        Formula j = F.Id("j");
        Formula body = ExistsMany(
            [new Formula.BoundVariable(FormulaIdentifier.Create("i"), Nat()),
             new Formula.BoundVariable(FormulaIdentifier.Create("j"), Nat())],
            And(
                Less(j, i),
                Equal(Add(Mul(D(3), n), Power(D(2), j)), Power(D(2), i))));
        return Disp(ForAll("n", Equal(Call("IsA023758DivThree", n), body)));
    }

    private static Formula ResultFormula()
    {
        Formula n = F.Id("n");
        Formula equivalence = new Formula.Logic(
            Parenthesized(Exists("k", Nat(), And(
                LessEqual(D(1), F.Id("k")),
                Equal(Add(Mul(D(3), OrdCompl(n)), D(1)), Power(D(4), F.Id("k")))))),
            FormulaLogicOperator.Iff,
            Parenthesized(ExistsMany(
                [new Formula.BoundVariable(FormulaIdentifier.Create("i"), Nat()),
                 new Formula.BoundVariable(FormulaIdentifier.Create("j"), Nat())],
                And(
                    Less(F.Id("j"), F.Id("i")),
                    Equal(Add(Mul(D(3), n), Power(D(2), F.Id("j"))),
                        Power(D(2), F.Id("i")))))));
        Formula hypothesis = LessEqual(D(1), n);
        return Disp(ForAll("n", new Formula.Logic(
            Parenthesized(hypothesis), FormulaLogicOperator.Implies,
            Parenthesized(equivalence))));
    }

    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula Call(string name, Formula argument) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [argument]);

    private static Formula OrdCompl(Formula n) =>
        new Formula.Apply(new Formula.Subscript(
            Seq(Operatorname, Grp(F.Id("ordCompl"))), D(2)), [n]);

    private static Formula Exists(string name, Formula type, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.Exists,
            [new Formula.BoundVariable(FormulaIdentifier.Create(name), type)], body);

    private static Formula ExistsMany(
        ImmutableArray<Formula.BoundVariable> variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.Exists, variables, body);

    private static Formula ForAll(string name, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create(name), Nat())], body);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Equal(Formula left, Formula right) =>
        Seq(left, Sp, Eq, Sp, right);

    private static Formula Less(Formula left, Formula right) =>
        Seq(left, Sp, Lt, Sp, right);

    private static Formula LessEqual(Formula left, Formula right) =>
        Seq(left, Sp, Le, Sp, right);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Power(Formula value, Formula exponent) =>
        new Formula.Power(value, exponent);

    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
}
