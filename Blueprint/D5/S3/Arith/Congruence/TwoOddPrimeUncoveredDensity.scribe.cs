using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Congruence;

internal sealed class TwoOddPrimeUncoveredDensityDocument : IScribeDocumentDefinition
{
    private const string DeclarationPrefix =
        "D5/S3/Arith/Congruence/TwoOddPrimeUncoveredDensity.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Congruence classes with distinct nontrivial moduli supported on two odd primes "
            + "leave a positive density of residue classes uncovered.",
        H("Two-Odd-Prime Uncovered Density"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("two-odd-prime-uncovered-density"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "two_odd_prime_uncovered_density"),
                H("At least one eighth of the residues remain uncovered"),
                StatementSource.FromAuthor(DensityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let p and q be distinct odd primes and let L = p^A q^B, with A and B "
                            + "arbitrary natural numbers, including zero. A finite set D records "
                            + "distinct moduli. If every d in D is greater than one and divides L, "
                            + "then every assignment a of residue representatives leaves at least "
                            + "one eighth of Fin L uncovered.")),
                    Paragraph(Text(
                        "Here mod denotes natural-number remainder, val is the coercion from Fin L "
                            + "to its natural representative, and card counts the displayed finite "
                            + "set. The proof counts one residue fibre exactly as L/d, bounds the "
                            + "finite union of covered fibres, identifies the ambient reciprocal "
                            + "sum with the divisor sum with d = 1 removed, and proves "
                            + "8 sigma(L) <= 15L from two finite geometric estimates.")),
                    Paragraph(Text(
                        "The reciprocal-sum necessary condition is classical covering-system "
                            + "folklore: the reciprocal sum of covering moduli is at least one. "
                            + "The quantified two-odd-prime form proved here is repository-derived. "
                            + "Hough and Nielsen (2019), Covering systems with restricted "
                            + "divisibility, and Balister, Bollobas, Morris, Sahasrabudhe and "
                            + "Tiba (2022), On the Erdos Covering Problem: the density of the "
                            + "uncovered set, provide background on odd covering systems; "
                            + "neither is cited as attesting the displayed two-prime L/8 bound.")),
                    Paragraph(Text(
                        "This is a periphery result for Erdos problem 7. It excludes modulus "
                            + "families supported on at most two odd primes; it does not resolve "
                            + "the open problem for arbitrary distinct odd moduli."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("two-odd-prime-residue-classes-do-not-cover"),
                DeclarationHandle.Create(
                    DeclarationPrefix + "two_odd_prime_residue_classes_do_not_cover"),
                H("The residue classes cannot cover the complete period"),
                StatementSource.FromAuthor(NoCoverFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Under the same prime, exponent, modulus, and residue hypotheses, it is "
                            + "not the case that every element of Fin(p^A q^B) belongs to one of "
                            + "the selected congruence classes. This is the named bind-only "
                            + "companion directed from the no-cover consequence to the preceding "
                            + "density theorem. This consequence is repository-derived from "
                            + "that theorem; the literature above supplies background only."))),
                DescribeRole.Proposition))));

    private static Formula DensityFormula()
    {
        Formula p = F.Id("p");
        Formula q = F.Id("q");
        Formula aExponent = F.Id("A");
        Formula bExponent = F.Id("B");
        Formula moduli = F.Id("D");
        Formula residues = F.Id("a");
        Formula divisor = F.Id("d");
        Formula point = F.Id("x");
        Formula period = Product(Power(p, aExponent), Power(q, bExponent));
        Formula primeHypotheses = Conjunction(
            Call("Prime", p),
            Call("Prime", q),
            Call("Odd", p),
            Call("Odd", q),
            NotEqual(p, q));
        Formula modulusHypothesis = ForAll(
            [Bound("d", Naturals())],
            Implies(
                Member(divisor, moduli),
                Conjunction(Less(D(1), divisor), Divides(divisor, period))));
        Formula uncoveredPredicate = ForAll(
            [Bound("d", Naturals())],
            Implies(
                Member(divisor, moduli),
                NotEqual(
                    Remainder(Call("val", point), divisor),
                    Remainder(Call("a", divisor), divisor))));
        Formula uncovered = SetBuilder(
            point, Call("Fin", period), uncoveredPredicate);
        Formula conclusion = LessOrEqual(
            period,
            Product(D(8), Call("card", uncovered)));

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, p, Comma, Sp, q, Sp, InMacro, Sp, Naturals(), Comma),
            Seq(
                Parenthesized(primeHypotheses), Sp, Rightarrow),
            Seq(
                Forall, Sp, aExponent, Comma, Sp, bExponent, Sp, InMacro, Sp,
                Naturals(), Comma, Sp, moduli, Sp, InMacro, Sp,
                Call("Finset", Naturals()), Comma),
            Seq(
                Forall, Sp, residues, Colon, Sp,
                Arrow(Naturals(), Naturals()), Comma),
            Seq(
                Parenthesized(modulusHypothesis), Sp, Rightarrow),
            Seq(conclusion, Dot),
        ]));
    }

    private static Formula NoCoverFormula()
    {
        Formula p = F.Id("p");
        Formula q = F.Id("q");
        Formula aExponent = F.Id("A");
        Formula bExponent = F.Id("B");
        Formula moduli = F.Id("D");
        Formula residues = F.Id("a");
        Formula divisor = F.Id("d");
        Formula point = F.Id("x");
        Formula period = Product(Power(p, aExponent), Power(q, bExponent));
        Formula primeHypotheses = Conjunction(
            Call("Prime", p),
            Call("Prime", q),
            Call("Odd", p),
            Call("Odd", q),
            NotEqual(p, q));
        Formula modulusHypothesis = ForAll(
            [Bound("d", Naturals())],
            Implies(
                Member(divisor, moduli),
                Conjunction(Less(D(1), divisor), Divides(divisor, period))));
        Formula coveredAtPoint = ExistsMany(
            [Bound("d", Naturals())],
            Conjunction(
                Member(divisor, moduli),
                Equal(
                    Remainder(Call("val", point), divisor),
                    Remainder(Call("a", divisor), divisor))));
        Formula completeCover = ForAll(
            [Bound("x", Call("Fin", period))],
            coveredAtPoint);

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, p, Comma, Sp, q, Sp, InMacro, Sp, Naturals(), Comma),
            Seq(
                Parenthesized(primeHypotheses), Sp, Rightarrow),
            Seq(
                Forall, Sp, aExponent, Comma, Sp, bExponent, Sp, InMacro, Sp,
                Naturals(), Comma, Sp, moduli, Sp, InMacro, Sp,
                Call("Finset", Naturals()), Comma),
            Seq(
                Forall, Sp, residues, Colon, Sp,
                Arrow(Naturals(), Naturals()), Comma),
            Seq(
                Parenthesized(modulusHypothesis), Sp, Rightarrow),
            Seq(Neg, Sp, Parenthesized(completeCover), Dot),
        ]));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula ForAll(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    private static Formula ExistsMany(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [.. variables], body);

    private static Formula Relation(
        Formula left, FormulaRelationOperator relation, Formula right) =>
        new Formula.Relation(left, relation, right);

    private static Formula Equal(Formula left, Formula right) =>
        Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula NotEqual(Formula left, Formula right) =>
        Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula Less(Formula left, Formula right) =>
        Relation(left, FormulaRelationOperator.LessThan, right);

    private static Formula LessOrEqual(Formula left, Formula right) =>
        Relation(left, FormulaRelationOperator.LessThanOrEqual, right);

    private static Formula Divides(Formula left, Formula right) =>
        Relation(left, FormulaRelationOperator.Divides, right);

    private static Formula Member(Formula value, Formula set) =>
        Relation(value, FormulaRelationOperator.MemberOf, set);

    private static Formula Conjunction(Formula first, params Formula[] rest)
    {
        Formula result = first;
        foreach (Formula item in rest)
        {
            result = new Formula.Logic(result, FormulaLogicOperator.And, item);
        }

        return result;
    }

    private static Formula Implies(Formula premise, Formula conclusion) =>
        new Formula.Logic(premise, FormulaLogicOperator.Implies, conclusion);

    private static Formula Product(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Power(Formula value, Formula exponent) =>
        new Formula.Power(value, exponent);

    private static Formula Remainder(Formula value, Formula modulus) =>
        new Formula.Modulo(value, modulus);

    private static Formula SetBuilder(
        Formula variable, Formula domain, Formula predicate) =>
        Seq(
            OpenBrace, variable, Colon, Sp, domain, Sp, Mid, Sp,
            predicate, CloseBrace);

    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(domain, codomain);

    private static Formula Parenthesized(Formula value) =>
        Seq(Open, value, Close);

    private static Formula Naturals() =>
        Seq(Mathbb, Grp(F.Id("N")));
}
