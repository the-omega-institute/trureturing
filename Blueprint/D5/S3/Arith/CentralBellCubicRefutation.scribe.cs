using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith;

internal sealed class CentralBellCubicRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/CentralBellCubicRefutation.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Rational double-root certificates refute the two distinct-root claims for the printed "
            + "n = 3, lambda = 3 central Bell cosine cubics.",
        H("Central Bell Cubic Refutations"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("euler-cubic"),
                DeclarationHandle.Create(Prefix + "eulerCubic"),
                H("Expanded Euler-type cubic"),
                StatementSource.FromAuthor(CubicDefinition(true)),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "This repository definition transcribes the printed n = 3, lambda = 3 Euler-type "
                        + "cosine cubic, with all three arguments and its value in the complex numbers. "
                        + "Khan et al., Networks and Heterogeneous Media 21(2) (2026), 693-724, "
                        + "DOI 10.3934/nhm.2026030, Conjecture 3, is the claim in scope; the paper "
                        + "is not cited as proving the refutation below."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("bernoulli-cubic"),
                DeclarationHandle.Create(Prefix + "bernoulliCubic"),
                H("Expanded Bernoulli-type cubic"),
                StatementSource.FromAuthor(CubicDefinition(false)),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "This repository definition transcribes the printed n = 3, lambda = 3 "
                        + "Bernoulli-type cosine cubic, with all arguments and its value complex. "
                        + "Conjecture 1 of the same paper is the claim in scope. The definition "
                        + "uses the printed expansion; its factorization is derived in the proof."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("three-distinct-roots"),
                DeclarationHandle.Create(Prefix + "HasThreeDistinctRoots"),
                H("Three pairwise distinct complex zeros"),
                StatementSource.FromAuthor(DistinctRootsDefinition()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The predicate asks for three zeros and all three pairwise inequalities. "
                        + "It counts distinct complex solutions, not algebraic multiplicities. "
                        + "Both refutation theorems use this predicate."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("finite-egf-jet"),
                DeclarationHandle.Create(Prefix + "egfJet"),
                H("Finite generating-function jet"),
                StatementSource.FromAuthor(JetDefinition()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The product is a polynomial over the complex numbers. C denotes Polynomial.C "
                        + "and X denotes Polynomial.X. It records the four finite jets, including "
                        + "the central Bell z/24 contribution, without asserting an infinite-series identity."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("euler-egf-coefficient"),
                DeclarationHandle.Create(Prefix + "euler_egf_coefficient"),
                H("Euler coefficient identity"),
                StatementSource.FromAuthor(CoefficientFormula(true)),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Six times the degree-three coefficient with prefactor parameter 3/8 is the "
                        + "printed Euler cubic. coeff denotes Polynomial.coeff."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("bernoulli-egf-coefficient"),
                DeclarationHandle.Create(Prefix + "bernoulli_egf_coefficient"),
                H("Bernoulli coefficient identity"),
                StatementSource.FromAuthor(CoefficientFormula(false)),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Six times the degree-three coefficient with prefactor parameter 1/8 is the "
                        + "printed Bernoulli cubic."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("euler-coefficient-bridge"),
                DeclarationHandle.Create(Prefix + "euler_coefficient_bridge"),
                H("Shifted Euler identity"),
                StatementSource.FromAuthor(ShiftedFormula(true)),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The shift x+z isolates the Euler quadratic parameter y squared plus 3/4."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("bernoulli-coefficient-bridge"),
                DeclarationHandle.Create(Prefix + "bernoulli_coefficient_bridge"),
                H("Shifted Bernoulli identity"),
                StatementSource.FromAuthor(ShiftedFormula(false)),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The shift x+z isolates the Bernoulli quadratic parameter y squared plus 1/4."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("euler-factorization"),
                DeclarationHandle.Create(Prefix + "euler_factorization"),
                H("Euler rational factorization"),
                StatementSource.FromAuthor(FactorizationFormula(true)),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At the rational parameters 1/2 and 8, the repeated factor is x+7."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("bernoulli-factorization"),
                DeclarationHandle.Create(Prefix + "bernoulli_factorization"),
                H("Bernoulli rational factorization"),
                StatementSource.FromAuthor(FactorizationFormula(false)),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "At the rational parameters 2/3 and 125/27, the repeated factor is x+205/54."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("bernoulli-parameter-identities"),
                DeclarationHandle.Create(Prefix + "bernoulli_parameter_identities"),
                H("Bernoulli rational parameter identities"),
                StatementSource.FromAuthor(Disp(And(
                    Equal(Add(Pow(Parenthesized(Div(D(2), D(3))), 2), Div(D(1), D(4))),
                        Pow(Parenthesized(Div(D(5), D(6))), 2)),
                    Equal(Div(Div(D(1, 2, 5), D(2, 7)), D(4)),
                        Mul(D(2), Pow(Parenthesized(Div(D(5), D(6))), 3)))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Both equalities hold in the rationals and exhibit the parameter 5/6 "
                        + "in the Bernoulli double-root certificate."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("conjecture-three-refuted"),
                DeclarationHandle.Create(Prefix + "conjecture3_refuted"),
                H("Euler rational double-root refutation"),
                StatementSource.FromAuthor(RefutationFormula(true)),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For the printed n = 3, lambda = 3 cubics, the Euler parameters y = 1/2 "
                            + "and z = 8 are rational and the entire complex zero set is {-7,-10}. "
                            + "These roots are unequal, so there are exactly two distinct solutions "
                            + "and there cannot be three. The last conjunct refutes the universal "
                            + "real-parameter reading of Conjecture 3 at this degree and lambda. "
                            + "It also refutes any universal-lambda reading that includes 3.")),
                    Paragraph(Text(
                        "In both refutation formulas, val denotes Rat.cast : Rat -> Real and "
                            + "ofReal denotes Complex.ofReal : Real -> Complex. Thus the nested coercions in the rational "
                            + "witness and the single coercions in the universal clause are explicit. "
                            + "Every displayed division is field division.")),
                    Paragraph(Text(
                        "Provenance correction: the atom bracket's lambda=1 is an orchestrator typo "
                            + "corrected by PZG remark 27.844 / PR #5820. This module refutes the paper's "
                            + "printed n = 3, lambda = 3 cubics; the existing 4.105 and 4.106 atoms "
                            + "remain the coverage targets.")),
                    Paragraph(Text(
                        "The live proof extracts six times the degree-three coefficient of the "
                            + "finite generating-function jet with Euler prefactor 1-3t^2/8. It "
                            + "identifies the result with the expanded cubic, rewrites it as "
                            + "(x+z)^3-3(x+z)(y^2+3/4)+z/4, and proves the factorization "
                            + "(x+7)^2(x+10). Product-zero reasoning gives the complete root set. "
                            + "The finite-jet coefficient identity is kernel checked; an identity "
                            + "with the full infinite generating function is not asserted."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("conjecture-one-refuted"),
                DeclarationHandle.Create(Prefix + "conjecture1_refuted"),
                H("Bernoulli rational double-root refutation"),
                StatementSource.FromAuthor(RefutationFormula(false)),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For the printed n = 3, lambda = 3 cubics, the Bernoulli parameters "
                            + "y = 2/3 and z = 125/27 are rational and the entire complex zero set "
                            + "is {-205/54,-170/27}. The inequality of these two roots and the "
                            + "absence of three distinct roots are both explicit. The last conjunct "
                            + "refutes the universal real-parameter reading of Conjecture 1 at "
                            + "this degree and lambda, hence any universal-lambda reading including 3.")),
                    Paragraph(Text(
                        "The finite-jet prefactor is 1-t^2/8. The coefficient bridge gives "
                            + "(x+z)^3-3(x+z)(y^2+1/4)+z/4. Exact rational arithmetic then yields "
                            + "(x+205/54)^2(x+170/27), and the proof determines all complex zeros "
                            + "before excluding three pairwise distinct ones. As for the Euler "
                            + "case, the kernel statement concerns the printed cubic and the "
                            + "finite coefficient computation, not an infinite-series theorem."))),
                DescribeRole.Theorem))));

    private static Formula JetDefinition()
    {
        Formula q = F.Id("q");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula z = F.Id("z");
        Formula variable = F.Id("X");
        Formula prefactor = Sub(D(1), Mul(Call("C", q), Pow(variable, 2)));
        Formula exponential = Add(Add(Add(D(1), Mul(Call("C", x), variable)),
            Mul(Call("C", Div(Pow(x, 2), D(2))), Pow(variable, 2))),
            Mul(Call("C", Div(Pow(x, 3), D(6))), Pow(variable, 3)));
        Formula cosine = Sub(D(1), Mul(Call("C", Div(Pow(y, 2), D(2))), Pow(variable, 2)));
        Formula bell = Add(Add(Add(D(1), Mul(Call("C", z), variable)),
            Mul(Call("C", Div(Pow(z, 2), D(2))), Pow(variable, 2))),
            Mul(Call("C", Add(Div(Pow(z, 3), D(6)), Div(z, D(2, 4)))), Pow(variable, 3)));
        Formula product = Mul(Mul(Mul(Parenthesized(prefactor), Parenthesized(exponential)),
            Parenthesized(cosine)), Parenthesized(bell));
        return Disp(All([Bound("q", Complexes()), Bound("x", Complexes()),
            Bound("y", Complexes()), Bound("z", Complexes())],
            Equal(Call("egfJet", q, x, y, z), product)));
    }

    private static Formula CoefficientFormula(bool euler)
    {
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula z = F.Id("z");
        Formula q = Div(D(euler ? (byte)3 : (byte)1), D(8));
        return Disp(All([Bound("x", Complexes()), Bound("y", Complexes()),
            Bound("z", Complexes())], Equal(Mul(D(6),
                Call("coeff", Call("egfJet", q, x, y, z), D(3))),
                Call(CubicName(euler), x, y, z))));
    }

    private static Formula ShiftedFormula(bool euler)
    {
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula z = F.Id("z");
        Formula c = Div(D(euler ? (byte)3 : (byte)1), D(4));
        return Disp(All([Bound("x", Complexes()), Bound("y", Complexes()),
            Bound("z", Complexes())], Equal(Call(CubicName(euler), x, y, z),
                Add(Sub(Pow(Parenthesized(Add(x, z)), 3),
                    Mul(Mul(D(3), Parenthesized(Add(x, z))),
                        Parenthesized(Add(Pow(y, 2), c)))), Div(z, D(4))))));
    }

    private static Formula FactorizationFormula(bool euler)
    {
        Formula x = F.Id("x");
        Formula yValue = euler ? Div(D(1), D(2)) : Div(D(2), D(3));
        Formula zValue = euler ? D(8) : Div(D(1, 2, 5), D(2, 7));
        Formula firstOffset = euler ? D(7) : Div(D(2, 0, 5), D(5, 4));
        Formula secondOffset = euler ? D(1, 0) : Div(D(1, 7, 0), D(2, 7));
        return Disp(All([Bound("x", Complexes())],
            Equal(Call(CubicName(euler), x, yValue, zValue),
                Mul(Pow(Parenthesized(Add(x, firstOffset)), 2),
                    Parenthesized(Add(x, secondOffset))))));
    }

    private static Formula CubicDefinition(bool euler)
    {
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula z = F.Id("z");
        Formula linear = new Formula.Negate(Div(Mul(D(euler ? (byte)9 : (byte)3), x), D(4)));
        Formula value = Add(linear, Pow(x, 3));
        value = Sub(value, Mul(Mul(D(3), x), Pow(y, 2)));
        value = Sub(value, euler ? Mul(D(2), z) : Div(z, D(2)));
        value = Add(value, Mul(Mul(D(3), Pow(x, 2)), z));
        value = Sub(value, Mul(Mul(D(3), Pow(y, 2)), z));
        value = Add(value, Mul(Mul(D(3), x), Pow(z, 2)));
        value = Add(value, Pow(z, 3));
        return Disp(All([Bound("x", Complexes()), Bound("y", Complexes()),
            Bound("z", Complexes())], Equal(Call(CubicName(euler), x, y, z), value)));
    }

    private static Formula DistinctRootsDefinition()
    {
        Formula a = F.Id("a");
        Formula b = F.Id("b");
        Formula c = F.Id("c");
        Formula body = And(Equal(Call("f", a), D(0)), Equal(Call("f", b), D(0)),
            Equal(Call("f", c), D(0)), NotEqual(a, b), NotEqual(a, c), NotEqual(b, c));
        Formula exists = Some([Bound("a", Complexes()), Bound("b", Complexes()),
            Bound("c", Complexes())], body);
        return Disp(All([Bound("f", new Formula.TypeArrow(Complexes(), Complexes()))],
            new Formula.Logic(Call("HasThreeDistinctRoots", F.Id("f")),
                FormulaLogicOperator.Iff, Parenthesized(exists))));
    }

    private static Formula RefutationFormula(bool euler)
    {
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula z = F.Id("z");
        Formula yValue = euler ? Div(D(1), D(2)) : Div(D(2), D(3));
        Formula zValue = euler ? D(8) : Div(D(1, 2, 5), D(2, 7));
        Formula firstRoot = new Formula.Negate(euler ? D(7) : Div(D(2, 0, 5), D(5, 4)));
        Formula secondRoot = new Formula.Negate(euler ? D(1, 0) : Div(D(1, 7, 0), D(2, 7)));
        Formula rationalValue = Call(CubicName(euler), x,
            Call("ofReal", Call("val", y)), Call("ofReal", Call("val", z)));
        Formula realValue = Call(CubicName(euler), x, Call("ofReal", y), Call("ofReal", z));
        Formula roots = All([Bound("x", Complexes())],
            new Formula.Logic(Equal(rationalValue, D(0)), FormulaLogicOperator.Iff,
                Parenthesized(new Formula.Logic(Equal(x, firstRoot),
                    FormulaLogicOperator.Or, Equal(x, secondRoot)))));
        Formula witness = Some([Bound("y", Rationals()), Bound("z", Rationals())],
            And(Equal(y, yValue), Equal(z, zValue), Parenthesized(roots),
                NoThree(rationalValue)));
        Formula universal = All([Bound("y", Reals()), Bound("z", Reals())],
            Call("HasThreeDistinctRoots", LambdaX(realValue)));
        return Disp(And(Parenthesized(witness), NotEqual(firstRoot, secondRoot),
            new Formula.Not(Parenthesized(universal))));
    }

    private static Formula NoThree(Formula value) =>
        new Formula.Not(Call("HasThreeDistinctRoots", LambdaX(value)));

    private static Formula LambdaX(Formula value) =>
        Seq(F.Id("x"), Sp, Mapsto, Sp, value);

    private static string CubicName(bool euler) => euler ? "eulerCubic" : "bernoulliCubic";

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);

    private static Formula.BoundVariable Bound(string name, Formula domain) =>
        new(FormulaIdentifier.Create(name), domain);

    private static Formula All(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);

    private static Formula Some(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [.. variables], body);

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);

    private static Formula And(Formula first, params Formula[] rest)
    {
        Formula result = first;
        foreach (Formula item in rest)
        {
            result = new Formula.Logic(result, FormulaLogicOperator.And, item);
        }
        return result;
    }

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Sub(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);

    private static Formula Mul(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Div(Formula numerator, Formula denominator) =>
        new Formula.Fraction(numerator, denominator);

    private static Formula Pow(Formula value, byte exponent) => new Formula.Power(value, D(exponent));

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Rationals() => Seq(Mathbb, Grp(F.Id("Q")));
}
