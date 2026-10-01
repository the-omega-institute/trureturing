using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.CellularAutomata;

internal sealed class TernaryDensityClassificationRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/CellularAutomata/TernaryDensityClassificationRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/StatisticalMechanics/fuks2019ternary");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The ternary cellular automaton with Wolfram number 6478767664173 sends the configuration 210 of length 3 to 111, which it and the rule 7580606234490 both fix, although 210 contains a zero and has density 1/2. This refutes Conjecture 1 of H. Fukś and R. Procyk (arXiv:2002.08924), which asserts that this pair of rules classifies by density every finite configuration containing a zero.",
        H("A misclassified configuration for a ternary two-rule density classifier"),
        Blocks(
            Node("wolfram", "The local rule of a Wolfram number", WolframFormula(),
                "A ternary nearest-neighbour local rule is a map from {0,1,2}^3 to {0,1,2}. The rule with Wolfram number N has f(a,b,c) equal to the base-3 digit of N at the position 9a + 3b + c, that is, the integer part of N divided by 3^(9a+3b+c), reduced modulo 3; the paper indexes the coefficients as a_(9x_0+3x_1+x_2) = f(x_0,x_1,x_2). Here a, b, c lie in Fin 3, the division is division of natural numbers with remainder discarded, and the result is the element of Fin 3 with that value.",
                "wolfram", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("rulef", "The rule F", RuleFormula("ruleF", D(6, 4, 7, 8, 7, 6, 7, 6, 6, 4, 1, 7, 3)),
                "F is the rule with Wolfram number 6478767664173; it conserves the number of each value weighted by the value, and its restriction to the values 1 and 2 is elementary rule 184.",
                "ruleF", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("ruleg", "The rule G", RuleFormula("ruleG", D(7, 5, 8, 0, 6, 0, 6, 2, 3, 4, 4, 9, 0)),
                "G is the rule with Wolfram number 7580606234490.",
                "ruleG", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("step", "The global map on periodic configurations", StepFormula(),
                "A configuration of length L is a map x from ZMod L to Fin 3, so that indices are taken modulo L. The global map of a local rule f sends x to the configuration whose value at i is f(x(i - 1), x(i), x(i + 1)).",
                "step", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("rho", "The density", RhoFormula(),
                "For L different from 0 (NeZero L), the density of x is the rational number (1/2L) times the sum over i in ZMod L of the values x(i), read as natural numbers.",
                "rho", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("claim", "Conjecture 1", ClaimFormula(),
                "Conjecture 1 of the paper: for every length L (with NeZero L) and every configuration x of length L containing at least one zero, G^L F^L(x) is the constant configuration 0 if the density lies in [0, 2/3), the constant 1 if it lies in (2/3, 3/4), and the constant 2 if it lies in (3/4, 1). In the formula the exponent [L] denotes the L-fold iterate of the global map, and (i -> c) is the constant configuration c.",
                "claim", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The configuration 210", Disp(new Formula.Not(F.Id("claim"))),
                "Take L = 3 and x = (2, 1, 0), which contains a zero and has density 3/6 = 1/2, in [0, 2/3). Decoding the Wolfram number of F gives F(0,2,1) = F(2,1,0) = F(1,0,2) = 1, so the global map of F sends x to (1, 1, 1). Both rules send (1, 1, 1) to itself, since F(1,1,1) = G(1,1,1) = 1, so G^3 F^3(x) = (1, 1, 1) and not the constant 0 that the conjecture predicts. The iterates are evaluated by decide and the density by norm_num.",
                "result", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("fuks-2019-ternary-density-classification"),
                    ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create("ternarydcp-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Named(Formula name) => Seq(Operatorname, Grp(name));
    private static Formula Call(Formula name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Rel(Formula left, FormulaRelationOperator op, Formula right) =>
        new Formula.Relation(left, op, right);
    private static Formula Equal(Formula left, Formula right) =>
        Rel(left, FormulaRelationOperator.Equal, right);
    private static Formula Member(Formula left, Formula right) =>
        Rel(left, FormulaRelationOperator.MemberOf, right);
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, right);
    private static Formula AllIn(Formula variable, Formula domain, Formula body) =>
        Seq(Forall, Sp, variable, Sp, InMacro, Sp, domain, Comma, Sp, body);
    private static Formula Plus(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Minus(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Times(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Ternary() => Call(F.Id("Fin"), D(3));
    private static Formula Configurations() =>
        Seq(Call(F.Id("ZMod"), F.Id("L")), Sp, To, Sp, Ternary());
    private static Formula At(Formula x, Formula i) => new Formula.Apply(x, [i]);
    private static Formula Run(Formula x)
    {
        Formula l = F.Id("L");
        Formula iterate(string rule) =>
            new Formula.Power(Call(F.Id("step"), Named(F.Id(rule))), Seq(OpenBracket, l, CloseBracket));
        return new Formula.Apply(iterate("ruleG"), [new Formula.Apply(iterate("ruleF"), [x])]);
    }
    private static Formula Constant(byte c) =>
        Seq(Open, F.Id("i"), Sp, Mapsto, Sp, D(c), Close);

    private static Formula WolframFormula()
    {
        Formula n = F.Id("N"), a = F.Id("a"), b = F.Id("b"), c = F.Id("c");
        Formula position = Plus(Plus(Times(D(9), a), Times(D(3), b)), c);
        Formula quotient = new Formula.Floor(new Formula.Fraction(n, new Formula.Power(D(3), position)));
        return Disp(Equal(Call(F.Id("wolfram"), n, a, b, c),
            Seq(quotient, Sp, Named(F.Id("mod")), Sp, D(3))));
    }

    private static Formula RuleFormula(string name, Formula number) =>
        Disp(Equal(Named(F.Id(name)), Call(F.Id("wolfram"), number)));

    private static Formula StepFormula()
    {
        Formula x = F.Id("x"), i = F.Id("i"), f = F.Id("f");
        Formula lhs = At(Call(F.Id("step"), f, x), i);
        Formula rhs = new Formula.Apply(f,
            [At(x, Minus(i, D(1))), At(x, i), At(x, Plus(i, D(1)))]);
        return Disp(Equal(lhs, rhs));
    }

    private static Formula RhoFormula()
    {
        Formula x = F.Id("x"), i = F.Id("i");
        Formula sum = Seq(F.Sum, Underscore, Grp(i), Sp, At(x, i));
        return Disp(Equal(Call(F.Id("rho"), x),
            new Formula.Fraction(sum, Times(D(2), F.Id("L")))));
    }

    private static Formula ClaimFormula()
    {
        Formula l = F.Id("L"), x = F.Id("x"), i = F.Id("i");
        Formula rho = Call(F.Id("rho"), x);
        Formula hasZero = Seq(Exists, Sp, i, Comma, Sp, Equal(At(x, i), D(0)));
        Formula case0 = Implies(
            Member(rho, Seq(OpenBracket, D(0), Comma, Sp, new Formula.Fraction(D(2), D(3)), Close)),
            Equal(Run(x), Constant(0)));
        Formula case1 = Implies(
            Member(rho, Seq(Open, new Formula.Fraction(D(2), D(3)), Comma, Sp,
                new Formula.Fraction(D(3), D(4)), Close)),
            Equal(Run(x), Constant(1)));
        Formula case2 = Implies(
            Member(rho, Seq(Open, new Formula.Fraction(D(3), D(4)), Comma, Sp, D(1), Close)),
            Equal(Run(x), Constant(2)));
        Formula conclusion = And(case0, And(case1, case2));
        Formula body = AllIn(l, Seq(Mathbb, Grp(F.Id("N"))),
            Seq(l, Sp, Neq, Sp, D(0), Sp, Rightarrow, Sp,
                AllIn(x, Configurations(), Implies(hasZero, conclusion))));
        return Disp(Iff(F.Id("claim"), body));
    }
}
