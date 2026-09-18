using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates;

internal sealed class BradshawConjectureTwentyRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S0/Certificates/BradshawConjectureTwentyRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/bradshaw2025collatz");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "At a = 17, b = 7, the nonsquarefree input 125 satisfies Bradshaw's commutation equation.",
        H("Bradshaw's Conjecture 20 is false"),
        Blocks(
            Node("arithmetic-derivative", "The arithmetic derivative",
                DerivativeFormula(),
                DerivativeProse(),
                "IsArithmeticDerivative", DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node("generalized-collatz", "The generalized Collatz map",
                CollatzFormula(),
                CollatzProse(),
                "C", DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node("conjecture-twenty", "Conjecture 20 on positive inputs",
                ClaimFormula(),
                ClaimProse(),
                "claim", DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node("conjecture-twenty-refuted", "A nonsquarefree commuting input",
                Disp(new Formula.Not(F.Id("claim"))),
                "An arithmetic derivative exists: for each n, sum k times NatDiv(n,p) "
                    + "over its prime factorization, where k is the multiplicity of p. "
                    + "The empty factorizations at zero and one give zero; prime factorization "
                    + "of a product gives the product rule, with zero factors treated separately. "
                    + "For every derivative satisfying the four properties, the prime values "
                    + "and product rule give D(25) = 10, D(125) = 75, D(533) = 54 and "
                    + "D(1066) = 641. These values follow from the properties alone. "
                    + "At a = 17, b = 7, C(17,7,125) = 1066 and C(17,7,75) = 641. "
                    + "Thus both sides of the commutation equation equal 641, although "
                    + "125 = 5³ is divisible by 5² and is not squarefree.",
                "result", DescribeRole.Theorem,
                AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create(
                        "bradshaw-arithmetic-derivative-collatz-squarefree-refutation"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Node(
        string id, string title, Formula formula, string prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Node(id, title, formula, Blocks(Paragraph(Text(prose))), declaration, role, provenance,
            resolution);

    private static DocumentBlock Node(
        string id, string title, Formula formula, BlockSequence prose,
        string declaration, DescribeRole role, AssessedProvenance provenance,
        OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(formula), provenance,
            prose, role, resolution);

    private static BlockSequence DerivativeProse() => Blocks(
        Paragraph(
            Text("Bradshaw, printed page 3: \"We define the arithmetic derivative to be a "
                + "non-linear derivation "),
            Math(Seq(F.Id("D"), Sp, Colon, Sp, DerivativeType())),
            Text(" on the set of natural numbers with the property that "),
            Math(new Formula.RelationChain(FormulaRelationOperator.Equal,
                [SourceD(D(1)), SourceD(D(0)), D(0)])),
            Text(" and "), Math(Equal(SourceD(F.Id("p")), D(1))),
            Text(" for all primes "), Math(F.Id("p")),
            Text(". Explicitly, we define "), Math(F.Id("D")), Text(" so that "),
            Math(Equal(SourceD(Seq(F.Id("m"), F.Id("n"))),
                Seq(SourceD(F.Id("m")), F.Id("n"), Plus,
                    F.Id("m"), SourceD(F.Id("n"))))),
            Text(" (1) for every "),
            Math(Seq(F.Id("m"), Comma, Sp, F.Id("n"), Sp, InMacro, Sp, Naturals())),
            Text(".\"")),
        Paragraph(Text(
            "The predicate records the four properties in the order D(0) = 0, D(1) = 0, "
                + "prime values, and the product rule. All inputs and values are natural "
                + "numbers, including zero; Prime denotes Nat.Prime.")));

    private static BlockSequence CollatzProse() => Blocks(
        Paragraph(
            Text("Bradshaw, printed page 16: \"It should also be noted that similar problems "
                + "can be formulated for the generalized Collatz functions "),
            Math(SourceCollatzFormula()), Text(" with "), Math(SourceParity()), Text(".\"")),
        Paragraph(Text(
            "The encoding C(a,b,n) uses exactly these two branches. NatDiv(x,y) is "
                + "natural-number integer division, and NatMod(x,y) is the natural remainder. "
                + "The expression ite(P,x,y) chooses x when P holds and y otherwise. For natural "
                + "n, NatMod(n,2) = 1 means n is odd, and the other branch means n is even. "
                + "The map is defined for all natural a,b,n; the claim imposes equal parity "
                + "on a and b, so the fractions in the source quotation have exact integral "
                + "values on their respective branches. The formal definition displayed "
                + "above uses NatDiv for both quotients.")));

    private static BlockSequence ClaimProse() => Blocks(
        Paragraph(
            Text("Bradshaw, Conjecture 20, printed page 16: \"The solutions to the commutation "
                + "problem "),
            Math(Equal(SourceD(SourceC(F.Id("n"))), SourceC(SourceD(F.Id("n"))))),
            Text(" are squarefree for every "), Math(SourceParity()), Text(".\"")),
        Paragraph(Text(
            "The encoding quantifies over D : Nat to Nat satisfying all four defining "
                + "properties and over natural a,b,n. Equal remainders modulo two encode "
                + "the stated parity condition; Squarefree is Mathlib's predicate on natural "
                + "numbers. The extra hypothesis 1 ≤ n makes claim weaker than the source "
                + "statement, so refuting it refutes the source, and excludes the trivial "
                + "n = 0 boundary. The intended domain of (a,b) is read as naturals of equal "
                + "parity; the counterexample has a,b positive and odd with b < a, as in "
                + "the source's five tested pairs.")));

    private static Formula SourceD(Formula argument) =>
        Seq(F.Id("D"), Parenthesized(argument));

    private static Formula SourceC(Formula argument) =>
        Seq(new Formula.Subscript(F.Id("C"), Seq(F.Id("a"), Comma, F.Id("b"))),
            Parenthesized(argument));

    private static Formula SourceParity() =>
        Seq(F.Id("a"), Sp, Equiv, Sp, F.Id("b"), Sp,
            Parenthesized(Seq(Mathrm, Grp(F.Id("mod")), Sp, D(2))));

    // Fractions here reproduce the source quotation; the Lean mirror uses NatDiv below.
    private static Formula SourceCollatzFormula() =>
        Seq(SourceC(F.Id("n")), Sp, Colon, Eq, Sp,
            Begin, Grp(F.Id("cases")),
            Call("NatDiv", Add(Multiply(F.Id("a"), F.Id("n")), F.Id("b")), D(2)),
            Comma, Amp, F.Text, Grp(Seq(F.Id("if"), Sp)), F.Id("n"),
            F.Text, Grp(Seq(Sp, F.Id("odd"))), Semi, RowBreak,
            Call("NatDiv", F.Id("n"), D(2)),
            Comma, Amp, F.Text, Grp(Seq(F.Id("if"), Sp)), F.Id("n"),
            F.Text, Grp(Seq(Sp, F.Id("even"))), Comma,
            End, Grp(F.Id("cases")));

    private static Formula DerivativeFormula()
    {
        var derivative = F.Id("D");
        var p = F.Id("p");
        var m = F.Id("m");
        var n = F.Id("n");
        var primeValues = Universal("p", Naturals(),
            Logic(Call("Prime", p), FormulaLogicOperator.Implies,
                Equal(Call("D", p), D(1))));
        var productRule = Universal("m", Naturals(), Universal("n", Naturals(),
            Equal(Call("D", Multiply(m, n)),
                Add(Multiply(Call("D", m), n), Multiply(m, Call("D", n))))));
        var properties = Logic(Equal(Call("D", D(0)), D(0)), FormulaLogicOperator.And,
            Logic(Equal(Call("D", D(1)), D(0)), FormulaLogicOperator.And,
                Logic(primeValues, FormulaLogicOperator.And, productRule)));
        return Disp(Universal("D", Parenthesized(DerivativeType()),
            Logic(Call("IsArithmeticDerivative", derivative), FormulaLogicOperator.Iff,
                properties)));
    }

    private static Formula CollatzFormula()
    {
        var a = F.Id("a");
        var b = F.Id("b");
        var n = F.Id("n");
        var branches = Call("ite", Equal(Call("NatMod", n, D(2)), D(1)),
            Call("NatDiv", Add(Multiply(a, n), b), D(2)), Call("NatDiv", n, D(2)));
        return Disp(Universal("a", Naturals(), Universal("b", Naturals(),
            Universal("n", Naturals(), Equal(Call("C", a, b, n), branches)))));
    }

    private static Formula ClaimFormula()
    {
        var a = F.Id("a");
        var b = F.Id("b");
        var n = F.Id("n");
        var parity = Equal(Call("NatMod", a, D(2)), Call("NatMod", b, D(2)));
        var positive = new Formula.Relation(D(1), FormulaRelationOperator.LessThanOrEqual, n);
        var commutes = Equal(Call("D", Call("C", a, b, n)),
            Call("C", a, b, Call("D", n)));
        var assertion = Universal("D", Parenthesized(DerivativeType()),
            Logic(Call("IsArithmeticDerivative", F.Id("D")), FormulaLogicOperator.Implies,
                Universal("a", Naturals(), Universal("b", Naturals(), Universal("n", Naturals(),
                    Logic(parity, FormulaLogicOperator.Implies,
                        Logic(positive, FormulaLogicOperator.Implies,
                            Logic(commutes, FormulaLogicOperator.Implies,
                                Call("Squarefree", n)))))))));
        return Disp(Logic(F.Id("claim"), FormulaLogicOperator.Iff, assertion));
    }

    private static Formula Universal(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), domain, body);

    private static Formula Logic(Formula left, FormulaLogicOperator op, Formula right) =>
        new Formula.Logic(Parenthesized(left), op, Parenthesized(right));

    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);

    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula Naturals() =>
        Seq(Mathbb, Grp(F.Id("N")));

    private static Formula DerivativeType() => new Formula.TypeArrow(Naturals(), Naturals());

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
}
