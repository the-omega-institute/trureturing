using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.StatisticalMechanics.CellularAutomata;

internal sealed class Diploid10245DensityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/StatisticalMechanics/CellularAutomata/Diploid10245Density.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/StatisticalMechanics/fuksfates2026diploid");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For every mixing parameter in [0,1], diploid rule 10-245 has density 1/4 + λ/2 at every time from one onwards, starting from the fair Bernoulli cylinder law.",
        H("Exact density of diploid rule 10-245"), Blocks(
            Node("rule10", "Elementary rule 10", "rule10", Rule10Formula(),
                "For an ordered left, centre and right neighbourhood, rule 10 returns true exactly when the left spin is false and the right spin is true. The centre spin does not affect the output. Thus the neighbourhoods 001 and 011 give one, as in the rule 10-245 table of §3.2.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("rule245", "Elementary rule 245", "rule245", Rule245Formula(),
                "Rule 245 complements the output of rule 10. It returns zero on 001 and 011 and one on the other six neighbourhoods, giving the complementary rule in §3.2.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("p", "Conditional probability of a one", "p", ProbabilityFormula(),
                "Equation (2) weights rule 10 by 1−λ and rule 245 by λ. In the order 000, 001, 010, 011, 100, 101, 110, 111, the probability of a one is λ, 1−λ, λ, 1−λ, λ, λ, λ, λ, exactly the table in §3.2. The formula defines a real-valued function for every real λ; probability laws below restrict λ to [0,1].",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("w", "The binary update kernel", "w", KernelFormula(),
                "The conditional probability in Eq. (1) is p for output true and 1−p for output false. For a fixed parent configuration, the cells use independent fresh choices of rule.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("evolve", "Evolution of finite cylinders", "evolve", EvolutionFormula(),
                "A real cylinder family assigns a weight to every Boolean word of each length. To update a word of length n, sum over all parent words of length n+2, multiplying their weights by the n conditional update factors. The three Fin embeddings have values j, j+1 and j+2, so the two exterior parents are included without periodic indexing. This defines the cylinder evolution for the lattice process of §2, Eq. (1).",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("hierarchy", "The Bernoulli cylinder hierarchy", "P", HierarchyFormula(),
                "Nat.rec starts at the fair Bernoulli weight (1/2)^n for each word of length n, the symmetric Bernoulli initial condition of §2. Its successor branch applies evolve to the preceding cylinder family. The denominator two is first a natural number and then cast to the real numbers. The hierarchy includes every finite word length and every natural time.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("d", "The density at a given time", "d", DensityFormula(),
                "The density is the weight of the singleton cylinder whose spin is true. This is the expected spin value P_t(1) in §2, Eq. (3); it is an expectation, rather than a statement about the density along an individual realization.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("cylinder-law", "Consistent finite probability laws", "CylinderLaw", CylinderLawFormula(),
                "At every time, each cylinder weight is nonnegative and the weights at each length sum to one. Summing over a new spin on either the right, using Fin.snoc, or the left, using Fin.cons, recovers the shorter cylinder weight. These are finite cylinder laws; no separate infinite-product probability space is part of this definition.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("claim", "The exact-density proposition", "claim", ClaimFormula(),
                "Section 5 asks whether the asymptotic density 1/4 + λ/2 is exact for rule 10-245. This proposition strengthens that question: for every λ in the closed interval [0,1], the hierarchy satisfies CylinderLaw and the density equals 1/4 + λ/2 for every time t≥1. That identity implies the limit asked in §5, which is also stated explicitly. Both denominators are real casts of natural numerals.",
                DescribeRole.Definition, AssessedProvenance.FromRepo(Source)),
            Node("result", "Exact density from time one", "result", Local("claim"),
                "The proposition holds for the cylinder hierarchy of Fukś–Fatès's rule 10-245, including λ=0 and λ=1. Summing out the independent output spins preserves both endpoint marginals, normalization and nonnegativity. The probability of a zero followed by a one at distance two stays equal to 1/4: its update is λ(1−λ) plus (1−2λ)^2 times its previous value, because the overlapping contributions vanish when a shared spin would have to be both zero and one. The next density is λ plus (1−2λ) times that distance-two probability, hence 1/4 + λ/2. Constancy from time one gives the stated limit. Constant density does not assert that the full cylinder family is stationary.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source))
        )));

    private static DocumentBlock Node(string id, string title, string declaration, Formula formula,
        string prose, DescribeRole role, AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), role,
            declaration == "result" ? new OpenProblemResolutionClaim(
                ProblemSlugRef.Create("fuks-fates-2026-diploid-10-245-density"),
                ResolutionKind.Proved) : null);

    private static Formula Rule10Formula() => Neighbourhood(
        Equal(LocalCall("rule10", X("x"), X("y"), X("z")),
            At(Qualified("Bool", "and"), At(Qualified("Bool", "not"), X("x")), X("z"))));

    private static Formula Rule245Formula() => Neighbourhood(
        Equal(LocalCall("rule245", X("x"), X("y"), X("z")),
            At(Qualified("Bool", "not"), LocalCall("rule10", X("x"), X("y"), X("z")))));

    private static Formula ProbabilityFormula() => All("lam", Reals(), Neighbourhood(
        Equal(LocalCall("p", X("lam"), X("x"), X("y"), X("z")),
            Add(Multiply(Parenthesized(Subtract(D(1), X("lam"))),
                    RealNatural(At(Qualified("Bool", "toNat"),
                        LocalCall("rule10", X("x"), X("y"), X("z"))))),
                Multiply(X("lam"),
                    RealNatural(At(Qualified("Bool", "toNat"),
                        LocalCall("rule245", X("x"), X("y"), X("z")))))))));

    private static Formula KernelFormula() => All("lam", Reals(), All("b", Booleans(),
        Neighbourhood(Equal(LocalCall("w", X("lam"), X("b"), X("x"), X("y"), X("z")),
            At(Qualified("ite"), Equal(X("b"), Qualified("Bool", "true")),
                LocalCall("p", X("lam"), X("x"), X("y"), X("z")),
                Subtract(D(1), LocalCall("p", X("lam"), X("x"), X("y"), X("z"))))))));

    private static Formula EvolutionFormula()
    {
        Formula left = At(Qualified("Fin", "castSucc"), At(Qualified("Fin", "castSucc"), X("j")));
        Formula centre = At(Qualified("Fin", "castSucc"), At(Qualified("Fin", "succ"), X("j")));
        Formula right = At(Qualified("Fin", "succ"), At(Qualified("Fin", "succ"), X("j")));
        Formula updates = ProductOver("j", FinOf(X("n")),
            LocalCall("w", X("lam"), At(X("b"), X("j")),
                At(X("a"), left), At(X("a"), centre), At(X("a"), right)));
        Formula evolved = SumOver("a", Word(Add(X("n"), D(2))),
            Multiply(Parenthesized(updates), At(X("R"), Add(X("n"), D(2)), X("a"))));
        return All("lam", Reals(), All("R", CylinderFamily(), All("n", Naturals(),
            All("b", Word(X("n")),
                Equal(LocalCall("evolve", X("lam"), X("R"), X("n"), X("b")), evolved)))));
    }

    private static Formula HierarchyFormula()
    {
        Formula motive = Seq(X("motive"), Sp, Colon, Eq, Sp,
            LambdaIgnored(Naturals(), CylinderFamily()));
        Formula initial = LambdaOf("n", Naturals(), LambdaIgnored(Word(X("n")),
            new Formula.Power(Parenthesized(Fraction(D(1), RealNatural(D(2)))), X("n"))));
        Formula successor = LambdaIgnored(Naturals(), LambdaOf("R", CylinderFamily(),
            LocalCall("evolve", X("lam"), X("R"))));
        return All("lam", Reals(), Equal(LocalCall("P", X("lam")),
            At(Qualified("Nat", "rec"), motive, initial, successor)));
    }

    private static Formula DensityFormula() => All("lam", Reals(), All("t", Naturals(),
        Equal(LocalCall("d", X("lam"), X("t")),
            LocalCall("P", X("lam"), X("t"), D(1),
                LambdaIgnored(FinOf(D(1)), Qualified("Bool", "true"))))));

    private static Formula CylinderLawFormula()
    {
        Formula nonnegative = All("t", Naturals(), All("n", Naturals(), All("b", Word(X("n")),
            LE(D(0), LocalCall("P", X("lam"), X("t"), X("n"), X("b"))))));
        Formula normalized = All("t", Naturals(), All("n", Naturals(),
            Equal(SumOver("b", Word(X("n")),
                LocalCall("P", X("lam"), X("t"), X("n"), X("b"))), D(1))));
        Formula right = All("t", Naturals(), All("n", Naturals(), All("b", Word(X("n")),
            Equal(SumOver("c", Booleans(), LocalCall("P", X("lam"), X("t"), Add(X("n"), D(1)),
                    At(Qualified("Fin", "snoc"), X("b"), X("c")))),
                LocalCall("P", X("lam"), X("t"), X("n"), X("b"))))));
        Formula left = All("t", Naturals(), All("n", Naturals(), All("b", Word(X("n")),
            Equal(SumOver("c", Booleans(), LocalCall("P", X("lam"), X("t"), Add(X("n"), D(1)),
                    At(Qualified("Fin", "cons"), X("c"), X("b")))),
                LocalCall("P", X("lam"), X("t"), X("n"), X("b"))))));
        return All("lam", Reals(), Equivalence(LocalCall("CylinderLaw", X("lam")),
            And(nonnegative, And(normalized, And(right, left)))));
    }

    private static Formula ClaimFormula()
    {
        Formula density = All("t", Naturals(), Implication(LE(D(1), X("t")),
            Equal(LocalCall("d", X("lam"), X("t")), Add(Fraction(D(1), RealNatural(D(4))),
                Fraction(X("lam"), RealNatural(D(2)))))));
        Formula limit = At(Qualified("Filter", "Tendsto"),
            LambdaOf("t", Naturals(), LocalCall("d", X("lam"), X("t"))),
            Qualified("Filter", "atTop"), At(Qualified("nhds"),
                Add(Fraction(D(1), RealNatural(D(4))), Fraction(X("lam"), RealNatural(D(2))))));
        return Equivalence(Local("claim"), All("lam", Reals(),
            Implication(Member(X("lam"), At(Qualified("Set", "Icc"), Typed(D(0), Reals()), D(1))),
                And(LocalCall("CylinderLaw", X("lam")), And(density, limit)))));
    }

    private static Formula X(string name) => F.Id(name);
    private static Formula Qualified(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(X(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula Local(string name) =>
        Qualified("D5", "S3", "StatisticalMechanics", "CellularAutomata", "Diploid10245Density", name);
    private static Formula LocalCall(string name, params Formula[] args) => At(Local(name), args);
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Naturals() => Seq(Mathbb, Grp(X("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(X("R")));
    private static Formula Booleans() => Qualified("Bool");
    private static Formula FinOf(Formula n) => At(Qualified("Fin"), n);
    private static Formula Word(Formula n) => Parenthesized(new Formula.TypeArrow(FinOf(n), Booleans()));
    private static Formula CylinderFamily() => Parenthesized(new Formula.TypeArrow(Typed(X("n"), Naturals()),
        new Formula.TypeArrow(Word(X("n")), Reals())));
    private static Formula RealNatural(Formula numeral) => Typed(Typed(numeral, Naturals()), Reals());
    private static Formula Neighbourhood(Formula body) =>
        All("x", Booleans(), All("y", Booleans(), All("z", Booleans(), body)));
    private static Formula All(string variable, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), type, body);
    private static Formula LambdaOf(string variable, Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(X(variable), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula LambdaIgnored(Formula type, Formula body) =>
        Seq(LambdaLower, Sp, Typed(new Formula.Placeholder(), type), Sp, Mapsto, Sp, Parenthesized(body));
    private static Formula SumOver(string variable, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Typed(X(variable), type)), Sp, Parenthesized(body));
    private static Formula ProductOver(string variable, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Prod, Typed(X(variable), type)), Sp, Parenthesized(body));
    private static Formula Fraction(Formula numerator, Formula denominator) => new Formula.Fraction(numerator, denominator);
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Multiply(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula LE(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Member(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Implication(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Equivalence(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
}
