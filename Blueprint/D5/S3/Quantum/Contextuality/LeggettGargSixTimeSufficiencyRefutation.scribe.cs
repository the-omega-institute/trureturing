using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Contextuality;

internal sealed class LeggettGargSixTimeSufficiencyRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Contextuality/LeggettGargSixTimeSufficiencyRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Observer/halliwellmawby2019finentimes");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Six-time pair probabilities satisfy the polygon and three-time inequalities without admitting a joint distribution.",
        H("Polygon and three-time inequalities are insufficient"),
        Blocks(
            Definition("pair-tables", "PairTables", "Real pair tables", PairTablesFormula(),
                "For a natural number n, PairTables n is the type of real arrays indexed by two times "
                    + "and two Boolean outcomes. The sign of true is 1 and the sign of false is -1, "
                    + "using the real-valued function sgn. Only entries with i < j constrain the "
                    + "probability conditions below; the array also assigns values to the other entries. "
                    + "The dichotomic pairwise setting is described in the source's TeX lines 148-159."),
            Definition("pair-family", "IsPairFamily", "Compatible pair probabilities", IsPairFamilyFormula(),
                "Each table at i < j has nonnegative entries summing to one. A single family m of "
                    + "one-time marginals gives both the row and column sums of every such table, "
                    + "so shared times have the same marginal in all pairs. This expresses the "
                    + "compatibility condition in TeX lines 150-153 and the nonnegative pairwise "
                    + "probabilities assumed in Section 4.B, line 551. There is no condition on i >= j."),
            Definition("correlation", "corr", "The pair correlation", CorrFormula(),
                "The real correlation is the sum of the product of the two signs weighted by their "
                    + "pair-table entry. This is the correlator in TeX lines 155-159. The definition "
                    + "applies to every pair of indices, including those outside i < j."),
            Definition("polygon-inequalities", "NGonInequalities", "The n-gon inequalities", NGonFormula(),
                "For every Boolean sign assignment s, the signed sum of pair correlations obeys "
                    + "the polygon bound of Section 4.A, equation (neweq), TeX lines 494-512. "
                    + "The lower bound is one for odd n and zero for even n. The natural number n "
                    + "is cast to a real number in the right-hand side. The double sum includes "
                    + "exactly the terms with i < j."),
            Definition("three-time-lg", "ThreeTimeLG", "All three-time Leggett-Garg inequalities", ThreeTimeFormula(),
                "Every ordered triple of distinct times i < j < k satisfies the three-time "
                    + "inequality for every choice of Boolean outcomes a, b and c. This is equation "
                    + "(LGcomp) in Section 4.B, TeX lines 554-559, with signs represented by sgn."),
            Definition("joint-distribution", "HasJointDistribution", "A matching nonnegative joint distribution", JointFormula(),
                "There exists a nonnegative real mass function on all Boolean time assignments "
                    + "whose two-time marginals equal the specified tables for every i < j and "
                    + "every pair of outcomes. The finite sum is restricted to assignments having "
                    + "those outcomes. This is the matching-joint-probability requirement in TeX "
                    + "line 551. The definition does not separately require total mass one; when "
                    + "n is at least two and a pair table is normalized, that marginal identity "
                    + "forces normalization. The definition also permits n equal to zero or one."),
            Describe.Lean(
                DescribeId.Create("claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("The sufficiency assertion"),
                StatementSource.FromAuthor(Disp(ClaimFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "For every natural n at least three and every compatible family of normalized "
                        + "nonnegative pair tables, the n-gon inequalities and all three-time "
                        + "Leggett-Garg inequalities imply a matching joint distribution. This is "
                        + "the universal assertion corresponding to the conjecture in Section 4.B, "
                        + "TeX lines 549-561. It imposes the polygon inequalities on the full set "
                        + "of n times; it does not additionally impose them on every subset."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("A six-time obstruction to a joint distribution"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(Local("claim"))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Use the six time indices 0, 1, 2, 3, 4 and 5. Set the correlations between "
                            + "index 5 and indices 0, 1, 2 and 3 to 1/2, the correlation between "
                            + "4 and 5 to -1/2, and all other correlations at distinct indices to zero. "
                            + "For each pair of Boolean outcomes, take the table entry to be one "
                            + "quarter of one plus the product of the two signs and the specified "
                            + "correlation.")),
                    Paragraph(Text(
                        "Evaluation of the finitely many indices and outcomes shows that every "
                            + "ordered pair table is nonnegative and normalized, with both one-time "
                            + "marginals equal to the constant 1/2. Summing the four signed entries "
                            + "recovers each specified correlation. Since six is even, the polygon "
                            + "lower bound is zero; evaluation on all 64 Boolean sign assignments "
                            + "verifies every six-gon inequality. Evaluation on every ordered "
                            + "triple i < j < k and every triple of outcomes verifies the "
                            + "three-time inequalities.")),
                    Paragraph(Text(
                        "Choose the real coefficients (1, 1, 1, 1, -1, -2), and let W(x) be "
                            + "their scalar product with the six signs of an assignment x. "
                            + "Expansion on the 64 assignments gives W(x) squared as the sum of "
                            + "the coefficient squares plus twice the sum, over i < j, of the "
                            + "two coefficients multiplied by the corresponding two signs.")),
                    Paragraph(Text(
                        "Suppose a nonnegative joint mass function matches the pair tables. "
                            + "Partitioning its assignments by the outcomes at indices 0 and 1 "
                            + "and using that pair's normalization shows that its total mass is one. "
                            + "For any i < j, partitioning by the two outcomes similarly shows "
                            + "that the expectation of the product of the two signs is the "
                            + "specified pair correlation.")),
                    Paragraph(Text(
                        "Distribute the mass function through the finite double sum and "
                            + "interchange the sums over assignments and time indices. The square "
                            + "expansion and the pair expectations then express the expectation "
                            + "of W squared as the sum of the coefficient squares times the total "
                            + "mass, plus twice the sum of coefficient products weighted by the "
                            + "pair correlations.")),
                    Paragraph(Text(
                        "Evaluation on all 64 assignments gives W(x) squared at least one "
                            + "at every assignment. Nonnegative mass and total mass one therefore "
                            + "give an expectation at least one. But the sum of the coefficient "
                            + "squares is 9, and the sum of their pair products weighted by the "
                            + "specified correlations is -5. The same expectation is consequently "
                            + "9 + 2(-5) = -1, a contradiction.")),
                    Paragraph(Text(
                        "Thus these six-time tables satisfy every hypothesis of the "
                            + "sufficiency assertion and admit no matching joint distribution. "
                            + "Applying that assertion at n = 6 would give the impossible joint "
                            + "distribution, so the universal assertion is false."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Definition(string id, string declaration, string title,
        Formula formula, string prose) => Describe.Lean(
            DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula PairTablesFormula() => All("n", Naturals(),
        Equal(Call("PairTables", X("n")), Arrow(FinOf(X("n")),
            Arrow(FinOf(X("n")), Arrow(Booleans(), Arrow(Booleans(), Reals()))))));

    private static Formula IsPairFamilyFormula()
    {
        Formula normalized = Equal(SumOver("a", Booleans(),
            SumOver("b", Booleans(), Entry())), Real(D(1)));
        Formula nonnegative = All("a", Booleans(), All("b", Booleans(), LE(Real(D(0)), Entry())));
        Formula tables = All("i", FinOf(X("n")), All("j", FinOf(X("n")),
            Implies(LT(X("i"), X("j")), And(nonnegative, normalized))));
        Formula first = All("a", Booleans(), Equal(SumOver("b", Booleans(), Entry()),
            At(X("m"), X("i"), X("a"))));
        Formula second = All("b", Booleans(), Equal(SumOver("a", Booleans(), Entry()),
            At(X("m"), X("j"), X("b"))));
        Formula compatible = Some("m", Arrow(FinOf(X("n")), Arrow(Booleans(), Reals())),
            All("i", FinOf(X("n")), All("j", FinOf(X("n")),
                Implies(LT(X("i"), X("j")), And(first, second)))));
        return FamilyBinders(IffF(Call("IsPairFamily", X("p")), And(tables, compatible)));
    }

    private static Formula CorrFormula() => FamilyBinders(All("i", FinOf(X("n")),
        All("j", FinOf(X("n")), Equal(Call("corr", X("p"), X("i"), X("j")),
            SumOver("a", Booleans(), SumOver("b", Booleans(),
                Multiply(Multiply(Sign(X("a")), Sign(X("b"))), Entry())))))));

    private static Formula NGonFormula()
    {
        Formula term = At(Qualified("ite"), LT(X("i"), X("j")),
            Multiply(Multiply(Sign(At(X("s"), X("i"))), Sign(At(X("s"), X("j")))),
                Call("corr", X("p"), X("i"), X("j"))), Real(D(0)));
        Formula bound = At(Qualified("ite"), At(Qualified("Odd"), X("n")), Real(D(1)), Real(D(0)));
        Formula total = Add(Typed(At(Qualified("Nat", "cast"), X("n")), Reals()),
            Multiply(Real(D(2)), SumOver("i", FinOf(X("n")), SumOver("j", FinOf(X("n")), term))));
        return FamilyBinders(IffF(Call("NGonInequalities", X("p")),
            All("s", AssignmentType(), LE(bound, total))));
    }

    private static Formula ThreeTimeFormula()
    {
        Formula first = Multiply(Multiply(Sign(X("a")), Sign(X("b"))),
            Call("corr", X("p"), X("i"), X("j")));
        Formula second = Multiply(Multiply(Sign(X("a")), Sign(X("c"))),
            Call("corr", X("p"), X("i"), X("k")));
        Formula third = Multiply(Multiply(Sign(X("b")), Sign(X("c"))),
            Call("corr", X("p"), X("j"), X("k")));
        Formula inequality = LE(Real(D(0)), Add(Add(Add(Real(D(1)), first), second), third));
        Formula outcomes = All("a", Booleans(), All("b", Booleans(), All("c", Booleans(), inequality)));
        Formula ordered = Implies(LT(X("i"), X("j")), Implies(LT(X("j"), X("k")), outcomes));
        return FamilyBinders(IffF(Call("ThreeTimeLG", X("p")),
            All("i", FinOf(X("n")), All("j", FinOf(X("n")), All("k", FinOf(X("n")), ordered)))));
    }

    private static Formula JointFormula()
    {
        Formula nonnegative = All("x", AssignmentType(), LE(Real(D(0)), At(Mu, X("x"))));
        Formula fiber = And(Equal(At(X("x"), X("i")), X("a")),
            Equal(At(X("x"), X("j")), X("b")));
        Formula marginal = Equal(Seq(new Formula.Subscript(Sum,
            Seq(Typed(X("x"), AssignmentType()), Comma, Sp, fiber)), Sp, Parenthesized(At(Mu, X("x")))), Entry());
        Formula pairs = All("i", FinOf(X("n")), All("j", FinOf(X("n")),
            Implies(LT(X("i"), X("j")), All("a", Booleans(), All("b", Booleans(), marginal)))));
        return FamilyBinders(IffF(Call("HasJointDistribution", X("p")),
            Some("μ", Arrow(AssignmentType(), Reals()), And(nonnegative, pairs))));
    }

    private static Formula ClaimFormula() => IffF(Local("claim"), FamilyBinders(
        Implies(LE(Typed(D(3), Naturals()), X("n")), Implies(Call("IsPairFamily", X("p")),
            Implies(Call("NGonInequalities", X("p")), Implies(Call("ThreeTimeLG", X("p")),
                Call("HasJointDistribution", X("p"))))))));

    private static Formula FamilyBinders(Formula body) => All("n", Naturals(),
        All("p", Call("PairTables", X("n")), body));
    private static Formula AssignmentType() => Arrow(FinOf(X("n")), Booleans());
    private static Formula Entry() => At(X("p"), X("i"), X("j"), X("a"), X("b"));
    private static Formula Sign(Formula value) => At(Qualified("D5", "S3", "Combinatorics", "IsingUniquenessSets", "sgn"), value);
    private static Formula Local(string name) => Qualified("D5", "S3", "Quantum", "Contextuality",
        "LeggettGargSixTimeSufficiencyRefutation", name);
    private static Formula Call(string name, params Formula[] arguments) => At(Local(name), arguments);
    private static Formula X(string name) => name == "μ" ? Mu : F.Id(name);
    private static Formula Qualified(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(F.Id(part));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula At(Formula function, params Formula[] arguments) => new Formula.Apply(function, [.. arguments]);
    private static Formula Parenthesized(Formula value) => new Formula.LatexSequence([Open, value, Close]);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Booleans() => Qualified("Bool");
    private static Formula Real(Formula value) => Typed(value, Reals());
    private static Formula FinOf(Formula n) => At(Qualified("Fin"), n);
    private static Formula Arrow(Formula domain, Formula codomain) => new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Some(string name, Formula type, Formula body) =>
        Seq(Exists, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula SumOver(string name, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Typed(X(name), type)), Sp, Parenthesized(body));
    private static Formula LE(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula LT(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula And(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Implies(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula IffF(Formula left, Formula right) => new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
}
