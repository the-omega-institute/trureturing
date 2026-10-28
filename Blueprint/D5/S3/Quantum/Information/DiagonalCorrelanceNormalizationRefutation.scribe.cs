using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;

internal sealed class DiagonalCorrelanceNormalizationRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Information/DiagonalCorrelanceNormalizationRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Entropy/hedemann2020correlance");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A seven-qubit diagonal state exceeds the proposed diagonal-correlance normalization.",
        H("Diagonal correlance exceeds its proposed normalization"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("reduction-product"),
                DeclarationHandle.Create(Prefix + "reductionProduct"),
                H("The product of the one-coordinate reductions"),
                StatementSource.FromAuthor(Disp(ReductionProductFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For a real function p on n-bit strings, the reduction product is the diagonal matrix "
                    + "whose entry at x is the product of the n one-coordinate marginals evaluated at x i. "
                    + "FunOnFinite.map sums p over the fiber of the coordinate map y to y i. "
                    + "When p is a probability distribution, these marginals are the diagonal entries of the "
                    + "single-qubit reduced states, and this matrix is their tensor product. "
                    + "This is the diagonal-state form of Hedemann's equation (11), "
                    + "CorrelanceAndDiscordance.tex lines 308-312. "
                    + "The definition also applies to arbitrary real p and to n equal to zero."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("correlance-raw"),
                DeclarationHandle.Create(Prefix + "correlanceRaw"),
                H("Raw correlance of a diagonal state"),
                StatementSource.FromAuthor(Disp(CorrelanceRawFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "Raw correlance is the trace of the square of the difference between the diagonal matrix "
                    + "with entries p and its reduction product. For a probability distribution p, "
                    + "this is the squared Hilbert-Schmidt distance between the diagonal density matrix "
                    + "and the tensor product of its single-qubit reductions. "
                    + "It is Hedemann's equation (10), CorrelanceAndDiscordance.tex lines 303-305, "
                    + "restricted to diagonal real matrices. No probability assumption is needed to define it."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("The proposed bound for every number of qubits"),
                StatementSource.FromAuthor(Disp(ClaimFormula())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The assertion requires the raw correlance of every probability distribution on n-bit strings "
                    + "to be at most one half minus the reciprocal of two to the nth power, for every natural n at least two. "
                    + "Probability p means that all entries are nonnegative and their finite sum is one. "
                    + "This is the qubit consequence of the maximum over all diagonal states in equation (16) "
                    + "and the normalization asserted in equation (18), CorrelanceAndDiscordance.tex lines 450-465. "
                    + "The source states that the equal mixture of the first and last basis projectors "
                    + "attains this maximum in all systems."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("A seven-qubit counterexample"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(Local("claim"))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Subtraction and squaring preserve diagonal matrices, and the trace of a diagonal matrix "
                        + "is the sum of its entries. Thus raw correlance is the sum over all bit strings x "
                        + "of the squared difference between p(x) and the product of its coordinate marginals at x.")),
                    Paragraph(Text(
                        "For seven qubits, take p to put mass 3/5 on the all-false string, mass 2/5 on the all-true string, "
                        + "and zero elsewhere. These entries are nonnegative and sum to one. "
                        + "Summing over a coordinate fiber gives mass 3/5 at false and mass 2/5 at true, "
                        + "for every coordinate i. Consequently the reduction-product entry at x is the product "
                        + "of seven factors, each equal to 3/5 or 2/5 according to the bit x i.")),
                    Paragraph(Text(
                        "Squaring this product squares each factor. The sum over all seven-bit strings "
                        + "then factors into seven copies of (3/5)^2 + (2/5)^2, "
                        + "so the sum of the squared reduction-product entries is (13/25)^7. "
                        + "The two constant strings are distinct, so the sum of p(x)^2 is just "
                        + "(3/5)^2 + (2/5)^2 = 13/25. "
                        + "The mixed sum of p(x) times the reduction-product entry has only the same two nonzero terms: "
                        + "(3/5)^8 + (2/5)^8.")),
                    Paragraph(Text(
                        "Expanding each squared difference and distributing the finite sums therefore gives "
                        + "raw correlance 13/25 - 2((3/5)^8 + (2/5)^8) + (13/25)^7 "
                        + "= 3023545392/6103515625. "
                        + "If the assertion held, applying it to n = 7 and this probability distribution "
                        + "would bound that number by 1/2 - 1/2^7 = 63/128. "
                        + "Their difference is 2492325801/781250000000, which is strictly positive, a contradiction. "
                        + "Thus the proposed bound fails already for seven qubits. "
                        + "This does not determine the actual maximum over diagonal states."))),
                DescribeRole.Theorem))));

    private static Formula ReductionProductFormula()
    {
        Formula diagonal = At(Qualified("Matrix", "diagonal"), LambdaOf("x", BitStrings(),
            ProductOver("i", FinOf(X("n")), MarginalAt(X("p"), At(X("x"), X("i"))))));
        return OverRealFunctions(Equal(Typed(LocalCall("reductionProduct", X("p")), MatrixType()), diagonal));
    }

    private static Formula CorrelanceRawFormula()
    {
        Formula difference = new Formula.Binary(At(Qualified("Matrix", "diagonal"), X("p")),
            FormulaBinaryOperator.Subtract, LocalCall("reductionProduct", X("p")));
        Formula trace = At(Qualified("Matrix", "trace"),
            new Formula.Power(Parenthesized(difference), Typed(D(2), Naturals())));
        return OverRealFunctions(Equal(Typed(LocalCall("correlanceRaw", X("p")), Reals()), trace));
    }

    private static Formula ClaimFormula()
    {
        Formula bound = new Formula.Binary(
            new Formula.Fraction(Typed(D(1), Reals()), Typed(D(2), Reals())),
            FormulaBinaryOperator.Subtract,
            new Formula.Fraction(Typed(D(1), Reals()), new Formula.Power(Typed(D(2), Reals()), X("n"))));
        Formula probabilities = All("p", Arrow(BitStrings(), Reals()), Implication(
            At(Qualified("D5", "S3", "TotalVariation", "CycleSingleCutMinimax", "Probability"), X("p")),
            LE(LocalCall("correlanceRaw", X("p")), bound)));
        return Equivalence(Local("claim"),
            All("n", Naturals(), Implication(LE(Typed(D(2), Naturals()), X("n")), probabilities)));
    }

    private static Formula MarginalAt(Formula p, Formula bit) =>
        At(Qualified("FunOnFinite", "map"),
            LambdaOf("y", BitStrings(), At(X("y"), X("i"))), p, bit);
    private static Formula OverRealFunctions(Formula body) =>
        All("n", Naturals(), All("p", Arrow(BitStrings(), Reals()), body));
    private static Formula MatrixType() => At(Qualified("Matrix"), BitStrings(), BitStrings(), Reals());
    private static Formula BitStrings() => Arrow(FinOf(X("n")), Qualified("Bool"));
    private static Formula FinOf(Formula n) => At(Qualified("Fin"), n);
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula X(string name) => F.Id(name);
    private static Formula Local(string name) => Qualified("D5", "S3", "Quantum", "Information",
        "DiagonalCorrelanceNormalizationRefutation", name);
    private static Formula LocalCall(string name, params Formula[] args) => At(Local(name), args);
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
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula value) =>
        new Formula.LatexSequence([Left, Open, value, Right, Close]);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula LambdaOf(string name, Formula type, Formula body) =>
        Parenthesized(Seq(LambdaLower, Sp, Typed(X(name), type), Sp, Mapsto, Sp, Parenthesized(body)));
    private static Formula ProductOver(string name, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Prod, Seq(X(name), Colon, Sp, type)), Sp, Parenthesized(body));
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula LE(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Implication(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Equivalence(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
}
