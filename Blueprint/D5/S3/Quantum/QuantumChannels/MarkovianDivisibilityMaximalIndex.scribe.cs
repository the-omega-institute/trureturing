using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels;

internal sealed class MarkovianDivisibilityMaximalIndexDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/QuantumChannels/MarkovianDivisibilityMaximalIndex";
    private static LibraryNoteRef Source =>
        LibraryNoteRef.Create("D5/L/Eigenstructure/carograswald2021markovian");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The greatest admissible index is 2d minus 5 for dimensions at least five, and two in dimension three.",
        H("The maximal index for arithmetic and geometric mean matrices"),
        Blocks(
            Node("arith", "The arithmetic mean at an ordered position", ArithmeticFormula(),
                AssessedProvenance.FromLiterature(Source),
                "For a real vector p indexed by Fin d, arith p ij is the arithmetic mean of the coordinates at the two components of ij. "
                    + "The function meanOne is exactly their sum divided by two. The positions are ordered, so both (i,j) and (j,i) occur. "
                    + "This is the matrix a in Conjecture 4.19, arXiv v3 TeX lines 729–731. "
                    + "The definition allows arbitrary real coordinates and every natural dimension; nonnegativity and normalization are imposed separately."),
            Node("geom", "The geometric mean at an ordered position", GeometricFormula(),
                AssessedProvenance.FromLiterature(Source),
                "The function meanZero is Real.sqrt of the product of the two coordinates. For nonnegative p this gives the matrix g of Conjecture 4.19, "
                    + "arXiv v3 TeX lines 729–731, again with both ordered positions counted. "
                    + "The definition is total on all real vectors because Real.sqrt is zero on negative arguments."),
            Node("topSum", "The largest-entry sum with multiplicity", TopSumFormula(),
                AssessedProvenance.FromRepo(Source),
                "Take the nonempty finite maximum of the sums over subsets of ordered positions having exactly min(m,d*d) elements. "
                    + "The candidate subsets form Finset.powersetCard of the full position set, and their maximum is Finset.sup'. "
                    + "Nonemptiness follows because min(m,d*d) is at most the cardinality d*d of that set. "
                    + "For every real function f, this is the sum of its largest min(m,d*d) entries, with repeated values retained at their distinct positions. "
                    + "The value is zero at m = 0 and is the full sum when m is at least d*d, including in dimension zero. "
                    + "Applied separately to arith p and geom p, it expresses the two independently sorted sums in arXiv v3 TeX lines 733–735."),
            Node("IsProbability", "Nonnegative coordinates of total mass one", ProbabilityFormula(),
                AssessedProvenance.FromLiterature(Source),
                "A probability vector has every coordinate nonnegative and its finite sum equal to one. "
                    + "These are precisely the assumptions on p in arXiv v3 TeX line 729. The predicate is false in dimension zero."),
            Node("admissibleIndices", "Indices satisfying the universal inequality", AdmissibleFormula(),
                AssessedProvenance.FromRepo(Source),
                "The set consists of natural indices m for which every probability vector in dimension d satisfies "
                    + "topSum(arith p,m) + topSum(geom p,m) at most the real image of d. "
                    + "The two maxima may use different sets of positions. This specifies the universal inequality underlying the maximal integer in arXiv v3 TeX line 737, "
                    + "with sums saturated at d*d positions."),
            Describe.Lean(
                DescribeId.Create("markovian-maximal-index-result"),
                DeclarationHandle.Create(Module + ".result"),
                H("The greatest indices in dimensions at least five and in dimension three"),
                StatementSource.FromAuthor(Disp(ResultFormula())),
                AssessedProvenance.FromRepo(Source),
                ResultArgument(),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("caro-graswald-2021-markovian-divisibility-maximal-index"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string declaration, string title, Formula formula,
        AssessedProvenance provenance, string prose) => Describe.Lean(
            DescribeId.Create("markovian-maximal-index-" + declaration.ToLowerInvariant()),
            DeclarationHandle.Create(Module + "." + declaration), H(title),
            StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static BlockSequence ResultArgument() => Blocks(
        Paragraph(Text(
            "First, each largest-entry sum is attained by a set of the prescribed cardinality. "
                + "For nonnegative entries these sums are nondecreasing in m: a selected set can be enlarged to the larger prescribed cardinality without decreasing its sum. "
                + "For a probability vector each coordinate is at most one, and two distinct coordinates have sum at most one.")),
        Paragraph(Text(
            "For a position set s and an index set q, count how often the first or second component of a position in s belongs to q. "
                + "Each position contributes at most one, except that a position in q times q may contribute twice. "
                + "Thus this incidence count is at most |s| + |q| squared. "
                + "The arithmetic sum over s equals the sum of c(i)p(i), where c(i) is half the number of incidences at i, with a diagonal position counted twice. "
                + "Using singleton and two-element sets q gives c(i) at most (|s| + 1)/2 and c(i) + c(j) at most |s|/2 + 2 for distinct i,j.")),
        Paragraph(Text(
            "More generally, suppose c(i) is at most u, every distinct pair has sum at most v, v is at most 2u, "
                + "and all probabilities are at most t with t at least one half. Then the weighted sum of c(i)p(i) is at most (2t - 1)u + (1 - t)v. "
                + "If every coefficient is at most v/2, normalization gives a bound v/2, which is at most that expression. "
                + "Otherwise choose j with c(j) greater than v/2. Every other coefficient is at most v - c(j), "
                + "so the weighted sum is at most v - c(j) + (2c(j) - v)p(j). "
                + "Replace p(j) by t and then c(j) by u; both replacements multiply nonnegative coefficients.")),
        Paragraph(Text(
            "The sum of the squares of all geometric entries is the sum of p(i)p(j), hence one. "
                + "Cauchy–Schwarz therefore bounds the geometric sum on any set s by the square root of |s|. "
                + "For a sharper bound, let i maximize p and write t = p(i). The diagonal entry at (i,i) equals t and is at least every geometric entry. "
                + "Any nonempty selected set can be replaced by a set of the same cardinality containing (i,i), without decreasing its sum. "
                + "After removing that position, the remaining squared entries sum to at most 1 - t squared. "
                + "Another application of Cauchy–Schwarz gives t + sqrt(|s| - 1) sqrt(1 - t squared), where |s| - 1 is natural subtraction.")),
        Paragraph(Text(
            "Now let d be at least five and take independently chosen arithmetic and geometric position sets, each of size m = 2d - 5. "
                + "The incidence bounds give u = d - 2 and v = d - 1/2. Let t be the largest probability. "
                + "If t is at most one half, the weighted estimate with parameter 1/2 bounds the arithmetic sum by d/2 - 1/4. "
                + "The geometric sum is at most sqrt(2d - 5), which is at most d/2 - 1/4 for d at least five. "
                + "Their sum is consequently at most d. "
                + "If t is greater than one half, the weighted estimate bounds the arithmetic sum by 3/2 + (d - 7/2)t, "
                + "and the sharper geometric estimate bounds the other sum by t + sqrt(2d - 6) sqrt(1 - t squared). "
                + "The square of (d - 5/2)t + sqrt(2d - 6) sqrt(1 - t squared) is at most (d - 5/2) squared + 2d - 6, "
                + "by expanding the nonnegative square of (d - 5/2)sqrt(1 - t squared) - sqrt(2d - 6)t. "
                + "This yields a bound d - 3/2 for the expression itself, and adding 3/2 proves the desired bound d. "
                + "Choose sets attaining the two maxima; since m is at most d*d, both have size m. This proves admissibility of 2d - 5.")),
        Paragraph(Text(
            "To show failure at the next index, first note that the star consisting of (o,o), all (o,a) and all (a,o) for a in a set q not containing o "
                + "has size 2|q| + 1. The sum of any function on it is its value at (o,o) plus the sum over q of its two cross values. "
                + "Set o = 0, j = 1, z = d - 2 and q = {1,...,d - 3} inside Fin d. Put r = d - 2, k = d - 3 and n = r squared + k, all as real numbers. "
                + "Assign mass r squared/n at o, mass 1/n at each index of q, and zero at the two remaining indices. "
                + "These masses are nonnegative and sum to one. Let c be the star just described. "
                + "Use c together with (o,z) for the arithmetic sum, and c together with (j,j) for the geometric sum. "
                + "Both sets have size 2d - 4. Their sums are respectively r squared/(2n) + r squared/n + k(r squared + 1)/n "
                + "and 1/n + r squared/n + 2kr/n. "
                + "Their sum is d + (d - 4) squared/(2n), strictly greater than d. "
                + "Each selected sum is at most its corresponding largest-entry sum, so 2d - 4 is inadmissible.")),
        Paragraph(Text(
            "For dimension three, the arithmetic–geometric mean inequality bounds every geometric entry by the corresponding arithmetic entry. "
                + "Any two distinct arithmetic positions have sum at most 3/2: if both are diagonal, the corresponding distinct probabilities sum to at most one; "
                + "otherwise an off-diagonal entry is at most one half and the other entry is at most one. "
                + "Thus each of the two largest-entry sums at index two is at most 3/2, and their sum is at most three. "
                + "At p = (4/5,1/5,0), select the positions (0,0), (0,1) and (1,0). "
                + "Their arithmetic sum is 9/5 and their geometric sum is 8/5. Hence the largest-entry sums at index three total at least 17/5, greater than three.")),
        Paragraph(Text(
            "Finally, whenever m is admissible and a probability vector violates the inequality at m + 1, no larger natural index is admissible: "
                + "monotonicity of both largest-entry sums preserves that strict violation. "
                + "Apply this observation at m = 2d - 5 for every d at least five, and then at m = 2 in dimension three. "
                + "This proves the two greatest-element assertions. The first establishes the value proposed in arXiv v3 TeX line 737 in dimensions at least five; "
                + "the second gives two in dimension three, where the printed expression 2d - 5 equals one. "
                + "No value in dimensions one, two or four, and no determinant criterion for linear maps, is asserted here.")));

    private static Formula ArithmeticFormula()
    {
        Formula a = At(X("p"), Seq(X("ij"), Dot, D(1)));
        Formula b = At(X("p"), Seq(X("ij"), Dot, D(2)));
        return VectorBinders(All("ij", Positions(), new Formula.RelationChain(
            FormulaRelationOperator.Equal,
            [LocalCall("arith", X("p"), X("ij")),
                At(Qualified("D5", "S3", "Constants", "PowerMeanKernel", "meanOne"), a, b),
                new Formula.Fraction(Add(a, b), Typed(D(2), Reals()))])));
    }

    private static Formula GeometricFormula()
    {
        Formula a = At(X("p"), Seq(X("ij"), Dot, D(1)));
        Formula b = At(X("p"), Seq(X("ij"), Dot, D(2)));
        return VectorBinders(All("ij", Positions(), new Formula.RelationChain(
            FormulaRelationOperator.Equal,
            [LocalCall("geom", X("p"), X("ij")),
                At(Qualified("D5", "S3", "Constants", "PowerMeanKernel", "meanZero"), a, b),
                At(Qualified("Real", "sqrt"), Multiply(a, b))])));
    }

    private static Formula TopSumFormula()
    {
        Formula candidates = At(Qualified("Finset", "powersetCard"),
            At(Qualified("min"), X("m"), Multiply(X("d"), X("d"))),
            Typed(Qualified("Finset", "univ"), At(Qualified("Finset"), Positions())));
        Formula maximum = Seq(new Formula.Subscript(Max,
                Seq(Typed(X("s"), At(Qualified("Finset"), Positions())), Comma, Sp,
                    Member(X("s"), candidates))), Sp,
            Parenthesized(SumIn("ij", X("s"), At(X("f"), X("ij")))));
        return All("d", Naturals(), All("f", Arrow(Positions(), Reals()), All("m", Naturals(),
            Equal(LocalCall("topSum", X("f"), X("m")), maximum))));
    }

    private static Formula ProbabilityFormula() => VectorBinders(Equivalence(
        LocalCall("IsProbability", X("p")), Conjunction(
            All("i", FinOf(X("d")), LE(Typed(D(0), Reals()), At(X("p"), X("i")))),
            Equal(SumOver("i", FinOf(X("d")), At(X("p"), X("i"))), Typed(D(1), Reals())))));

    private static Formula AdmissibleFormula() => All("d", Naturals(), Equal(
        LocalCall("admissibleIndices", X("d")),
        Seq(OpenBrace, Typed(X("m"), Naturals()), Sp, Mid, Sp,
            All("p", Arrow(FinOf(X("d")), Reals()), Arrow(LocalCall("IsProbability", X("p")),
                LE(Add(LocalCall("topSum", LocalCall("arith", X("p")), X("m")),
                        LocalCall("topSum", LocalCall("geom", X("p")), X("m"))),
                    Typed(At(Qualified("Nat", "cast"), X("d")), Reals())))), CloseBrace)));

    private static Formula ResultFormula() => Conjunction(
        All("d", Naturals(), Arrow(LE(D(5), X("d")), At(Qualified("IsGreatest"),
            LocalCall("admissibleIndices", X("d")),
            Typed(Subtract(Multiply(D(2), X("d")), D(5)), Naturals())))),
        At(Qualified("IsGreatest"), LocalCall("admissibleIndices", Typed(D(3), Naturals())),
            Typed(D(2), Naturals())));

    private static Formula VectorBinders(Formula body) => All("d", Naturals(),
        All("p", Arrow(FinOf(X("d")), Reals()), body));
    private static Formula Positions() => Parenthesized(Seq(FinOf(X("d")), Sp, Times, Sp, FinOf(X("d"))));
    private static Formula FinOf(Formula d) => At(Qualified("Fin"), d);
    private static Formula LocalCall(string name, params Formula[] args) =>
        At(Qualified("D5", "S3", "Quantum", "QuantumChannels", "MarkovianDivisibilityMaximalIndex", name), args);
    private static Formula X(string name) => F.Id(name);
    private static Formula Naturals() => Seq(Mathbb, Grp(X("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(X("R")));
    private static Formula Parenthesized(Formula value) => new Formula.LatexSequence([Open, value, Close]);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Arrow(Formula domain, Formula codomain) =>
        new Formula.TypeArrow(Parenthesized(domain), Parenthesized(codomain));
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula LE(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Member(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Add, Parenthesized(right));
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Subtract, Parenthesized(right));
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(Parenthesized(left), FormulaBinaryOperator.Multiply, Parenthesized(right));
    private static Formula Conjunction(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Equivalence(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula SumOver(string name, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Typed(X(name), type)), Sp, Parenthesized(body));
    private static Formula SumIn(string name, Formula set, Formula body) =>
        Seq(new Formula.Subscript(Sum, Member(X(name), set)), Sp, Parenthesized(body));
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
}
