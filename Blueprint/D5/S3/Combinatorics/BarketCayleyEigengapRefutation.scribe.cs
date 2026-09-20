using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics;

internal sealed class BarketCayleyEigengapRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Combinatorics/BarketCayleyEigengapRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/barket2026graphical");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The normalised-Laplacian eigengap conjecture fails on the Cayley 5-cycle.",
        H("A Five-Cycle Central-Quotient Counterexample"),
        Blocks(
            Definition("normalized-laplacian", "The normalised Laplacian",
                "normalizedLaplacian", NormalizedLaplacianFormula(),
                "For a finite simple graph, lapMatrix is L=D-A. Division is in the real "
                    + "numbers, entry by entry. The paper writes: \"L_N = D^{−1/2} L "
                    + "D^{−1/2} = I − D^{−1/2} A D^{−1/2}, (4.9)\"."),
            Definition("normalized-laplacian-classical", "Classical adjacency selection",
                "normalizedLaplacianClassical", NormalizedLaplacianClassicalFormula(),
                "Every adjacency proposition has a classical decision procedure. Selecting it "
                    + "supplies the implementation structure required by lapMatrix and degree; "
                    + "proof irrelevance makes the resulting matrix independent of that choice."),
            Definition("sorted-spectrum", "The ascending characteristic spectrum",
                "sortedSpectrum", SortedSpectrumFormula(),
                "The characteristic-polynomial roots are taken with multiplicity and sorted "
                    + "ascending. For a normalised Laplacian the matrix is real symmetric, so "
                    + "all roots are real and this list is its complete spectrum."),
            Definition("eig", "One-indexed spectral access", "eig", EigFormula(),
                "The index is one-based. getD reads position i-1 and returns zero outside the "
                    + "list; the conjecture only uses indices from one through card(G)-1."),
            Definition("conjecture-gap-set", "Indices of gaps above one",
                "conjectureGapSet", ConjectureGapSetFormula(),
                "The graph is the underlying undirected multiplicative Cayley graph. The paper "
                    + "writes: \"given the sorted spectrum of L_N, define the consecutive "
                    + "eigengaps δᵢ = λ_{i+1} − λᵢ for i = 1, …, n − 1\" and "
                    + "\"k_τ = min{i : δᵢ > τ}\", with τ = 1.0."),
            Definition("claim", "Conjecture 4.4 as printed", "claim", ClaimFormula(),
                "The paper states: \"Conjecture 4.4 (Central-quotient eigengaps). Let G be a "
                    + "finite nilpotent group with upper central series 1 = Z₀(G) ≤ Z₁(G) ≤ "
                    + "· · · ≤ Z_c(G) = G, and let Γ = Cay(G, S) be the underlying undirected "
                    + "Cayley graph associated to a chosen generating set S. If k_{>1} = "
                    + "min{i : λ_{i+1} − λ_i > 1} is defined for the normalised Laplacian "
                    + "spectrum of Γ, then either k_{>1} = |G| − 1, or k_{>1} = "
                    + "|G/Z_j(G)| for some 1 ≤ j ≤ c.\" The DecidableEq binder is "
                    + "implementation structure, classically available for every type."),
            Describe.Lean(DescribeId.Create("barket-eigengap-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The central-quotient eigengap conjecture is false"),
                StatementSource.FromAuthor(ResultFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For G=Z/5 and S={1}, the Cayley graph is the 5-cycle. Its normalised "
                        + "Laplacian has characteristic polynomial X(X^2-(5/2)X+5/4)^2 and "
                        + "ascending spectrum [0,a,a,b,b], where a=(5-sqrt(5))/4 and "
                        + "b=(5+sqrt(5))/4. The consecutive gaps are [a,0,sqrt(5)/2,0], "
                        + "so the first gap above one has index three. The final index is four, "
                        + "while the only central quotient allowed by nilpotency class one has "
                        + "cardinality one."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create(
                        "barket-central-quotient-eigengap-conjecture-refutation"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Definition(
        string id, string title, string name, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create("barket-eigengap-" + id),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(formula),
            AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula NormalizedLaplacianFormula()
    {
        var vertex = F.Id("V");
        var graph = F.Id("Gamma");
        var i = F.Id("i");
        var j = F.Id("j");
        var numerator = Call("entry", Call("lapMatrix", graph), i, j);
        var denominator = Multiply(
            Call("sqrt", Call("degree", graph, i)),
            Call("sqrt", Call("degree", graph, j)));
        var equation = Universal("i", vertex, Universal("j", vertex,
            Equal(Call("entry", Call("normalizedLaplacian", graph), i, j),
                new Formula.Fraction(numerator, denominator))));
        return Disp(TypeContext("V", [Call("Fintype", vertex), Call("DecidableEq", vertex)],
            Universal("Gamma", Call("SimpleGraph", vertex),
                Implies(Call("DecidableRel", Call("Adj", graph)), equation))));
    }

    private static Formula NormalizedLaplacianClassicalFormula()
    {
        var vertex = F.Id("V");
        var graph = F.Id("Gamma");
        var equation = Universal("Gamma", Call("SimpleGraph", vertex),
            Equal(Call("normalizedLaplacianClassical", graph),
                Call("normalizedLaplacian", graph,
                    Call("Classical.decRel", Call("Adj", graph)))));
        return Disp(TypeContext("V", [Call("Fintype", vertex), Call("DecidableEq", vertex)],
            equation));
    }

    private static Formula SortedSpectrumFormula()
    {
        var vertex = F.Id("V");
        var matrix = F.Id("M");
        var ascending = Parenthesized(new Formula.Relation(
            new Formula.Placeholder(), FormulaRelationOperator.LessThanOrEqual,
            new Formula.Placeholder()));
        var equation = Universal("M", Call("Matrix", vertex, vertex, Reals()),
            Equal(Call("sortedSpectrum", matrix),
                Call("Multiset.sort", Call("roots", Call("charpoly", matrix)), ascending)));
        return Disp(TypeContext("V", [Call("Fintype", vertex), Call("DecidableEq", vertex)],
            equation));
    }

    private static Formula EigFormula()
    {
        var spectrum = F.Id("l");
        var i = F.Id("i");
        return Disp(Universal("l", Call("List", Reals()), Universal("i", Naturals(),
            Equal(Call("eig", spectrum, i),
                Call("getD", spectrum, Subtract(i, D(1)), D(0))))));
    }

    private static Formula ConjectureGapSetFormula()
    {
        var group = F.Id("G");
        var generators = F.Id("S");
        var i = F.Id("i");
        var graph = Call("mulCayley", Call("asSet", generators));
        var spectrum = Call("sortedSpectrum", Call("normalizedLaplacianClassical", graph));
        var gap = Greater(
            Subtract(Call("eig", spectrum, Add(i, D(1))), Call("eig", spectrum, i)),
            D(1));
        var condition = And(
            LessEqual(D(1), i),
            And(LessEqual(i, Subtract(Call("FintypeCard", group), D(1))), gap));
        var set = Seq(OpenBrace, i, Sp, Mid, Sp, condition, CloseBrace);
        var equation = Universal("S", Call("Finset", group),
            Equal(Call("conjectureGapSet", generators), set));
        return Disp(TypeContext("G",
            [Call("Group", group), Call("Fintype", group), Call("DecidableEq", group)],
            equation));
    }

    private static Formula ClaimFormula()
    {
        var group = F.Id("G");
        var generators = F.Id("S");
        var k = F.Id("k");
        var j = F.Id("j");
        var generated = Equal(Call("closure", Call("asSet", generators)), Call("top", group));
        var least = Call("IsLeast", Call("conjectureGapSet", generators), k);
        var last = Equal(k, Subtract(Call("FintypeCard", group), D(1)));
        var quotient = Call("quotient", group, Call("upperCentralSeries", group, j));
        var central = Exists("j", Naturals(), And(
            LessEqual(D(1), j),
            And(LessEqual(j, Call("nilpotencyClass", group)),
                Equal(k, Call("NatCard", quotient)))));
        var conclusion = Or(last, central);
        var body = Implies(Call("IsNilpotent", group),
            Universal("S", Call("Finset", group),
                Implies(generated,
                    Universal("k", Naturals(), Implies(least, conclusion)))));
        var quantified = TypeContext("G",
            [Call("Group", group), Call("Fintype", group), Call("DecidableEq", group)], body);
        return Disp(Iff(F.Id("claim"), quantified));
    }

    private static Formula ResultFormula() => Disp(new Formula.Not(F.Id("claim")));

    private static Formula Naturals() => Named("Nat");
    private static Formula Reals() => Named("Real");
    private static Formula Named(string name) =>
        new Formula.NamedConstant(FormulaIdentifier.Create(name));
    private static Formula TypeContext(string name, Formula[] assumptions, Formula body)
    {
        for (var index = assumptions.Length - 1; index >= 0; index--)
        {
            body = Implies(assumptions[index], body);
        }
        return Universal(name, Named("Type"), body);
    }
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Universal(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Exists(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);
    private static Formula Call(string name, params Formula[] arguments)
    {
        var parts = name.Split('.');
        return parts.Length == 2
            ? new Formula.Apply(Seq(F.Id(parts[0]), Dot, F.Id(parts[1])), [.. arguments])
            : new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    }
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula LessEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Greater(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.GreaterThan, right);
    private static Formula Add(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Multiply(Formula left, Formula right) =>
        new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Or(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Or, Parenthesized(right));
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Iff(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
}
