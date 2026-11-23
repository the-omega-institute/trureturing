using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.MembraneSignatures;

internal sealed class AmendolaRiffoSchmitzRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Analytic/MembraneSignatures/AmendolaRiffoSchmitzRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/MembraneSignatures/amendolariffoschmitz2026membranes");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A normalized two-letter array satisfies the printed membrane shuffle equations and has no piecewise bilinear realization.",
        H("The printed Chen–Chow conjecture for membranes"),
        Blocks(
            Definition("grid", "Piecewise bilinear membranes", "PiecewiseBilinear",
                GridFormula(),
                "Section 4, p. 20, calls a membrane of order (m,n) one that is biaffine on every "
                    + "closed rectangle [(i−1)/m,i/m] × [(j−1)/n,j/n]. In zero-based indices I(m,i) "
                    + "is [i/m,(i+1)/m]. Both grid sizes are arbitrary positive integers. "
                    + "Biaffinity means that each component agrees throughout each closed cell with a "
                    + "polynomial a + bs + et + fst. One function on the whole square gives the same "
                    + "values on shared cell boundaries. The Lean function is a total ambient extension "
                    + "to ℝ × ℝ, with its cell conditions confined to the square."),
            Definition("signature", "Native mixed-partial signature", "signature",
                SignatureFormula(),
                "Definition 1.1, p. 2, integrates over the product of the two weakly increasing unit "
                    + "simplices. In degree ℓ, w lists ℓ letters and τ permutes ℓ column slots. "
                    + "The j-th factor is the real mixed partial of component w(j) evaluated at "
                    + "(s_j,t_{τ(j)}). The native derivative differentiates in t and then in s. "
                    + "On open cells it equals the biaffine mixed coefficient, and either derivative "
                    + "order gives that coefficient there. The grid lines and their pullbacks through "
                    + "each pair of coordinate evaluations are Lebesgue null. "
                    + "The integral therefore depends only on the square restriction. Degree zero equals one."),
            Definition("printed", "The printed truncated shuffle equations", "Printed",
                PrintedFormula(),
                "Theorem 2.10, p. 6, uses the product in Definition 2.6, p. 5. Test every ordered "
                    + "pair of words u,v and ranks α,β in degrees m,n with m+n ≤ k. In the positive-degree "
                    + "sum, π and λ independently range over the permutations increasing on each of the "
                    + "two source blocks. The word in a summand is the concatenation uv composed with π⁻¹. "
                    + "Its rank is λ ∘ (α ▷ β)⁻¹ ∘ π⁻¹, where α ▷ β extends both ranks on their own blocks. "
                    + "Every shuffle pair contributes once, even when distinct pairs index the same coordinate. "
                    + "The empty word and its unique permutation act as the unit."),
            Definition("claim", "Conjecture 6.10 as printed", "claim",
                ClaimFormula(),
                "Conjecture 6.10, p. 32. “For every sequence s ∈ ⊕_{ℓ=0}^k ⊕_{ν∈Σ_ℓ}(ℝ^d)^{⊗ℓ} "
                    + "with entries satisfying the two-parameter shuffle identity (Theorem 2.10) there is a "
                    + "piecewise bilinear membrane such that its k-truncated signature coincides with s.” "
                    + "The real array has one entry for each degree ℓ ≤ k, word on d letters, and permutation "
                    + "of ℓ slots. Equality of signatures means equality at every one of these indices."),
            Describe.Lean(
                DescribeId.Create("amendola-riffo-schmitz-result"),
                DeclarationHandle.Create(Prefix + "refute_conjecture_6_10_v1"),
                H("A normalized array with no membrane realization"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parens(ClaimFormula())))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Take d = 2 and k = 4. The rational array has 443 coordinates, with the "
                            + "empty coordinate equal to one and zero whenever the word uses the second letter. "
                            + "Its coefficients satisfy all 1,177 ordered equations of the printed system. "
                            + "For the input pair (1,1) and (111,231) in one-based notation, "
                            + "both the product and the printed sum equal 19/4.")),
                    Paragraph(Text(
                        "In a product of the degree-one and degree-three integrals, insert the singleton "
                            + "at one of four positions on each axis. Up to null ties, the 16 chambers "
                            + "partition the joint domain. Reindexing the axes sends old row slot j to "
                            + "π(j) and its old column slot (α ▷ β)(j) to λ((α ▷ β)(j)). "
                            + "The new row word uses π⁻¹ and the new rank is λ ∘ (α ▷ β) ∘ π⁻¹. "
                            + "For the same rational input pair this forward shuffle sum equals 7/4, "
                            + "so equality to a membrane signature is impossible.")),
                    Paragraph(Text(
                        "The same array refutes the printed conjecture with explicit degree-zero normalization. "
                            + "Realizability under the genuine shuffle equations remains open."))),
                DescribeRole.Theorem)
        )));

    private static DocumentBlock Definition(
        string id, string title, string declaration, Formula formula, string prose) =>
        Describe.Lean(
            DescribeId.Create("amendola-riffo-schmitz-" + id),
            DeclarationHandle.Create(Prefix + declaration),
            H(title),
            StatementSource.FromAuthor(Disp(formula)),
            AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))),
            DescribeRole.Definition);

    private static Formula V(string name) => F.Id(name);
    private static Formula Named(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Named(name), [.. args]);
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Parens(Formula value) => Seq(Open, value, Close);
    private static Formula N => Seq(Mathbb, Grp(V("N")));
    private static Formula R => Seq(Mathbb, Grp(V("R")));
    private static Formula Fin(Formula size) => Call("Fin", size);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, Parens(body));
    private static Formula Some(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, Parens(body));
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula LE(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula LT(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Member(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parens(a), FormulaLogicOperator.And, Parens(b));
    private static Formula If(Formula a, Formula b) => new Formula.Logic(Parens(a), FormulaLogicOperator.Implies, Parens(b));
    private static Formula IffOf(Formula a, Formula b) => new Formula.Logic(Parens(a), FormulaLogicOperator.Iff, Parens(b));
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Membrane => Call("Membrane", V("d"));
    private static Formula At(Formula degree, Formula word, Formula rank) => App(V("a"), degree, word, rank);

    private static Formula ClaimFormula()
    {
        var realizes = Some("X", Membrane, And(Call("PiecewiseBilinear", V("X")),
            Eq(Call("signature", V("X")), V("a"))));
        var arrays = All("a", Call("Array", R, V("d"), V("k")), If(Call("Printed", V("a")), realizes));
        return All("d", N, All("k", N, If(LE(D(2), V("d")), arrays)));
    }

    private static Formula GridFormula()
    {
        var polynomial = Add(Add(Add(V("a"), Mul(V("b"), V("s"))), Mul(V("e"), V("t"))),
            Mul(Mul(V("f"), V("s")), V("t")));
        var patch = All("s", R, All("t", R,
            If(And(Member(V("s"), Call("I", V("m"), V("i"))),
                Member(V("t"), Call("I", V("n"), V("j")))),
                Eq(App(V("X"), V("s"), V("t"), V("c")), polynomial))));
        var coefficients = Some("a", R, Some("b", R, Some("e", R, Some("f", R, patch))));
        var cells = All("i", Fin(V("m")), All("j", Fin(V("n")), All("c", Fin(V("d")), coefficients)));
        return IffOf(Call("PiecewiseBilinear", V("X")), Some("m", N, Some("n", N,
            And(And(LT(D(0), V("m")), LT(D(0), V("n"))), cells))));
    }

    private static Formula SignatureFormula()
    {
        var coordinate = Call("signature", V("X"), V("l"), V("w"), Tau);
        var domain = Seq(Call("simplex", V("l")), Sp, Times, Sp, Call("simplex", V("l")));
        var factor = Call("mixed", V("X"), App(V("w"), V("j")),
            new Formula.Subscript(V("s"), V("j")),
            new Formula.Subscript(V("t"), App(Tau, V("j"))));
        var integrand = Seq(new Formula.Subscript(Prod, Seq(V("j"), InMacro, Fin(V("l")))), Sp, factor);
        var integral = Seq(new Formula.Subscript(Int, domain), Sp, integrand, Thin, V("ds"), Thin, V("dt"));
        return new Formula.Aligned([
            If(Eq(V("l"), D(0)), Eq(coordinate, D(1))),
            If(LT(D(0), V("l")), Eq(coordinate, integral))]);
    }

    private static Formula PrintedFormula()
    {
        var degree = Fin(Add(V("k"), D(1)));
        var equation = Eq(Mul(At(V("m"), V("u"), V("alpha")), At(V("n"), V("v"), V("beta"))),
            Call("printedRhs", V("a"), V("m"), V("n"), V("u"), V("v"), V("alpha"), V("beta")));
        var ranks = All("alpha", Call("Rank", V("m")), All("beta", Call("Rank", V("n")), equation));
        var words = All("u", Call("Word", V("d"), V("m")), All("v", Call("Word", V("d"), V("n")), ranks));
        var inputs = All("m", degree, All("n", degree, If(LE(Add(V("m"), V("n")), V("k")), words)));
        return IffOf(Call("Printed", V("a")), inputs);
    }
}
