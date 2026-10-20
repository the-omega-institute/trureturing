using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy.PoissonBinomial;

internal sealed class PoissonBinomialStructureDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Entropy/PoissonBinomial/PoissonBinomialStructure.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Entropy/monkman2023symmetry");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite Bernoulli-sum laws, removal of two coordinates, and majorization chains in the open unit cube.",
        H("Poisson-binomial Structure"),
        Blocks(
            Node("pb", "The Bernoulli-sum law", Disp(Equal(Call("pb", F.Id("c"), F.Id("k")),
                Seq(Sum, Underscore, Grp(F.Id("A"), Colon, Sp, Call("card", F.Id("A")), EqualToken, F.Id("k")), Sp,
                    Call("w", F.Id("c"), F.Id("A"))))),
                "For c : Fin M → ℝ, pb c k sums over all subsets A of Fin M of cardinality k. " +
                "The weight w(c,A) is the product of c i over i in A times the product of 1−c i over i outside A. " +
                "On the closed unit cube this is the law of the sum of independent Bernoulli variables. " +
                "All cardinalities and indices are natural numbers; empty products are one.", DescribeRole.Definition,
                AssessedProvenance.FromLiterature(Source)),
            Node("F", "Configurational entropy", Disp(Equal(Call("F", F.Id("c")),
                Seq(Sum, Underscore, Grp(F.Id("i")), Sp, Call("h", Call("c", F.Id("i"))), Minus, Sp,
                    Sum, Underscore, Grp(F.Id("k"), EqualToken, D(0)), Caret, Grp(F.Id("M")), Sp,
                    Call("negMulLog", Call("pb", F.Id("c"), F.Id("k")))))),
                "Here h is Real.binEntropy, and Real.negMulLog x is −x log x with value zero at zero. " +
                "The first sum ranges over Fin M and the second over 0 through M. Natural logarithms give nats. " +
                "This is S−SN in Monkman and Sirker, Section 3.3. For independent coordinates it is also " +
                "the Shannon conditional entropy of the coordinate vector given its sum: independence gives " +
                "H(X)=Σ h(c i), and the sum N is a deterministic function of X, so H(X|N)=H(X)−H(N).",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("pb_nonneg", "Nonnegative masses", Disp(Seq(Call("ClosedCube", F.Id("c")), Sp,
                Rightarrow, Sp, D(0), Le, Call("pb", F.Id("c"), F.Id("k")))),
                "For every dimension, closed-cube parameter vector and natural k, each summand is nonnegative.",
                DescribeRole.Theorem),
            Node("pb_sum_one", "Total mass", Disp(Equal(Seq(Sum, Underscore, Grp(F.Id("k"), EqualToken, D(0)),
                Caret, Grp(F.Id("M")), Sp, Call("pb", F.Id("c"), F.Id("k"))), D(1))),
                "The finite expansion of the product of c i+(1−c i) gives total mass one. " +
                "The polynomial identity holds for arbitrary real parameters, including the empty vector.", DescribeRole.Theorem),
            Node("pb_perm", "Permutation invariance", Disp(Equal(Call("pb", Seq(F.Id("c"), Circ, Sp, F.Id("sigma")), F.Id("k")),
                Call("pb", F.Id("c"), F.Id("k")))),
                "For every permutation σ of Fin M, permuting the parameters preserves each mass. " +
                "The coefficient of degree k in the product of (c i)X+(1−c i) represents pb c k.", DescribeRole.Theorem),
            Node("pbRest", "The remaining coordinates", Disp(Equal(Call("pbRest", F.Id("c"), F.Id("i"), F.Id("j"), F.Id("k")),
                Call("pb", Call("zeroPair", F.Id("c"), F.Id("i"), F.Id("j")), F.Id("k")))),
                "zeroPair denotes the two function updates setting coordinates i and j to zero. " +
                "The resulting mass describes the sum of the remaining coordinates.", DescribeRole.Definition),
            Node("pb_remove_two", "Removal gives three-point convolution", Disp(Equal(Call("pb", F.Id("c"), F.Id("k")),
                Seq(F.Id("v0"), Sp, Call("r", F.Id("k")), Plus, F.Id("v1"), Sp, Call("r1", F.Id("k")),
                    Plus, F.Id("v2"), Sp, Call("r2", F.Id("k"))))),
                "For distinct i,j, put p=c i, q=c j and r=pbRest c i j. The three weights are " +
                "v₀=(1−p)(1−q), v₁=p(1−q)+q(1−p), v₂=pq. The shifted r₋₁(k) is r(k−1) " +
                "when 1≤k and zero otherwise; r₋₂ uses the corresponding guard 2≤k. " +
                "These guards prevent truncated natural subtraction from assigning spurious boundary mass. " +
                "The identity holds for arbitrary real parameters.", DescribeRole.Theorem),
            Node("InteriorT", "An interior T-transform", Disp(Equal(Call("InteriorT", F.Id("x"), F.Id("y")),
                Seq(Call("IsTTransform", F.Id("x"), F.Id("y")), Land, Sp,
                    Call("OpenCube", F.Id("x")), Land, Sp, Call("OpenCube", F.Id("y"))))),
                "OpenCube means every coordinate lies in (0,1). IsTTransform uses a convex combination " +
                "of the vector and a transposition of two coordinates.", DescribeRole.Definition),
            Node("le_of_interior_ttransform", "A stepwise criterion", Disp(Seq(
                Call("StepMonotone", F.Id("G")), Land, Sp, Call("OpenCube", F.Id("c")), Land, Sp,
                Call("OpenCube", F.Id("d")), Land, Sp, Call("moreMixed", F.Id("d"), F.Id("c")),
                Sp, Rightarrow, Sp, Call("G", F.Id("c")), Le, Call("G", F.Id("d")))),
                "StepMonotone G means G x≤G y for every InteriorT x y. Applying this premise " +
                "along the finite chain proves monotonicity under majorization for any real-valued G " +
                "on Fin M → ℝ.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance? provenance = null) =>
        Describe.Lean(DescribeId.Create("poisson-binomial-structure-" + name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance ?? AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
    private static Formula EqualToken => Eq;
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
}
