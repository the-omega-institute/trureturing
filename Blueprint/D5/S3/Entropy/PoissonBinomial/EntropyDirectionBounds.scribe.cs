using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy.PoissonBinomial;

internal sealed class EntropyDirectionBoundsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Entropy/PoissonBinomial/EntropyDirectionBounds.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A logarithmic divided-difference bound and the entropy derivative of a finite three-point convolution.",
        H("Entropy Direction Bounds"),
        Blocks(
            Node("log_divided_difference_lower", "The logarithmic slope bound", Disp(Seq(
                D(0), Lt, F.Id("B"), Lt, F.Id("A"), Lt, D(1), Sp, Rightarrow, Sp,
                ProductSlope(), Le, SecantSlope())),
                "For 0<B<A<1, the secant slope of log is at least −log(AB)/(1−AB). " +
                "This divided-difference estimate is the bound A1 for the binary-entropy part of the pairwise comparison. " +
                "Its proof uses log x≤x−1 to control the derivative of log x(1+x)/(1−x).",
                DescribeRole.Theorem),
            Node("neg_log_product_lt_div", "The intermediate slope dominates the logarithm", Disp(Seq(
                D(0), Lt, F.Id("B"), Lt, F.Id("A"), Lt, D(1), Sp, Rightarrow, Sp,
                Minus, Call("log", Seq(F.Id("A"), Sp, F.Id("B"))), Lt, ProductSlope())),
                "For the same range, 0<AB<1 and −log(AB)>0, so division by 1−AB strictly " +
                "increases −log(AB). This connects the convolution estimate to the divided-difference estimate.",
                DescribeRole.Theorem),
            Node("threePointMass", "A three-point convolution direction", Disp(new Formula.Relation(
                Call("threePointMass", F.Id("r"), F.Id("v0"), F.Id("v1"), F.Id("v2"), F.Id("t"), F.Id("k")),
                FormulaRelationOperator.Equal, Seq(
                    Open, F.Id("v0"), Plus, F.Id("t"), Close, Call("r0", F.Id("k")), Plus,
                    Open, F.Id("v1"), Minus, D(2), F.Id("t"), Close, Call("r1", F.Id("k")), Plus,
                    Open, F.Id("v2"), Plus, F.Id("t"), Close, Call("r2", F.Id("k"))))),
                "For r : Fin n → ℝ, r₀,r₁,r₂ denote its zero-extended shifts by zero, one and two. " +
                "The output is indexed by Fin(n+2). The real parameter t perturbs the weights in the direction " +
                "(1,−2,1), preserving their sum.", DescribeRole.Definition),
            Node("three_point_entropy_direction_bound", "Entropy derivative and upper bound", Disp(Seq(
                Call("HasDerivAt", F.Id("H"), F.Id("d"), D(0)), Land, Sp, F.Id("d"), Le,
                Minus, Call("log", Seq(F.Id("v0"), Sp, F.Id("v2"))))),
                "Assume r is nonnegative with total mass one, v₀,v₁,v₂ are positive and sum to one. " +
                "Let Q=threePointMass r v₀ v₁ v₂ 0 and H(t)=Σₖ −Qₜ(k) log Qₜ(k). " +
                "Then H has derivative d=Σⱼ r j[2 log Q(j+1)−log Q(j)−log Q(j+2)] at zero, " +
                "and d≤−log(v₀v₂). The indices are the three canonical Fin embeddings. " +
                "The middle embedding is injective, allowing its mass sum to be bounded by the total output mass. " +
                "The estimate log x≤x−1 controls the middle term, and Q(j)≥v₀r j and Q(j+2)≥v₂r j " +
                "control the outer terms. Zero entries of r are permitted. If an output mass vanishes, all three " +
                "contributing shifted masses vanish and that entropy summand is identically zero in t; " +
                "no derivative of −x log x at zero is assumed.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("entropy-direction-" + name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
    private static Formula ProductSlope() => new Formula.Fraction(
        Seq(Minus, Call("log", Seq(F.Id("A"), Sp, F.Id("B")))),
        Seq(D(1), Minus, F.Id("A"), Sp, F.Id("B")));
    private static Formula SecantSlope() => new Formula.Fraction(
        Seq(Call("log", F.Id("A")), Minus, Call("log", F.Id("B"))), Seq(F.Id("A"), Minus, F.Id("B")));
}
