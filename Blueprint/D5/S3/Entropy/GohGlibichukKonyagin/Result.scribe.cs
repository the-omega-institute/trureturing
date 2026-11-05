using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy.GohGlibichukKonyagin;

internal sealed class ResultDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Entropy/GohGlibichukKonyagin/Result.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Entropy/goh2026entropicenergy");
    private const string Quotation = @"**Conjecture 15 (Entropic Glibichuk–Konyagin lemma).** There is an integer $k\geq 3$ such that the following holds. Let $X$ be a random variable taking values in $\mathbf F_p$ for a prime $p$. Then for independent copies $X_1,\ldots,X_k,X'_1,\ldots,X'_k$ of $X$, we have
$$H\{X_1X'_1+\cdots+X_kX'_k\} \geq \min(2H\{X\},\log p)-1. \qquad (89)$$";
    private const string Following = @"In the original additive-combinatorial version of this statement, $k$ can be taken to be $3$, but any fixed integer is enough for our purposes.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A zero atom and a uniform component refute the unconditional entropic sum-product assertion for every fixed k.",
        H("The entropic Glibichuk–Konyagin conjecture"), Blocks(
            Entry("delta", Pq(All("a", G, Eq(C("delta", V("a")), Ite(Eq(V("a"), D(0)), D(1), D(0))))), "The point mass at zero on the finite field.", DescribeRole.Definition),
            Entry("spike", Pq(Qr("t", All("a", G, Eq(C("spike", V("t"), V("a")), Add(Mul(Sub(D(1), V("t")), Ite(Eq(V("a"), D(0)), D(1), D(0))), Div(V("t"), V("p"))))))), "For prime p and 0≤t≤1 this is (1−t)δ₀+tU_p. The uniform mass is 1/p at every element.", DescribeRole.Definition),
            Entry("conv", Pq(All("f", LawType, All("g", LawType, All("z", G, Eq(C("conv", V("f"), V("g"), V("z")), SumOver("a", G, Mul(C("f", V("a")), C("g", Sub(V("z"), V("a")))))))))), "This is the pinned Mathlib DiscreteConvolution.addRingConvolution, transported through the finite-field fiber equivalence to the displayed finite sum.", DescribeRole.Definition),
            Entry("conv_eq_sum", Pq(All("f", LawType, All("g", LawType, All("z", G, Eq(C("conv", V("f"), V("g"), V("z")), SumOver("a", G, Mul(C("f", V("a")), C("g", Sub(V("z"), V("a")))))))))), "The equivalence a↦(a,z−a) identifies the additive fiber with the field. Reindexing the upstream convolution sum gives the finite sum used by conv_spike and conv_mul."),
            Entry("mulLaw", Pq(All("f", LawType, All("z", G, Eq(C("mulLaw", V("f"), V("z")), SumOver("a", G, SumOver("b", G, Ite(Eq(Mul(V("a"), V("b")), V("z")), Mul(C("f", V("a")), C("f", V("b"))), D(0)))))))), "The weights f(a)f(b) express independence of the two copies before multiplication.", DescribeRole.Definition),
            Entry("iterLaw", Pq(All("f", LawType, And(Eq(C("iterLaw", D(0), V("f")), C("delta")), All("n", N, Eq(C("iterLaw", Add(V("n"), D(1)), V("f")), C("conv", C("mulLaw", V("f")), C("iterLaw", V("n"), V("f")))))))), "The zero-fold sum is zero; each further step adds an independent product.", DescribeRole.Definition),
            Entry("sumLaw", Pq(All("n", N, All("f", LawType, All("z", G, Eq(C("sumLaw", V("n"), V("f"), V("z")), DoubleProductPush(V("n"), V("f"), V("z"))))))), "The finite pushforward is reused from Entropy.Forgetting.CapacityMonotone. Its domain is a pair of functions Fin n→ZMod p, with product weights for the 2n independent copies. The standard equivalence arrowProdEquivProdArrow sends a tuple of pairs to its two projection functions; sum_spike uses its sum_comp identity to prove equality with the tuple-of-pairs expression in iter_product. The equivalence preserves both the sum of products and every product weight.", DescribeRole.Definition),
            Entry("Hbits", Pq(All("f", LawType, Eq(C("Hbits", V("f")), Div(Entropy(V("f")), Log(D(2)))))), "The reused D5.S3.Entropy.MaxEntropy.shannonEntropy is in nats. Division by log 2 expresses exactly the paper's bits.", DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("goh-gk-claim"), DeclarationHandle.Create(Prefix + "claim"), H("The complete unconditional assertion"), StatementSource.FromAuthor(Disp(Eq(V("claim"), ClaimBody()))), AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text("§6, Conjecture 15, equation (89), arXiv:2406.18798v4:")), VerbatimQuote(Quotation), VerbatimQuote(Following), Paragraph(Text("The paper uses binary logarithms and discrete random variables. On a finite field every discrete probability law is a nonnegative normalized real mass function. There is no further restriction on this mass function."))), DescribeRole.Definition),
            Entry("card_pos", Pq(Lt(D(0), V("p"))), "A prime has positive real cardinality; all denominators p are nonzero."),
            Entry("spike_sum", Pq(Qr("t", Eq(SumOver("a", G, C("spike", V("t"), V("a"))), D(1)))), "The signed affine mixture has total mass one for every real t."),
            Entry("spike_law", Pq(Qr("t", Imp(UnitInterval(V("t")), Law(C("spike", V("t")))))), "The zero-atom mixture is a probability law, including both endpoints t=0 and t=1."),
            Entry("spike_entropy", Pq(Qr("t", Imp(UnitInterval(V("t")), And(Le(Mul(V("t"), Log(V("p"))), Entropy(C("spike", V("t")))), Le(Entropy(C("spike", V("t"))), Add(Log(D(2)), Mul(V("t"), Log(V("p"))))))))), "The finite mixture entropy bracket gives the lower bound from the uniform component and the upper bound by adding the at-most-log-2 entropy of the Boolean mixing weight. Point-mass and uniform entropy are supplied by the existing equality characterizations."),
            Entry("conv_spike", Pq(Qr("t u", Eq(C("conv", C("spike", V("t")), C("spike", V("u"))), C("spike", Sub(Add(V("t"), V("u")), Mul(V("t"), V("u"))))))), "Translation preserves U_p, so convolution multiplies the complementary zero-atom weights. The identity is algebraic and holds for all real t,u."),
            Entry("mul_spike", MulSpikeBody(), "For a nonzero first coordinate, multiplication is a permutation of the field. Separating the zero coordinate yields the exact weight t²(p−1)/p of the uniform part of the product law."),
            Entry("conv_mul", Pq(All("f", LawType, All("g", LawType, All("z", G, Eq(C("conv", C("mulLaw", V("f")), V("g"), V("z")), SumOver("a", G, SumOver("b", G, Mul(Mul(C("f", V("a")), C("f", V("b"))), C("g", Sub(V("z"), Mul(V("a"), V("b")))))))))))), "Summing over the intermediate product value eliminates the product indicator."),
            Entry("iter_product", Pq(All("n", N, All("f", LawType, All("z", G, Eq(C("iterLaw", V("n"), V("f"), V("z")), ProductPush(V("n"), V("f"), V("z"))))))), "Induction using the bijection between an (n+1)-tuple and its head and tail proves equality with the full independent product-law pushforward. This equality connects the recursive computation to sumLaw."),
            Entry("sum_spike", SumSpikeBody(), "The independent sum of n products has uniform weight 1−(1−s)^n, with s=t²(p−1)/p. The product-law identity and the convolution identity prove this for every n."),
            Entry("weight_bounds", Pq(All("k", N, Imp(Le(D(3), V("k")), WeightBounds()))), "At t=1/k, Bernoulli's inequality gives 0≤r≤ks<1/k, while both t and s lie in [0,1]."),
            Entry("violation", Pq(All("k", N, Imp(Le(D(3), V("k")), Imp(Lt(Pow(D(2), Mul(D(2), V("k"))), V("p")), Violation())))), "Writing L=log₂ p, the input entropy is at least L/k and the sum entropy at most 1+L/k. Since 2L/k≤L and L>2k, the margin in (89) is strictly greater than zero. This holds for every k≥3 and every prime above the displayed threshold."),
            Describe.Lean(DescribeId.Create("goh-gk-result"), DeclarationHandle.Create(Prefix + "result"), H("Refutation for every proposed fixed integer"), StatementSource.FromAuthor(Disp(Seq(F.Neg, Sp, V("claim")))), AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text("For any proposed k, the infinitude of primes supplies a prime p>2^(2k). The nonnegative normalized spike law with t=1/k contradicts the claimed inequality by the strict violation. There are infinitely many primes above every fixed threshold. The conclusion proves that Conjecture 15 cannot supply the paper's route to Conjecture 14; Conjecture 14 itself remains open."))), DescribeRole.Theorem, openProblemResolutionClaim: new OpenProblemResolutionClaim(ProblemSlugRef.Create("goh-2026-entropic-glibichuk-konyagin"), ResolutionKind.Refuted))
        )));

    private static DocumentBlock VerbatimQuote(string source) => Paragraph(Text("<blockquote><pre>" + source.Replace("&", "&amp;").Replace("<", "&lt;").Replace(">", "&gt;").Replace("$", "&#36;").Replace("\n", "&#10;") + "</pre></blockquote>"));
    private static DocumentBlock Entry(string name, Formula statement, string text, DescribeRole role = DescribeRole.Theorem) => Describe.Lean(
        DescribeId.Create("goh-gk-" + name.Replace('_', '-').ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
        H(name.Replace('_', ' ')), StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(text))), role);
    private static Formula V(string s) => F.Id(s);
    private static Formula R => Seq(Mathbb, Sp, Grp(V("R")));
    private static Formula N => Seq(Mathbb, Sp, Grp(V("N")));
    private static Formula G => C("ZMod", V("p"));
    private static Formula LawType => new Formula.TypeArrow(G, R);
    private static Formula All(string n, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), type, body);
    private static Formula Ex(string n, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(n), type, body);
    private static Formula Pq(Formula body) => All("p", N, Imp(C("Nat.Prime", V("p")), body));
    private static Formula Qr(string names, Formula body) { foreach (var s in names.Split(' ').Reverse()) body = All(s, R, body); return body; }
    private static Formula P(Formula a) => Seq(Open, a, Close);
    private static Formula C(string name, params Formula[] args) { var parts = new List<Formula>(); foreach (var word in name.Split('.')) { if (parts.Count > 0) parts.Add(Dot); parts.Add(V(word)); } return new Formula.Apply(Seq(Operatorname, Sp, Grp([.. parts])), [.. args]); }
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula Sub(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Subtract, b);
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Div(Formula a, Formula b) => new Formula.Fraction(a, b);
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(P(a), b);
    private static Formula Sq(Formula a) => Pow(a, D(2));
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(P(a), FormulaLogicOperator.Implies, P(b));
    private static Formula And(Formula a, Formula b) => new Formula.Logic(P(a), FormulaLogicOperator.And, P(b));
    private static Formula Ite(Formula c, Formula a, Formula b) => C("ite", c, a, b);
    private static Formula Log(Formula a) => C("Real.log", a);
    private static Formula Entropy(Formula a) => C("shannonEntropy", a);
    private static Formula SumOver(string v, Formula type, Formula body) => Seq(F.Sum, Underscore, Grp(Seq(V(v), Colon, Sp, type)), Sp, P(body));
    private static Formula ProdOver(string v, Formula type, Formula body) => Seq(F.Prod, Underscore, Grp(Seq(V(v), Colon, Sp, type)), Sp, P(body));
    private static Formula UnitInterval(Formula t) => And(Le(D(0), t), Le(t, D(1)));
    private static Formula Law(Formula f) => And(All("a", G, Le(D(0), new Formula.Apply(f, [V("a")]))), Eq(SumOver("a", G, new Formula.Apply(f, [V("a")])), D(1)));
    private static Formula PairValue(string i, byte side) => Seq(P(C("v", V(i))), Dot, D(side));
    private static Formula ProductPush(Formula n, Formula f, Formula z) => SumOver("v", new Formula.TypeArrow(C("Fin", n), Seq(G, Times, G)), Ite(Eq(SumOver("i", C("Fin", n), Mul(PairValue("i", 1), PairValue("i", 2))), z), ProdOver("i", C("Fin", n), Mul(new Formula.Apply(f, [PairValue("i", 1)]), new Formula.Apply(f, [PairValue("i", 2)]))), D(0)));
    private static Formula DoubleProductPush(Formula n, Formula f, Formula z) => SumOver("x", new Formula.TypeArrow(C("Fin", n), G), SumOver("y", new Formula.TypeArrow(C("Fin", n), G), Ite(Eq(SumOver("i", C("Fin", n), Mul(C("x", V("i")), C("y", V("i")))), z), ProdOver("i", C("Fin", n), Mul(new Formula.Apply(f, [C("x", V("i"))]), new Formula.Apply(f, [C("y", V("i"))]))), D(0))));
    private static Formula MulSpikeBody() => Pq(Qr("t", Eq(C("mulLaw", C("spike", V("t"))), C("spike", Div(Mul(Sq(V("t")), Sub(V("p"), D(1))), V("p"))))));
    private static Formula SumSpikeBody() => Pq(Qr("t", All("n", N, Eq(C("sumLaw", V("n"), C("spike", V("t"))), C("spike", Sub(D(1), Pow(Sub(D(1), Div(Mul(Sq(V("t")), Sub(V("p"), D(1))), V("p"))), V("n"))))))));
    private static Formula T => Div(D(1), V("k"));
    private static Formula S => Div(Mul(Sq(T), Sub(V("p"), D(1))), V("p"));
    private static Formula W => Sub(D(1), Pow(Sub(D(1), S), V("k")));
    private static Formula WeightBounds() => And(Le(D(0), T), And(Le(T, D(1)), And(Le(D(0), S), And(Le(S, D(1)), And(Le(D(0), W), And(Le(W, Mul(V("k"), S)), Lt(Mul(V("k"), S), T)))))));
    private static Formula Violation() => Lt(C("Hbits", C("sumLaw", V("k"), C("spike", T))), Sub(C("min", Mul(D(2), C("Hbits", C("spike", T))), C("Real.logb", D(2), V("p"))), D(1)));
    private static Formula ClaimBody() => Ex("k", N, And(Le(D(3), V("k")), Pq(All("mu", LawType, Imp(Law(V("mu")), Le(Sub(C("min", Mul(D(2), C("Hbits", V("mu"))), C("Real.logb", D(2), V("p"))), D(1)), C("Hbits", C("sumLaw", V("k"), V("mu")))))))));
}
