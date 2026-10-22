using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin;

internal sealed class Activation5040InventoryDocument : IScribeDocumentDefinition
{
    // The Lean namespace extends the actual compiled NPC5 owner, while this
    // document owns only the standalone Activation5040Inventory module.
    private const string Prefix = "D5/S3/Arith/Robin/Activation5040Inventory.";
    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula N(long n) => new Formula.Number(n);
    private static Formula Call(string n, params Formula[] xs) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(n), [.. xs]);
    private static Formula All(string v, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(v), Nat, body);
    private static Formula Equal(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula Le(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.LessThanOrEqual, y);
    private static Formula Lt(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.LessThan, y);
    private static Formula And(Formula x, Formula y) =>
        new Formula.Logic(x, FormulaLogicOperator.And, y);
    private static Formula Implies(Formula x, Formula y) =>
        new Formula.Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula Iff(Formula x, Formula y) =>
        new Formula.Logic(x, FormulaLogicOperator.Iff, y);
    private static Formula Par(Formula f) => Seq(Left, Open, f, Right, Close);
    private static Formula Case(Formula c, Formula yes, Formula no) =>
        Par(Seq(Operatorname, Grp(F.Id("if")), Sp, Par(c), Sp,
            Operatorname, Grp(F.Id("then")), Sp, yes, Sp,
            Operatorname, Grp(F.Id("else")), Sp, no));
    private static Formula Q => F.Id("q11");
    private static Formula P => F.Id("p");
    private static Formula K => F.Id("k");
    private static Formula E => Call("targetExponent5040", P);
    private static Formula W => Call("targetExponent55440", P);
    private static Formula M => Call("goldenLayerMarginal", P, K);
    private static Formula PrimeLayer(Formula body) =>
        All("p", All("k", Implies(Call("Prime", P), Implies(Le(N(1), K), body))));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The exact strict and weak inventories at the first eleven-layer price.",
        H("The q11 inventory"),
        Blocks(
            Paragraph(Text("All p and k binders range over all natural numbers. Prime is Nat.Prime. The imported goldenLayerMarginal(p,k) is log((1-(1/p)^(k+1))/(1-(1/p)^k))/log(p). optimalLayerCount counts every strictly profitable positive prime layer, and weakLayerCount includes equality. strictInteger and maximalInteger are the actual imported strict-count integer and full weak-layer product, with their original total definitions. No optimizer domain is replaced by a finite menu.")),
            Describe.Lean(
                DescribeId.Create("activation5040-q11"),
                DeclarationHandle.Create(Prefix + "q11"), H("q11"),
                StatementSource.FromAuthor(Disp(Equal(Q, Call("goldenLayerMarginal", N(11), N(1))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This is exactly log(12/11)/log(11), which is positive. The proof establishes 1/28 < q11 < 1/25 using exact rational powers and real-log order."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("activation5040-target5040"),
                DeclarationHandle.Create(Prefix + "targetExponent5040"), H("The strict exponents"),
                StatementSource.FromAuthor(Disp(All("p", Equal(E,
                    Case(Equal(P, N(2)), N(4), Case(Equal(P, N(3)), N(2),
                        Case(Equal(P, N(5)), N(1), Case(Equal(P, N(7)), N(1), N(0))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The piecewise function is defined on every natural p; it is the factorization of 5040, including zero and one directions."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("activation5040-target55440"),
                DeclarationHandle.Create(Prefix + "targetExponent55440"), H("The weak exponents"),
                StatementSource.FromAuthor(Disp(All("p", Equal(W, Case(Equal(P, N(11)), N(1), E))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The first eleven-layer is the only additional layer."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("activation5040-strict-count"),
                DeclarationHandle.Create(Prefix + "optimalLayerCount_q11"), H("Every strict count"),
                StatementSource.FromAuthor(Disp(All("p", Equal(Call("optimalLayerCount", Q, P), E)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Reuse: golden_resource_unique_optimum at 1/25, optimal_layer_count_spec, positive_layers_eq_count_interval, golden_layer_marginal_le_inv_pow and golden_layer_strict_decrease. Selected final layers are transported from 1/25. Exact power-28 comparisons exclude the next 2,3,5,7 layers. For every prime p at least 13, inverse/log bounds strictly exclude the first layer, then strict decrease excludes every higher layer. The threshold architecture and log-comparison proof adapt the private layer_threshold_separation_5040 proof in GoldenResource5040PriceInterval; private declarations are not imported as public API. Nonprime counts and target exponents are both proved zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("activation5040-weak-count"),
                DeclarationHandle.Create(Prefix + "weakLayerCount_q11"), H("Every weak count"),
                StatementSource.FromAuthor(Disp(All("p", Equal(Call("weakLayerCount", Q, P), W)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual weak prefix-count API includes the first eleven-layer at equality and excludes every higher eleven-layer by strict decrease. Nonprime directions, including p=0 and p=1, have count zero."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("activation5040-strict-integer"),
                DeclarationHandle.Create(Prefix + "strictInteger_q11"), H("The actual strict integer"),
                StatementSource.FromAuthor(Disp(Equal(Call("strictInteger", Q), N(5040)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Factorization injectivity identifies the actual strictInteger from its public strictInteger_counts API and the all-direction count theorem. This asserts an actual integer equality."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("activation5040-maximal-integer"),
                DeclarationHandle.Create(Prefix + "maximalInteger_q11"), H("The actual maximal integer"),
                StatementSource.FromAuthor(Disp(Equal(Call("maximalInteger", Q), N(55440)))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Factorization injectivity and maximalInteger_spec identify the full weak-layer product: 2^4 * 3^2 * 5 * 7 * 11 = 55440."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("activation5040-strict-layer"),
                DeclarationHandle.Create(Prefix + "q11_strict_layer_iff"), H("All strict layers"),
                StatementSource.FromAuthor(Disp(PrimeLayer(Iff(Lt(Q, M), Le(K, E))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every prime and every positive layer, exact set membership and the proved count equality give both implications."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("activation5040-weak-layer"),
                DeclarationHandle.Create(Prefix + "q11_weak_layer_iff"), H("All weak layers"),
                StatementSource.FromAuthor(Disp(PrimeLayer(Iff(Le(Q, M), Le(K, W))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("This quantifies over the same unrestricted prime and positive layer domain and includes every equality layer."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("activation5040-equality-layer"),
                DeclarationHandle.Create(Prefix + "q11_equality_layer_iff"), H("The complete equality tie"),
                StatementSource.FromAuthor(Disp(PrimeLayer(Iff(Equal(M, Q), And(Equal(P, N(11)), Equal(K, N(1))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Weak membership and failure of strict membership force exactly p=11,k=1. This is the complete equality classification, without a tie-free hypothesis. The bounded Robin application belongs to the separate reuse task. All-price EndpointRobinEstimates, NPC7 signed floor and global coverage remain open; no complete Robin or RH assertion follows here."))),
                DescribeRole.Theorem)
        )));
}
