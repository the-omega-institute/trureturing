using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Spacetime;

internal sealed class RegionFilterQExpressibilityDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/Spacetime/RegionFilterQExpressibility.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A region has a native charge expression exactly when its past tail is uniform.",
        H("Region Filters and Uniform Past Tails"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("tail"), DeclarationHandle.Create(Prefix + "Tail"),
                H("One threshold works for every position"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A region is a set of integer time and integer spatial-triple pairs. TailAt R c says that, for every position p and every t,t' strictly below c, membership of (t,p) and (t',p) agrees. Tail R asserts the existence of such a single integer c. The threshold is independent of position."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("charge-expression"),
                DeclarationHandle.Create(Prefix + "QExpressible"),
                H("A fixed total word computes filtered charge"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("QExpressible R means that one fixed finite native one-hole word succeeds on every balanced rich input and returns the sum of signs of its selected events lying in R. The word may use arbitrary fixed balanced parameters, both binary slots, all native filters, complement and integer shifts."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("total-word-saturation"),
                DeclarationHandle.Create(Prefix + "total_word_saturation"),
                H("A total word saturates below one common time"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every fixed native word total on all balanced rich inputs, there is an integer c such that every position p and every pair t,t' below c admit two legal inputs with equal final optional charge. Their archives have the same literal event names, order, current region and selection. Only the time of the unique selected positive event differs, from t to t'; its position is p and its source agrees. Common earlier and later archive events strictly enclose both times.")),
                    Paragraph(Text("Exact total-word normalization removes temporal composition. The finite family of pulled-back causal predicates before the first product supplies finitely many target attributes and a common lower time bound. A balanced star adds a current successor for each nonempty predicate, an unselected opposite-sign twin for every current contribution, and two common inactive endpoints. Every prefix filter therefore acts synchronously. A current correspondence preserves attributes, causal order and selection, without matching inactive archive attributes. Parallel composition transports it through a disjoint sum and generated product through current-parent pairs. At the first product in either slot, the exceptional time is below every current parent time in the fixed factor, so the maximum erases it from generated attributes. An empty current factor also satisfies this argument. Every subsequent temporal-free step preserves the current correspondence. If there is no product, matching selected signs give the same conclusion directly."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("tail-construction"),
                DeclarationHandle.Create(Prefix + "tail_construction_q"),
                H("A shifted unit factor realizes every tail region"),
                StatementSource.FromAuthor(TailConstructionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Let U be the canonical balanced representative with one selected positive event at time zero and position zero. Form X product T_k U and retain generated events with time n at least k+1 and (n-1,p) in R. The product time is max(t,k)+1 and its current region is an antichain, so the causal filter reads exactly R at max(t,k). When k is at most c-1, TailAt R c identifies this membership with R at the original t. The identity holds for every balanced rich input X."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("classification"),
                DeclarationHandle.Create(Prefix + "q_expressible_iff_tail"),
                H("The exact charge-expressibility classification"),
                StatementSource.FromAuthor(ClassificationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Necessity applies total-word saturation to the expressing word. The unique selected positive point reads the two region membership bits, forcing their equality below one common c at every position. Sufficiency uses the shifted-unit construction with k=c-1. Neither direction restricts the region or the balanced input."))),
                DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(
            GidRef.Create("D5/S3/ConceptDynamics/Spacetime/TotalCopyNormalization")),
         DocumentEdge.Dependency.Create(
            GidRef.Create("D5/S3/ConceptDynamics/Spacetime/CoarseObservation"))]));

    private static Formula TailConstructionFormula() => Disp(Seq(
        Forall, Sp, F.Id("R"), Comma, Sp, F.Id("c"), Comma, Sp, F.Id("k"),
        Comma, Sp, F.Id("X"), Comma, Sp,
        Call("TailAt", F.Id("R"), F.Id("c")), Sp, Land, Sp,
        F.Id("k"), Sp, Le, Sp, Seq(F.Id("c"), Sp, Minus, Sp, Num(1)),
        Sp, Rightarrow, Sp,
        Call("q", Call("tailConstruction", F.Id("R"), F.Id("k"), F.Id("X"))),
        Sp, Eq, Sp, Call("regionReadout", F.Id("R"), F.Id("X")), Dot));

    private static Formula ClassificationFormula() => Disp(Seq(
        Forall, Sp, F.Id("R"), Comma, Sp,
        Call("QExpressible", F.Id("R")), Sp, Iff, Sp, Call("Tail", F.Id("R")), Dot));
}
