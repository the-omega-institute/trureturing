using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer;
internal sealed class NativeUniformAnalysisDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformAnalysis.";
    private static DocumentBlock Entry(string n, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("nativeuniformanalysis-" + n.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + n), H(n), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "NativeUniformAnalysis", H("NativeUniformAnalysis"), Blocks(
            Paragraph(Text("The exact serialization retains every raw pattern cell, its original variable table, feasibility, symbolic exterior, reached addresses, ordered pair plans, pass flag and summed template cost. The whole bundle preserves all four native summary fields and K0 = 2*k*(2^d-1) + maximum feasible-cell template cost. Empty sums and no feasible cells use the original native zero conventions.")),
            Entry("templateLeaves", "Count Boolean leaves in a template word, matching the native ground-template cost rather than the number of constructor tokens.", DescribeRole.Definition),
            Entry("codedCellBudget", "Sum every stored binding template cost over the ordered pair plans, retaining repeated bindings.", DescribeRole.Definition),
            Entry("exteriorHasVariable", "Test whether the symbolic exterior still contains any residual ordinal variable.", DescribeRole.Definition),
            Entry("materializeCell", "Retain the pattern words, variable keys, finite-history feasibility flag, exact symbolic exterior and reached-address order, pair codes, pass flag and template budget. The synthetic history filling assigns the fixed Boolean leaf to each residual variable; old legality tests the entire disequality list.", DescribeRole.Definition),
            Entry("nativeCellCode", "The reference serialization retains the native feasible flag, symbolic exterior, ordered reached addresses, pair plans, pass flag and full template budget for each raw cell.", DescribeRole.Definition),
            Entry("nativeAnalysisCode", "Retain all raw cells in their native order together with the four existing analyze fields and the native K0 value. This reference bundle has no epoch argument.", DescribeRole.Definition),
            Entry("materializeAnalysis", "Parse the common input and enumerate its complete raw cell list. Retain every cell, filter by computed feasibility, and aggregate raw and feasible counts, the universal pass flag and the maximum template budget. The budget projection is twice the class count times two to the required depth minus one, plus the template maximum. Malformed encodings return none. Contradictory histories remain valid computational inputs.", DescribeRole.Definition),
            Entry("materialize_analysis_exact", "Every encoded common input yields exactly the full original native analysis serialization and K0, uniformly in the unused epoch N. All raw cells remain present with their feasibility flags.", DescribeRole.Theorem))));
}
