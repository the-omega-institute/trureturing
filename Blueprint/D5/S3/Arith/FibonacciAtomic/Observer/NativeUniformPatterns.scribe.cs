using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer;
internal sealed class NativeUniformPatternsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformPatterns.";
    private static DocumentBlock Entry(string n, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("nativeuniformpatterns-" + n.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + n), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform native pattern and frontier words", H("NativeUniformPatterns"), Blocks(
            Paragraph(Text("A fixed token language represents Boolean leaves, pairing and reached frontier placeholders. The depth-indexed native Pattern and dependent Frontier carriers are erased only through exact reconstruction equations. No source tree or feasible source witness enters the factories. Depth and class count are arbitrary natural numbers. The factories preserve the existing enumeration order, early leaves, depth-zero frontier and the zero-class vector.")),
            Paragraph(Text("The matching Reg mirror proves typed whole-family reconstruction, variation, role sensitivity and actual observational dependence on the complete infinite domain. Contract source-selection coordinates and raw source-occurrence binding remain unregistered. No validated four-slot audit status is claimed.")),
            Entry("patternWord", "patternWord", "A native pattern becomes its structural preorder constructor word. Placeholder 0 denotes a frontier position rather than a source value; its actual address is recovered structurally.", DescribeRole.Definition),
            Entry("familyWord", "familyWord", "The pattern family is represented by a finite vector in the unchanged sorted old-class order.", DescribeRole.Definition),
            Entry("uniform_pattern_words", "uniform pattern words", "One primitive recursive patternWords factory, before the depth quantifier, equals patternList d mapped through patternWord for every d. This is consumed by the uniform family factory.", DescribeRole.Theorem),
            Entry("uniform_frontier_words", "uniform frontier words", "One primitive recursive parser frontierWords returns exactly frontierList p mapped through frontierAddress p for every native depth pattern. Its fold equation is proved by structural induction. The actual variable-table factory consumes this result.", DescribeRole.Theorem),
            Entry("uniform_pattern_families", "uniform pattern families", "One primitive recursive vector factory on class count and depth returns exactly allPatterns C d mapped through familyWord. A dependent List.pi enumeration equation proves fidelity to the native family. The common-input cell materializer consumes this result.", DescribeRole.Theorem))));
}
