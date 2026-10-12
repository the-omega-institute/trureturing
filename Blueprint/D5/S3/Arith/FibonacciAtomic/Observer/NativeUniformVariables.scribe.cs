using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer;
internal sealed class NativeUniformVariablesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Observer/NativeUniformVariables.";
    private static DocumentBlock Entry(string n, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("nativeuniformvariables-" + n.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + n), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uniform structural native variable tables", H("NativeUniformVariables"), Blocks(
            Paragraph(Text("The actual variable key is the old numeric class name together with its reached relative frontier address. The finite cursor consumes class-ordered pattern words and accumulates frontier keys in the native order, then applies the native rightmost dedup convention. Injectivity follows from the existing frontier reconstruction law. No hash bucket layout or arbitrary String encoding is supplied. This finite first-order stage is subordinate to the full native Theorem 74.4: solver simulation, exact criterion and K0 computation, and the joint controller evaluator remain required.")),
            Paragraph(Text("The matching Reg mirror proves typed whole-family reconstruction, variation, role sensitivity and actual observational dependence on the complete infinite domain. Contract source-selection coordinates and raw source-occurrence binding remain unregistered. No validated four-slot audit status is claimed.")),
            Entry("variableKey", "variableKey", "Encode a dependent native frontier variable by its original old-class name and actual relative frontier address.", DescribeRole.Definition),
            Entry("materializeVariableCells", "materializeVariableCells", "The decoded common-input cell factory supplies each complete pattern vector with its exact structural variable table. No source witness, hidden tree bound or closure code is an input.", DescribeRole.Definition),
            Entry("uniform_variable_table", "uniform variable table", "One primitive recursive variableKeys factory on fixed finite name and pattern-word lists returns exactly variableList eta mapped through variableKey for every native cell. The exact frontier parser, explicit cursor invariant and key injectivity preserve order and dedup behavior. The common-input variable-cell materializer consumes it.", DescribeRole.Theorem),
            Entry("uniform_variable_materializer", "uniform variable materializer", "One primitive recursive first-order algorithm, before all common-input quantifiers, returns the exact required depth, original class names and all native pattern families paired with their exact structural variable tables. For every variable in every cell, its table index agrees with the ordinal of the actual unary finName in presentation. The index equation directly uses the pinned findIdx_map equation and the injectivity of structural keys. This closes uniform cell and variable enumeration and native variable-name fidelity. Solver simulation, uniform effectiveness of analyze and K0, and the joint evaluator of controller(compileService) remain required.", DescribeRole.Theorem))));
}
