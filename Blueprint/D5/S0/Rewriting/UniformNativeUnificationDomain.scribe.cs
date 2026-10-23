using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S0.Rewriting;
internal sealed class UniformNativeUnificationDomainDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S0/Rewriting/UniformNativeUnificationDomain.";
    private static DocumentBlock Entry(string n, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create("uniformnativeunification-" + n.Replace(".", "-").Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + n.Split('.')[^1]), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), role);
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Original-domain native unification", H("UniformNativeUnificationDomain"), Blocks(
            Paragraph(Text("A solver input is a natural-number domain size together with an ordered finite list of equations between finite binary trees. Leaves carry Boolean constants or natural-number variable indices. The solver returns outer none exactly when an occurring index lies outside the declared domain. A well-formed native failure returns some none. Success returns some of some of the original-domain bindings, in ascending index order, with the fully composed native substitution applied to each bound original variable.")),
            Paragraph(Text("The domain includes zero variables, empty equations, arbitrary finite trees, contradictions, aliases to unbound variables and every malformed finite input. These unification results alone do not construct a history materializer, a source-free service criterion or a stationary original service run.")),
            Entry("liftTerm", "Original index embedding", "The embedding changes each Fin index to its natural-number value and preserves Boolean leaves and ordered binary constructors.", DescribeRole.Definition),
            Entry("liftEquations", "Ordered equation embedding", "Each equation is embedded without changing the list order, its two sides or repeated variable occurrences.", DescribeRole.Definition),
            Entry("inRange", "Occurrence range check", "Every variable occurrence must be strictly below the declared domain size. Boolean leaves are always in range; both children of a binary node must be in range.", DescribeRole.Definition),
            Entry("lowerTerm", "Finite-domain reconstruction", "Every in-range natural-number variable becomes its original Fin index. Any out-of-range occurrence rejects the entire term.", DescribeRole.Definition),
            Entry("lowerEquations", "Finite-domain equation reconstruction", "Reconstruction retains all equation and constructor order and rejects any malformed occurrence in either side of any equation.", DescribeRole.Definition),
            Entry("project", "Ascending native action projection", "The native key set filters the ascending original Fin domain. Each retained key is paired with its fully substituted native action, decoded into finite terms and embedded back into natural-number indices.", DescribeRole.Definition),
            Entry("F", "Total uniform solver", "The function rejects malformed finite inputs and otherwise executes the exact native unifier from its empty substitution. Native failure and native success remain distinct from malformed input.", DescribeRole.Definition),
            Entry("exact_native", "Universal native correspondence", "For every domain size and every finite Fin-indexed equation list, the solver on the index embedding equals the exact native result projection. The equality uses the native solver's own branch and fully composed substitution action.", DescribeRole.Theorem),
            Entry("rejection_exact", "Exact malformed-input rejection", "For every natural-number domain size and every finite Nat-indexed equation list, the outer result is none if and only if at least one occurring index is outside the domain. A native unification failure never produces outer rejection.", DescribeRole.Theorem),
            Entry("Code.nativeTerm", "Native tree coding", "Boolean leaves and ordered binary nodes use the existing native constructors. An ordinal variable uses the exact native finName of its natural-number index.", DescribeRole.Definition),
            Entry("lower_range", "Exact term reconstruction range", "For every domain size and finite term, reconstruction succeeds exactly when every variable occurrence is in range. The retained computability implementation uses this original helper to validate clipped terms.", DescribeRole.Theorem),
            Entry("lower_equations_range", "Exact equation reconstruction range", "For every domain size and ordered finite equation list, reconstruction succeeds exactly when both sides of every equation are in range. The retained encoded solver uses this original helper for its malformed-input branches.", DescribeRole.Theorem))));
}
