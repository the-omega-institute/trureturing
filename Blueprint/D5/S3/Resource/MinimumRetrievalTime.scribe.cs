using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Resource;

internal sealed class MinimumRetrievalTimeDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Resource/MinimumRetrievalTime.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/SparseCoding/barlev2026blockretrieval");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "An actual iid stopping-time bridge and a universal five-column obstruction refute the finite-length Pareto conjecture at file dimensions (1,2).",
        H("Minimum iid span retrieval and the finite-length Pareto obstruction"),
        Blocks(
            Definition("minimumTime", "Minimum recovery time",
                "The value is the least natural time satisfying the recovery predicate, or infinity if no such time exists."),
            Definition("uniformSamples", "Uniform iid physical-index sampling",
                "The measure is the infinite product of uniform probability measures on the finite nonempty physical column-index alphabet. Equal or zero columns do not change the alphabet."),
            Definition("prefixSpan", "Span after a finite prefix",
                "The prefix span is the linear span of columns at all sampled indices in positions strictly less than the given natural time."),
            Definition("recovered", "Whole-file recovery",
                "Recovery means inclusion of the entire target file submodule in the sampled prefix span."),
            Definition("retrievalTime", "Actual minimum file-retrieval stopping time",
                "The retrieval time is minimumTime applied to the prefix-span recovery predicate; it is not defined by an expectation formula."),
            Theorem("retrieval_time_probability_bridge", "Probability and expectation bridge",
                Equal(Expectation(F.Id("G"), F.Id("U")), Call("tailSum", F.Id("G"), F.Id("U"))),
                "For any field and module, finite nonempty measurable physical-index alphabet with measurable singletons, and file U included in the column span of G: retrievalTime is measurable; t<retrievalTime iff recovery has not occurred after t draws; the nonnegative integral equals the sum of these tail probabilities. Each tail is at most N(1-1/N)^t, every finite tail sum is bounded by the integral, the integral is finite, its real-valued stopping time is integrable, and its Bochner integral equals the toReal nonnegative integral. Here E denotes this actual integral, not a new definition of the stopping time."),
            Definition("oldAddress", "Old physical-index map",
                "The four physical indices map to basis indices 0,0,1,2."),
            Definition("oldColumns", "Old full-rank generator",
                "For any three-element basis, the columns are b0,b0,b1,b2, with both b0 copies retained as distinct indices."),
            Definition("oldFirstFile", "One-dimensional first file",
                "The first file is span{b0}."),
            Definition("oldSecondFile", "Two-dimensional second file",
                "The second file is span{b1,b2}."),
            Theorem("old_code_actual_expectations", "The old code has actual expectation pair (2,6)",
                new Formula.Logic(Equal(Expectation(F.Id("G0"), F.Id("U1")), D(2)),
                    FormulaLogicOperator.And, Equal(Expectation(F.Id("G0"), F.Id("U2")), D(6))),
                "For every three-element basis over any field, the old four columns span the whole module, the actual expected retrieval time of span{b0} is 2, and that of span{b1,b2} is 6."),
            Theorem("five_column_three_kernel_obstruction", "Arbitrary-index two-coupon obstruction",
                Less(D(6), Expectation(F.Id("G"), F.Id("U"))),
                "For any five physical columns, linear projection, and file containing two vectors with independent projections: if all projected columns outside two distinct arbitrary indices vanish and the file lies in the full column span, its actual expected retrieval time is greater than 6. The conclusion uses a nine-term lower tail sum; no column ordering or permutation premise is required."),
            Theorem("five_column_bad_pairs_obstruction", "Two intersecting failing pairs force expectation greater than two",
                Less(D(2), Expectation(F.Id("G"), F.Id("U"))),
                "For any five physical columns and three distinct indices common,left,right, if neither the common,left pair nor the common,right pair spans the file, while all columns together do, the actual expected retrieval time is greater than 2."),
            Theorem("five_column_projected_obstruction", "Independent projections and a third failing singleton",
                Less(D(2), Expectation(F.Id("G"), F.Id("U"))),
                "For any five physical columns and recoverable file containing a nonzero target killed by a linear projection: if two columns have independent projections and a third distinct column cannot alone span the target, the actual expected file-retrieval time is greater than 2."),
            Theorem("five_column_universal_obstruction", "Every full-rank successor fails weak Pareto domination",
                new Formula.Logic(Less(D(2), Expectation(F.Id("G"), F.Id("U1"))),
                    FormulaLogicOperator.Or, Less(D(6), Expectation(F.Id("G"), F.Id("U2")))),
                "For every field, module, three-element basis, and unrestricted five-column full-span generator G, either E(G,span{b0})>2 or E(G,span{b1,b2})>6. Project along b0, select two independent projected columns from full span, and split according to the existence of another nonzero projected column. This exhausts all generators, including zeros and duplicates."),
            Definition("firstCoordinateFile", "First coordinate file",
                "For field K and file dimensions s1,s2, this is the span of standard basis vectors whose Fin(s1+s2) indices have value less than s1."),
            Definition("secondCoordinateFile", "Second coordinate file",
                "For field K and file dimensions s1,s2, this is the span of standard basis vectors whose Fin(s1+s2) indices have value at least s1."),
            Definition("paretoCodeLengthMonotonicity", "Same-field weak Pareto length monotonicity",
                "For a fixed field K, quantify positive s1,s2 with max(s1,s2)>=2, every n>=s1+s2, and every indexed n-column matrix of rank s1+s2. Require an arbitrary (n+1)-column matrix over the same K of the same full rank whose actual expected retrieval times for both coordinate files are each at most those of the original matrix."),
            Definition("FiniteFieldModel", "The complete finite-field data",
                "A finite-field model contains an arbitrary carrier type, its field structure, and a Fintype structure. Quantification over this record preserves quantification over all finite fields and fixes the same field structure for both codes."),
            Node("claim", "Bar-Lev Conjecture 2",
                Disp(new Formula.Logic(F.Id("claim"), FormulaLogicOperator.Iff,
                    Seq(Open, ClaimFormula(), Close))),
                "The previous monotonicity property is asserted for every finite field structure. Both file sizes are positive; k=s1+s2, n>=k, and max(s1,s2)>=2. Expectations use actual minimum iid uniform-with-replacement span recovery. The successor is unrestricted and retains all physical zero and duplicate indices.",
                DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", "The complete literal conjecture is false", Disp(new Formula.Not(F.Id("claim"))),
                "Over F2, take s1=1,s2=2,n=4 and columns e0,e0,e1,e2. Matrix rank equals three, and actual expectations are (2,6). The universal five-column obstruction excludes every full-rank successor under weak Pareto domination. Matrix rank is connected to full column span by the pinned finite-dimensional rank lemmas. This refutes Conjecture 2, not the already excluded (1,1) case or an append-only substitute.",
                DescribeRole.Theorem, AssessedProvenance.FromRepo(Source),
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("bar-lev-2026-pareto-code-length-monotonicity-refutation"),
                    ResolutionKind.Refuted))),
        []));

    private static DocumentBlock Definition(string name, string title, string prose) =>
        Node(name, title, Disp(Call(name)), prose, DescribeRole.Definition, AssessedProvenance.FromRepo());

    private static DocumentBlock Theorem(string name, string title, Formula formula, string prose) =>
        Node(name, title, Disp(formula), prose, DescribeRole.Theorem, AssessedProvenance.FromRepo());

    private static DocumentBlock Node(string name, string title, Formula formula, string prose,
        DescribeRole role, AssessedProvenance provenance, OpenProblemResolutionClaim? resolution = null) =>
        Describe.Lean(DescribeId.Create("minimum-retrieval-time-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Named(string name) => Seq(Operatorname, Grp(F.Id(name)));
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Named(name), [.. arguments]);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Less(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula AtMost(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Expectation(Formula columns, Formula file) => Call("E", columns, file);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);

    private static Formula ClaimFormula()
    {
        Formula field = F.Id("K"), firstSize = F.Id("s1"), secondSize = F.Id("s2");
        Formula length = F.Id("n"), columns = F.Id("G"), successor = F.Id("Gprime");
        Formula firstFile = Call("firstCoordinateFile", field, firstSize, secondSize);
        Formula secondFile = Call("secondCoordinateFile", field, firstSize, secondSize);
        Formula dimension = new Formula.Binary(firstSize, FormulaBinaryOperator.Add, secondSize);
        Formula nextLength = new Formula.Binary(length, FormulaBinaryOperator.Add, D(1));
        Formula bounds = new Formula.Logic(
            AtMost(Expectation(successor, firstFile), Expectation(columns, firstFile)),
            FormulaLogicOperator.And,
            AtMost(Expectation(successor, secondFile), Expectation(columns, secondFile)));
        Formula next = new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create("Gprime"),
            Call("FullRankCodes", field, dimension, nextLength), bounds);
        return All("K", Named("FiniteFields"), All("s1", Named("PositiveNaturals"),
            All("s2", Named("PositiveNaturals"), new Formula.Logic(
                AtMost(D(2), Call("max", firstSize, secondSize)), FormulaLogicOperator.Implies,
                All("n", Named("Naturals"), new Formula.Logic(AtMost(dimension, length),
                    FormulaLogicOperator.Implies,
                    All("G", Call("FullRankCodes", field, dimension, length), next)))))));
    }
}
