using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HilbertOperators.Approximation;

internal sealed class KyFanTriangleDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/HilbertOperators/Approximation/KyFanTriangle.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite approximation-number prefixes obey the triangle inequality on arbitrary complex Hilbert spaces.",
        H("Approximation-number Ky Fan triangle"),
        Blocks(
            Paragraph(Text("The approximation number at index n is the infimum of operator-norm errors over actual bounded operators of rank at most n. The source and target Hilbert spaces may have independent universes and unequal dimensions. Every prefix length is a natural number, including zero and lengths above either finite dimension. Compactness, separability and nonzero spaces are not assumptions.")),
            Node("lower-bound-of-lt-rank", "lower_bound_of_lt_rank", null,
                "A subspace of rank greater than n forces every rank-at-most-n approximant to have a nonzero kernel vector in that subspace. A homogeneous lower modulus on the subspace therefore bounds the approximation number from below."),
            Node("spectral-lower", "singular_value_le_approximation_number", null,
                "In finite dimensions the first n plus one right singular directions give the lower spectral bound, by the rank obstruction."),
            Node("spectral-upper", "approximation_number_le_singular_value", null,
                "Projection onto the first n right singular directions gives an actual rank-at-most-n approximant. The ordered Gram eigenvalues bound its complementary error. When n exceeds the source dimension the original operator itself is admissible."),
            Node("spectral-identification", "approximation_number_eq_singular_value", null,
                "The two spectral inequalities identify approximation numbers with Mathlib singular values, including zero padding and independent universes."),
            Describe.Lean(DescribeId.Create("ky-fan-gauge"), DeclarationHandle.Create(Owner + "ky_fan_gauge"),
                H("Finite approximation-number prefix"), StatementSource.FromAuthor(Disp(GaugeFormula())),
                AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/HilbertOperators/kitware2026kyfanapproximation")),
                Blocks(Paragraph(Text("The displayed kyFanGauge denotes the native ky_fan_gauge, approximationNumber denotes MinMaxLowerBound.approximation_number, and range denotes Finset.range. The definition is a finite prefix sum of that single native approximation_number. It requires complex inner-product structures but neither completeness instance."))), DescribeRole.Definition),
            Node("finite-restriction-tolerance", "exists_finite_restriction_add_gt", null,
                "Every strictly positive tolerance admits a restriction to the span of n plus one actual vectors whose approximation number approaches the ambient one. Completeness of both spaces supplies the strict-threshold min-max input; the zero and small-value cases remain included."),
            Node("ky-fan-triangle", "ky_fan_gauge_add_le", TriangleFormula(),
                "The finite spectral theorem and an attaining orthonormal pair give the rectangular finite-dimensional triangle inequality. Isometric coordinate transport permits independent universes. Compression to the joint range handles an arbitrary target for a finite source. For each positive tolerance, the finitely many near-optimal source restrictions for the prefix are placed in one common finite span. Summing their errors and letting the tolerance decrease proves the stated inequality. Both completeness instances are retained."),
            Paragraph(Text("These classical results adapt AIQ-Kitware/aiq-dkps-formalization revision 8924c4cc743d2f193bb4f39bee800790698a681b under Apache-2.0. Existing finite rectangular and spectral proofs retain their separate attribution chains. No infinite-prefix, compact-spectrum, Hilbert-Schmidt energy, Shirokov-cost or convex-roof identity follows solely from this statement.")))));

    private static DocumentBlock Node(string id, string name, Formula? formula, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Owner + name), H(name),
            formula is null ? StatementSource.WithoutFormula() : StatementSource.FromAuthor(Disp(formula)),
            AssessedProvenance.FromLiterature(LibraryNoteRef.Create("D5/L/HilbertOperators/kitware2026kyfanapproximation")),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
    private static Formula Id(string name) => F.Id(name);
    private static Formula Named(string name) => new Formula.NamedConstant(FormulaIdentifier.Create(name));
    private static Formula App(string name, params Formula[] args) => new Formula.Apply(Named(name), [..args]);
    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal,b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual,b);
    private static Formula Add(Formula a, Formula b) => new Formula.Binary(a,FormulaBinaryOperator.Add,b);
    private static Formula Op() => Seq(Id("E"), Sp, new Formula.Subscript(To, Id("L")),
        OpenBracket, Named("Complex"), CloseBracket, Sp, Id("F"));
    private static Formula Instance(Formula type, Formula body) =>
        Seq(OpenBracket, type, CloseBracket, Sp, body);
    private static Formula Structures(bool complete, Formula body)
    {
        if (complete) body = Instance(App("CompleteSpace", Id("E")),
            Instance(App("CompleteSpace", Id("F")), body));
        body = Instance(App("NormedAddCommGroup", Id("E")),
            Instance(App("InnerProductSpace", Named("Complex"), Id("E")),
            Instance(App("NormedAddCommGroup", Id("F")),
            Instance(App("InnerProductSpace", Named("Complex"), Id("F")), body))));
        return All("u", App("UniverseLevel"), All("v", App("UniverseLevel"),
            All("E", App("Type", Id("u")), All("F", App("Type", Id("v")), body))));
    }
    private static Formula Gauge(Formula op) => App("kyFanGauge",op,Id("k"));
    private static Formula TriangleFormula() => Structures(true,
        All("S",Op(),All("T",Op(),All("k",Named("Nat"),
            Le(Gauge(Add(Id("S"),Id("T"))),Add(Gauge(Id("S")),Gauge(Id("T"))))))));
    private static Formula GaugeFormula() => Structures(false,
        All("T",Op(),All("k",Named("Nat"),Eq(Gauge(Id("T")),
            Seq(new Formula.Subscript(Sum,Seq(Id("n"),Sp,InMacro,Sp,App("range",Id("k")))),
                Sp,App("approximationNumber",Id("T"),Id("n")))))));
}
