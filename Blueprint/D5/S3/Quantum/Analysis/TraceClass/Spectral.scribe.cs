using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.TraceClass;
internal sealed class SpectralDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Complete spectral representation of the original positive trace-class operator.",
        H("Full spectrum and faithful finite or Nat reference bases"), Blocks(
            Item("exists_nonneg_trace_spectral_data", "Full nonnegative trace spectrum", General(),
                "H is an arbitrary complete complex Hilbert space, T is its actual bounded complex-linear operator, and trace is the analytic trace with its genuine IsTraceClass proof. The conclusion constructs w as a set of vectors in H, a full Hilbert basis b indexed by w, and real eigenvalues s. Every eigenspace is retained, including zero. The real eigenvalues are summable, have sum Re(trace T), and their complex casts have sum trace T. For each x, the weighted terms are (b.repr x i * (s i : Complex)) smul b i and have actual sum T(x). No basis, compactness, spectral carrier, separability or countability assumption is an input."),
            Item("exists_faithful_reference_spectral_data", "Faithful normalized reference", Faithful(),
                "The kernel is the actual linear-map kernel. Strictly positive weights follow because a zero eigenvalue would put a norm-one basis vector in that trivial kernel. Real summability and positivity then make the full index countable. Both the real and complex sums equal one, and the weighted expansion converges to the original sigma(x). Faithfulness gives no bounded inverse or uniform spectral gap."),
            Item("faithful_reference_finite_or_nat", "Actual finite or Nat basis", Branches(),
                "The finite branch returns a natural number n, an actual Hilbert basis indexed by Fin n, positive weights, finite-dimensionality, both trace sums and the original-operator vector series. In the infinite branch a genuine equivalence from the source full index to Nat transports a full Hilbert basis and all scalar sums; the transported basis has the same weighted operator representation. A finite basis is never padded by zero vectors."),
            Paragraph(Text("Construction: choose a Hilbert basis in each closed complex eigenspace. Mathlib's orthogonal sigma-family theorem gives orthonormality. An ambient vector orthogonal to all these vectors is orthogonal to each full eigenspace by density; the compact symmetric spectral theorem makes it zero. HilbertBasis.mkOfOrthogonalEqBot therefore yields a full basis. Symmetry makes its eigenvalues real, and the nonnegative quadratic form makes them nonnegative. The accepted trace-class compactness theorem supplies compactness from the operator itself.")),
            Paragraph(Text("The analytic diagonal summability and positive trace-basis identity are the attributed Physlib suppliers in Library/QuantumBounds/diem2026traceclass.md. Rewriting the actual diagonal first establishes Summable s; only then is its real sum identified with the trace. Mapping b.hasSum_repr x through T proves the weighted series. This is a formal composition of standard spectral theory, not a new analytic spectral theorem or a solution of the entropy-continuity conjecture.")),
            Paragraph(Text("Boundary cases: zero on a nonseparable space retains its full zero eigenspace without a countability conclusion. A nonfaithful rank-one state does not satisfy the faithful adapter's kernel premise. Positive summable eigenvalues may tend to zero. These endpoints do not assert logarithmic energy, entropy identities, heat-trace finiteness or an unbounded Hamiltonian.")))));

    private static readonly Formula Hh = F.Id("H"), T = F.Id("T"), W = F.Id("w"),
        B = F.Id("b"), S = F.Id("s"), I = F.Id("i"), X = F.Id("x"), N = F.Id("n"), E = F.Id("e"), C = F.Id("c");
    private static Formula At(Formula f, Formula x) => new Formula.Apply(f, [x]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [new(FormulaIdentifier.Create(name), type)], body);
    private static Formula Exists(string name, Formula type, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [new(FormulaIdentifier.Create(name), type)], body);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Or(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Or, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula Preconditions(bool faithful) => faithful
        ? And(Le(D(0), T), And(Call("IsTraceClass", T), And(Equal(Call("kernel", T), Call("bottom")), Equal(Call("trace", T), D(1)))))
        : And(Le(D(0), T), Call("IsTraceClass", T));
    private static Formula Spectrum(Formula index, bool faithful, bool finite = false)
    {
        var eigen = All("i", index, Equal(At(T, At(B, I)), Call("smul", Call("complexCast", At(S, I)), At(B, I))));
        var signs = All("i", index, faithful ? Lt(D(0), At(S, I)) : Le(D(0), At(S, I)));
        var realTotal = faithful ? D(1) : Call("re", Call("trace", T));
        var complexTotal = faithful ? D(1) : Call("trace", T);
        var vectors = All("x", Hh, Call("HasSum", Call("weightedBasisTerms", B, S, X), At(T, X)));
        var body = And(signs, And(eigen, And(Call("Summable", S),
            And(Call("HasSum", S, realTotal), And(Call("HasSum", Call("complexCastFamily", S), complexTotal), vectors)))));
        return finite ? And(Call("FiniteDimensional", Call("Complex"), Hh), body) : body;
    }
    private static Formula Basis(Formula index, Formula body) =>
        Exists("b", Call("HilbertBasis", index, Call("Complex"), Hh), Exists("s", Call("Function", index, Call("Real")), body));
    private static Formula Operator(Formula body, bool faithful) =>
        All("H", Call("CompleteComplexHilbertSpace"), All("T", Call("BoundedComplexOperator", Hh), Imp(Preconditions(faithful), body)));
    private static Formula General() => Operator(Exists("w", Call("Set", Hh), Basis(W, Spectrum(W, false))), false);
    private static Formula Faithful() => Operator(Exists("w", Call("Set", Hh), Basis(W, And(Spectrum(W, true), Call("Countable", W)))), true);
    private static Formula Branches() => Operator(Or(
        Exists("n", Call("Nat"), Basis(Call("Fin", N), Spectrum(Call("Fin", N), true, true))),
        Exists("w", Call("Set", Hh), Exists("c", Call("HilbertBasis", W, Call("Complex"), Hh),
            Exists("e", Call("Equiv", W, Call("Nat")), Basis(Call("Nat"),
                And(All("i", Call("Nat"), Equal(At(B, I), At(C, Call("inverseApply", E, I)))),
                    Spectrum(Call("Nat"), true))))))), true);
    private static DocumentBlock Item(string name, string title, Formula statement, string explanation) =>
        Describe.Lean(DescribeId.Create("spectral-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/Quantum/Analysis/TraceClass/Spectral." + name),
            H(title), StatementSource.FromAuthor(statement),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/QuantumBounds/mathlib2026compactspectral")),
            Blocks(Paragraph(Text(explanation))), DescribeRole.Theorem);
}
