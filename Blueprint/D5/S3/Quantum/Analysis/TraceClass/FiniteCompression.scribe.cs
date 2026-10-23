using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.TraceClass;
internal sealed class FiniteCompressionDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/QuantumBounds/mathlib2026tracecompactness");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite orthogonal compression in the trace-class Banach space.",
        H("Compression and discarded mass"), Blocks(
            Item("compress", "Two-sided trace-class compression", Hilbert([
                new(FormulaIdentifier.Create("P"), Call("BoundedComplexOperator", Hh)),
                new(FormulaIdentifier.Create("rho"), Call("TraceClass", Hh))],
                Equal(Call("underlyingOperator", Call("compress", P, Rho)),
                    Call("multiply", Call("multiply", P, Call("underlyingOperator", Rho)), P))),
                "Compression sends rho to P rho P. The trace-ideal inequality bounds its trace norm by the square of the operator norm of P times the trace norm of rho. This constructs a continuous complex-linear map on the genuine trace-norm space.", DescribeRole.Definition),
            Item("finiteSpan", "Finite basis span", Basis(Equal(U(), Call("span", Call("image", B, Ff)))),
                "The subspace is the complex span of the finite image of F under the full Hilbert basis b. It is finite dimensional even when the ambient space and basis index are arbitrary.", DescribeRole.Definition),
            Item("tailMass", "Discarded diagonal mass", BasisState(Equal(Tail(),
                Call("sumOutside", Ff, Call("diagonal", B, Rho)))),
                "The real diagonal sum outside F retains all basis indices. For positive rho each summand is nonnegative, and the full diagonal has sum equal to the real trace.", DescribeRole.Definition),
            Item("finiteDimensional_range", "Finite-dimensional compression range", Hilbert([
                new(FormulaIdentifier.Create("U"), Call("ComplexSubmodule", Hh))],
                Imp(Call("FiniteDimensional", Uu), Call("FiniteDimensional",
                    Call("linearRange", Call("compress", Call("starProjection", Uu)))))),
                "Every operator in the compression range is fixed by P on both sides. Restriction to U gives a linear map from this range into the endomorphisms of U. If the restriction is zero, x(y)=x(P y)=0 for every ambient vector y. Thus the restriction is injective and the range is finite dimensional with its inherited trace norm."),
            Item("exists_compact_compressions", "One compact set of compressed unit-ball elements", Hilbert([
                new(FormulaIdentifier.Create("U"), Call("ComplexSubmodule", Hh))],
                Imp(Call("FiniteDimensional", Uu), Exists([
                    new(FormulaIdentifier.Create("K"), Call("Set", Call("TraceClass", Hh)))],
                    Conj(Call("IsCompact", K), All([
                        new(FormulaIdentifier.Create("rho"), Call("TraceClass", Hh))],
                        Imp(Le(Call("norm", Rho), D(1)), Call("member",
                            Call("compress", Call("starProjection", Uu), Rho), K))))))),
                "Take the image of the closed unit ball of the finite-dimensional compression range under its continuous inclusion into the trace-class space. Orthogonal projection has operator norm at most one, so every compressed trace-norm unit-ball element belongs to this compact image."),
            Item("norm_sub_compress_le", "Noncommuting trace-norm compression error", BasisState(
                Imp(State(), Le(Call("norm", Call("subtract", Rho, Call("compress", Projection(), Rho))),
                    Call("multiply", D(2), Call("sqrt", Tail()))))),
                "For R equal to sqrt rho and Q equal to I-P, the column square sum of RQ is the discarded diagonal mass q. The adjoint column identity gives the same sum for QR, while the sum for PR is at most one. The operator identity rho-P rho P=(QR)R+(PR)(RQ), the Hilbert-Schmidt product trace-norm bound and the trace-norm triangle inequality give the bound 2 sqrt q. R is used as a Hilbert-Schmidt operator, with no assumption that it is trace class. P need not commute with rho."))));
    private static readonly Formula Hh=F.Id("H"), P=F.Id("P"), Rho=F.Id("rho"),
        W=F.Id("w"), B=F.Id("b"), Ff=F.Id("F"), Uu=F.Id("U"), K=F.Id("K");
    private static Formula U() => Call("finiteSpan", B, Ff);
    private static Formula Projection() => Call("starProjection", U());
    private static Formula Tail() => Call("tailMass", B, Ff, Rho);
    private static Formula State() => Conj(Le(D(0), Call("underlyingOperator", Rho)), Equal(Call("Re", Call("trace", Rho)), D(1)));
    private static Formula Hilbert(Formula.BoundVariable[] xs, Formula body) => All([
        new(FormulaIdentifier.Create("H"), F.Id("CompleteComplexHilbertSpace")), .. xs], body);
    private static Formula Basis(Formula body) => Hilbert([
        new(FormulaIdentifier.Create("w"), Call("Set", Hh)),
        new(FormulaIdentifier.Create("b"), Call("HilbertBasis", W, F.Id("Complex"), Hh)),
        new(FormulaIdentifier.Create("F"), Call("Finset", W))], body);
    private static Formula BasisState(Formula body) => Basis(All([
        new(FormulaIdentifier.Create("rho"), Call("TraceClass", Hh))], body));
    private static DocumentBlock Item(string name, string title, Formula formula, string text, DescribeRole role=DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create("finite-trace-compression-"+name.Replace('_','-').ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/Quantum/Analysis/TraceClass/FiniteCompression."+name), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(text))), role);
    private static Formula All(Formula.BoundVariable[] xs, Formula body) => new Formula.BindMany(FormulaQuantifier.ForAll, [..xs], body);
    private static Formula Exists(Formula.BoundVariable[] xs, Formula body) => new Formula.BindMany(FormulaQuantifier.Exists, [..xs], body);
    private static Formula Conj(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
}
