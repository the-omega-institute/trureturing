using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis;

internal sealed class CompactEigenbasisDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Full real eigenbases of compact symmetric Hilbert operators over real or complex scalars.",
        H("Compact Symmetric Eigenbasis"), Blocks(
            Describe.Lean(
                DescribeId.Create("compact-symmetric-set-index-eigenbasis"),
                DeclarationHandle.Create("D5/S3/Quantum/Analysis/CompactEigenbasis.exists_setIndex_real_eigenbasis_rclike"),
                H("A full set-indexed eigenbasis with real eigenvalues"),
                StatementSource.FromAuthor(CompactBasis()),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/QuantumBounds/mathlib2026compactspectral")),
                Blocks(
                    Paragraph(Text("For either real or complex scalars, let E be an arbitrary complete Hilbert space and T its actual compact symmetric continuous linear endomorphism. There exist a subset w of E, a full Hilbert basis b indexed by w, and a real family s such that T(b(i)) is the scalar cast of s(i) times b(i). Zero eigenspaces are retained. No positivity, trace-class, separability, countability or finite-dimensional hypothesis is imposed.")),
                    Paragraph(Text("Choose a Hilbert basis in each closed eigenspace, including eigenvalue zero. Distinct eigenspaces are orthogonal. If a vector is orthogonal to the combined basis, density makes it orthogonal to each full eigenspace; the compact symmetric spectral theorem then makes it zero. This constructs a full Hilbert basis. Symmetry makes every eigenvalue real, and the actual range of that basis supplies the subset index.")),
                    Paragraph(Text("The complex trace-class spectral representation uses the complex specialization. The real mean-zero boundary covariance uses the real specialization before deriving positivity, ordered infinite modes and multiplicities from its own hypotheses. These applications share the same complete eigenbasis construction."))),
                DescribeRole.Theorem))));

    private static readonly Formula T = F.Id("T"), W = F.Id("w"),
        B = F.Id("b"), S = F.Id("s"), I = F.Id("i");
    private static Formula At(Formula f, Formula x) => new Formula.Apply(f, [x]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [new(FormulaIdentifier.Create(name), type)], body);
    private static Formula Exists(string name, Formula type, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [new(FormulaIdentifier.Create(name), type)], body);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula CompactBasis()
    {
        Formula k=F.Id("k"), e=F.Id("E");
        Formula eigen=All("i", W,
            Equal(At(T, At(B,I)), Call("smul", Call("scalarCast", k, At(S,I)), At(B,I))));
        Formula basis=Exists("w", Call("Set", e),
            Exists("b", Call("HilbertBasis", W, k, e),
                Exists("s", Call("Function", W, Call("Real")), eigen)));
        return All("k", Call("RCLikeScalar"), All("E", Call("CompleteHilbertSpace", k),
            All("T", Call("ContinuousLinearEnd", k, e), Imp(
                And(Call("IsCompactOperator", T), Call("IsSymmetric", T)), basis))));
    }
}
