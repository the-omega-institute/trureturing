using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.TraceClass;
internal sealed class EnergySublevelCompactnessDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source=LibraryNoteRef.Create("D5/L/QuantumBounds/mathlib2026tracecompactness");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Compactness of complete singular-energy state sublevels in trace norm.",
        H("Energy tightness and trace-norm compactness"), Blocks(
            Item("energySublevel", "The entire energy sublevel", Parameters(All([
                new(FormulaIdentifier.Create("rho"), Call("TraceClass", Hh))],
                Iff(Call("member", Rho, Sublevel()), Conj(Positive(),
                    Conj(Equal(Call("Re", Call("trace", Rho)), D(1)),
                    Le(Call("spectralEnergy", T, Rho), Call("ofReal", M))))))),
                "The set consists of all actual positive trace-one operators with spectral energy at most ofReal M. Its topology is the genuine trace-class Banach topology. The reference is any positive trace-class contraction and is not required to be faithful or normalized. Negative real bounds are clamped by ofReal; no emptiness claim for negative M is made.", DescribeRole.Definition),
            Item("lowerSemicontinuousOn_spectralEnergy_state", "State-slot lower semicontinuity on the positive cone", Reference(
                Call("LowerSemicontinuousOn", Call("spectralEnergyAtReference", T), Call("positiveTraceClassCone", Hh))),
                "For fixed T, every bounded regularized trace pairing is continuous in the trace-class argument. Applying ofReal and taking the supremum gives lower semicontinuity. On the positive cone the actual singular spectral energy equals this supremum. The equality is used only for positive rho; this assertion makes no lower-semicontinuity claim on arbitrary nonpositive operators."),
            Item("isClosed_energySublevel", "Closedness of the complete state sublevel", Parameters(Call("IsClosed", Sublevel())),
                "The positive cone is closed through the continuous trace-norm-to-operator inclusion. The normalization equation is closed through the bounded trace pairing with the identity. State-slot lower semicontinuity on the positive cone gives a relatively closed energy sublevel. Intersecting these three conditions proves ambient trace-norm closedness."),
            Item("totallyBounded_energySublevel", "Uniform finite compression covers", Parameters(Imp(Le(D(0), M), Call("TotallyBounded", Sublevel()))),
                "Select the native full Set-index spectral basis of T together with its summable nonnegative eigenvalues s. For R>0 the indices with s_i at least exp(-R) form a finite set. Outside this set, singularLog(s_i) is at least R, including s_i=0 where singularLog is infinity. Summation in ENNReal before any conversion to real numbers gives R q<=M for the actual discarded state mass q. The noncommuting finite-compression estimate gives trace-norm error at most 2 sqrt(M/R). Compressed states lie in one compact image of the finite-dimensional trace-norm unit ball. A finite cover of this image and the uniform error bound give a finite cover of the entire sublevel. Arbitrary kernel fibers, M=0 and empty sublevels remain included."),
            Item("isCompact_energySublevel", "Trace-norm compactness of the entire energy sublevel", Parameters(Imp(Le(D(0), M), Call("IsCompact", Sublevel()))),
                "Closedness and total boundedness in the complete trace-class carrier imply compactness. The argument imposes no separability, finite ambient dimension, spectral enumeration, commutation or prior compactness assumption. This is a state-family compactness result for one reference; construction of a common continuous reference and a full unbounded Hamiltonian requires separate results."))));
    private static readonly Formula Hh=F.Id("H"), T=F.Id("T"), M=F.Id("M"), Rho=F.Id("rho");
    private static Formula Sublevel() => Call("energySublevel", T, M);
    private static Formula Positive() => Le(D(0), Call("underlyingOperator", Rho));
    private static Formula Reference(Formula body) => All([
        new(FormulaIdentifier.Create("H"), F.Id("CompleteComplexHilbertSpace")),
        new(FormulaIdentifier.Create("T"), Call("Reference", Hh))], body);
    private static Formula Parameters(Formula body) => Reference(All([new(FormulaIdentifier.Create("M"), F.Id("Real"))], body));
    private static DocumentBlock Item(string name, string title, Formula formula, string text, DescribeRole role=DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create("singular-energy-sublevel-"+name.Replace('_','-').ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/Quantum/Analysis/TraceClass/EnergySublevelCompactness."+name), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(text))), role);
    private static Formula All(Formula.BoundVariable[] xs, Formula body) => new Formula.BindMany(FormulaQuantifier.ForAll, [..xs], body);
    private static Formula Conj(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
}
