using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.TraceClass;
internal sealed class LogRegularizationDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/QuantumBounds/mathlib2026operatorlog");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual bounded logarithmic trace energies on positive trace-class contractions.",
        H("Positive trace pairing and logarithmic regularization"), Blocks(
            Describe.Lean(DescribeId.Create("positive-analytic-trace-pairing"),
                DeclarationHandle.Create("D5/S3/Quantum/Analysis/TraceClass/LogRegularization.QuantumLogEnergy.tracePairing_nonneg"),
                H("Noncommuting positive trace pairing"), StatementSource.FromAuthor(Positivity()),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For a bounded positive A and a positive trace-class rho, Re Tr(A rho) is nonnegative. With R equal to sqrt A, the trace-class ideal makes R rho trace class. Bounded-factor cyclicity gives Tr(A rho) = Tr(R rho R), and the latter operator is positive. The argument retains self-adjointness of R and requires no commutation or trace-class square root of rho.")),
                    Paragraph(Text("Positivity and normalization also imply rho is an operator contraction: the trace norm equals the real trace, and the operator norm is bounded by the trace norm."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("regularized-log-energy-lower-semicontinuity"),
                DeclarationHandle.Create("D5/S3/Quantum/Analysis/TraceClass/LogRegularization.QuantumLogEnergy.lowerSemicontinuous_regularizedSupremum"),
                H("Lower semicontinuity of the regularized supremum"), StatementSource.FromAuthor(Semicontinuity()),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The reference space consists of actual positive trace-class contractions and carries the topology from the genuine trace norm. For epsilon positive, B_epsilon(T) = log(1+epsilon) I - log(T+epsilon I) is a bounded positive self-adjoint operator. The pairing Re Tr(B_epsilon(T) rho) is continuous in T for every fixed trace-class rho.")),
                    Paragraph(Text("The auxiliary regularizedSupremum is the ENNReal supremum of these actual trace pairings at epsilon_n = 1/(n+1). Continuity of each term gives lower semicontinuity of the supremum. For positive rho the same supremum reverses Loewner order, including noncommuting references.")),
                    Paragraph(Text("Its identification with a singular spectral log-energy sum, the zero-kernel projection identity, scaling, self entropy, and finite-entropy cross-energy domination require additional spectral results. These statements are not consequences of the auxiliary definition alone. The logarithm theorems are supplied by pinned Mathlib, and the analytic trace-class infrastructure is attributed to Tom Ole Diem's Physlib."))),
                DescribeRole.Theorem))));
    private static Formula Positivity()
    {
        Formula h = F.Id("H"), a = F.Id("A"), rho = F.Id("rho");
        return All([new(FormulaIdentifier.Create("H"), F.Id("CompleteComplexHilbertSpace")),
            new(FormulaIdentifier.Create("A"), Call("BoundedComplexOperator", h)),
            new(FormulaIdentifier.Create("rho"), Call("TraceClass", h))],
            Implies(And(Call("Nonnegative", a), Call("Nonnegative", rho)),
                Call("Nonnegative", Call("Re", Call("tracePairing", a, rho)))));
    }
    private static Formula Semicontinuity()
    {
        Formula h = F.Id("H"), rho = F.Id("rho");
        return All([new(FormulaIdentifier.Create("H"), F.Id("CompleteComplexHilbertSpace")),
            new(FormulaIdentifier.Create("rho"), Call("TraceClass", h))],
            Call("LowerSemicontinuous", Call("regularizedSupremumAt", rho, Call("Reference", h))));
    }
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula All(Formula.BoundVariable[] xs, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. xs], body);
}
