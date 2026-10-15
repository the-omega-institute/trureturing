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
            Item("shift_strictlyPositive","Strict positivity of every positive shift",Call("PositiveShiftOfNonnegativeOperatorIsStrictlyPositive"),
                "For every bounded nonnegative operator T and every positive real epsilon, T+epsilon I is strictly positive. The nonnegative-add rule and strict positivity of the positive scalar operator prove this directly. Shifted CFC logarithms therefore have no singular spectrum at zero."),
            Describe.Lean(DescribeId.Create("positive-analytic-trace-pairing"),
                DeclarationHandle.Create("D5/S3/Quantum/Analysis/TraceClass/LogRegularization.tracePairing_nonneg"),
                H("Noncommuting positive trace pairing"), StatementSource.FromAuthor(Positivity()),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("For a bounded positive A and a positive trace-class rho, Re Tr(A rho) is nonnegative. With R equal to sqrt A, the trace-class ideal makes R rho trace class. Bounded-factor cyclicity gives Tr(A rho) = Tr(R rho R), and the latter operator is positive. The argument retains self-adjointness of R and requires no commutation or trace-class square root of rho.")),
                    Paragraph(Text("Positivity and normalization also imply rho is an operator contraction: the trace norm equals the real trace, and the operator norm is bounded by the trace norm."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("regularized-log-energy-lower-semicontinuity"),
                DeclarationHandle.Create("D5/S3/Quantum/Analysis/TraceClass/LogRegularization.lowerSemicontinuous_regularizedSupremum"),
                H("Lower semicontinuity of the regularized supremum"), StatementSource.FromAuthor(Semicontinuity()),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The reference space consists of actual positive trace-class contractions and carries the topology from the genuine trace norm. For epsilon positive, B_epsilon(T) = log(1+epsilon) I - log(T+epsilon I) is a bounded positive self-adjoint operator. The pairing Re Tr(B_epsilon(T) rho) is continuous in T for every fixed trace-class rho.")),
                    Paragraph(Text("The auxiliary regularizedSupremum is the ENNReal supremum of these actual trace pairings at epsilon_n = 1/(n+1). Continuity of each term gives lower semicontinuity of the supremum. For positive rho the same supremum reverses Loewner order, including noncommuting references.")),
                    Paragraph(Text("SpectralEnergy separately identifies this auxiliary supremum with an actual singular spectral series, while KernelEnergy identifies its actual kernel obstruction. The auxiliary definition alone supplies neither result. The logarithm theorems are supplied by pinned Mathlib, and the analytic trace-class infrastructure is attributed to Tom Ole Diem's Physlib."))),
                DescribeRole.Theorem),
            Item("cfc_apply_eigenvector", "CFC action on actual eigenvectors", Eigenvector(),
                "For a self-adjoint bounded operator T, a real scalar s, and any vector v satisfying T(v)=s v, the real continuous functional calculus sends v to f(s) v. Continuity is required only on the actual real spectrum. The zero-vector case is separate; a nonzero eigenvector supplies spectrum membership. The equality locus in the continuous functions on the compact spectrum is closed and contains constants, the coordinate function, sums and products, so Stone-Weierstrass induction proves the assertion. No compactness, basis, separability, inverse or spectral gap is required."),
            Item("logRegularization_apply_eigenvector", "Bounded logarithmic eigenvector action", RegularizedEigenvector(),
                "For epsilon>0 and an actual nonnegative operator T, B_epsilon(T) acts on an eigenvector v with real eigenvalue s by [log(1+epsilon)-log(s+epsilon)]v. The representation as a real CFC of T uses continuity of the shifted scalar logarithm on the actual nonnegative spectrum. The general CFC eigenvector theorem is applied directly, including zero vectors and zero eigenvalues."),
            Item("logRegularization_parameter_antitone", "Order as the parameter decreases", ParameterOrder(),
                "For 0<a<=b and 0<=T<=I, B_b(T)<=B_a(T). On the real spectrum, 0<=x<=1 implies (1+b)/(x+b)<=(1+a)/(x+a); scalar logarithm monotonicity and genuine CFC order give the operator inequality."),
            Item("monotone_regularizedEnergy", "Increasing trace energy grid", EnergyMonotone(),
                "For a positive trace-class rho, the real trace energies on epsilon_n=1/(n+1) increase with n. This follows from operator parameter order and positive trace pairing."),
            Item("regularizedSupremum_nonneg_linear", "Finite positive linearity", PositiveLinearity(),
                "The actual bounded trace pairing is linear in rho. Nonnegativity permits ENNReal.ofReal to preserve the finite sums and scalar products. Both energy sequences are increasing on the same grid, so synchronized supremum addition yields the displayed formula. Zero coefficients and infinite energies obey ENNReal arithmetic, including zero times infinity. This finite formula makes no assertion about countable decompositions."),
            Item("scaleReference", "Positive contraction scaling", ScaleDefinition(),
                "Multiplying the actual trace-class operator by a real w in (0,1] preserves positivity and the contraction inequality.", DescribeRole.Definition),
            Item("regularizedSupremum_scaleReference", "Scaling a singular reference", Scaling(),
                "For epsilon>0 the operator T+(epsilon/w)I is strictly positive even when T has a kernel. The supplied log-scalar theorem therefore gives B_epsilon(wT)=B_(epsilon/w)(T)+log((1+epsilon)/(w+epsilon))I. Every positive sequence tending to zero is cofinal for this energy supremum. Use epsilon_n=w/(n+1); the remaining scalar correction increases to -log w. Synchronized supremum addition then gives the formula with the actual unnormalized real trace mass. This result concerns the same auxiliary operator supremum; SpectralEnergy separately proves its identity with the singular eigenvalue series."))));
    private static readonly Formula Hh = F.Id("H"), T = F.Id("T"), Rho = F.Id("rho"),
        Gamma = F.Id("gamma"), A = F.Id("a"), B = F.Id("b"), W = F.Id("w");
    private static Formula Hilbert(Formula.BoundVariable[] xs, Formula body) => All([
        new(FormulaIdentifier.Create("H"), F.Id("CompleteComplexHilbertSpace")), .. xs], body);
    private static Formula ReferenceBody(Formula.BoundVariable[] xs, Formula body) => Hilbert([
        new(FormulaIdentifier.Create("T"), Call("Reference", Hh)), .. xs], body);
    private static Formula Sup(Formula t, Formula r) => Call("regularizedSupremum", t, r);
    private static Formula Nonneg(Formula a) => Call("Nonnegative", a);
    private static Formula OfReal(Formula a) => Call("ofReal", a);
    private static Formula Times(Formula a, Formula b) => Call("multiply", a, b);
    private static Formula Plus(Formula a, Formula b) => Call("add", a, b);
    private static Formula ScalarReference() => Call("scaleReference", T, W);
    private static Formula Eigenvector()
    {
        Formula s = F.Id("s"), v = F.Id("v"), f = F.Id("f");
        return Hilbert([
            new(FormulaIdentifier.Create("T"), Call("BoundedComplexOperator", Hh)),
            new(FormulaIdentifier.Create("s"), F.Id("Real")),
            new(FormulaIdentifier.Create("v"), Hh),
            new(FormulaIdentifier.Create("f"), Call("Function", F.Id("Real"), F.Id("Real")))],
            Implies(And(Call("IsSelfAdjoint", T), And(Equal(Call("apply", T, v), Call("smul", Call("complexOfReal", s), v)),
                Call("ContinuousOn", f, Call("spectrumReal", T)))),
                Equal(Call("apply", Call("cfc", f, T), v), Call("smul", Call("complexOfReal", Call("apply", f, s)), v))));
    }
    private static Formula RegularizedEigenvector()
    {
        Formula e=F.Id("epsilon"), s=F.Id("s"), v=F.Id("v");
        return Hilbert([new(FormulaIdentifier.Create("epsilon"),F.Id("Real")),
            new(FormulaIdentifier.Create("T"),Call("BoundedComplexOperator",Hh)),
            new(FormulaIdentifier.Create("s"),F.Id("Real")),new(FormulaIdentifier.Create("v"),Hh)],
            Implies(And(Call("Positive",e),And(Nonneg(T),Equal(Call("apply",T,v),Call("smul",Call("complexOfReal",s),v)))),
                Equal(Call("apply",Call("logRegularization",e,T),v),Call("smul",Call("complexOfReal",Call("subtract",Call("log",Plus(D(1),e)),Call("log",Plus(s,e)))),v))));
    }
    private static Formula ParameterOrder() => Hilbert([
        new(FormulaIdentifier.Create("a"), F.Id("Real")), new(FormulaIdentifier.Create("b"), F.Id("Real")),
        new(FormulaIdentifier.Create("T"), Call("BoundedComplexOperator", Hh))],
        Implies(And(Call("Positive", A), And(Le(A, B), And(Nonneg(T), Le(T, D(1))))),
            Le(Call("logRegularization", B, T), Call("logRegularization", A, T))));
    private static Formula EnergyMonotone() => ReferenceBody([
        new(FormulaIdentifier.Create("rho"), Call("TraceClass", Hh))],
        Implies(Nonneg(Rho), Call("Monotone", Call("regularizedEnergyGrid", T, Rho))));
    private static Formula PositiveLinearity() => ReferenceBody([
        new(FormulaIdentifier.Create("rho"), Call("TraceClass", Hh)),
        new(FormulaIdentifier.Create("gamma"), Call("TraceClass", Hh)),
        new(FormulaIdentifier.Create("a"), F.Id("Real")), new(FormulaIdentifier.Create("b"), F.Id("Real"))],
        Implies(And(Nonneg(Rho), And(Nonneg(Gamma), And(Nonneg(A), Nonneg(B)))),
            Equal(Sup(T, Plus(Call("smul", Call("complexOfReal", A), Rho), Call("smul", Call("complexOfReal", B), Gamma))),
                Plus(Times(OfReal(A), Sup(T, Rho)), Times(OfReal(B), Sup(T, Gamma))))));
    private static Formula ScaleDefinition() => ReferenceBody([
        new(FormulaIdentifier.Create("w"), F.Id("Real"))],
        Implies(And(Call("Positive", W), Le(W, D(1))),
            Equal(Call("underlyingOperator", ScalarReference()), Call("smul", Call("complexOfReal", W), Call("underlyingOperator", T)))));
    private static Formula Scaling() => ReferenceBody([
        new(FormulaIdentifier.Create("rho"), Call("TraceClass", Hh)), new(FormulaIdentifier.Create("w"), F.Id("Real"))],
        Implies(And(Nonneg(Rho), And(Call("Positive", W), Le(W, D(1)))),
            Equal(Sup(ScalarReference(), Rho), Plus(Sup(T, Rho),
                Times(OfReal(Call("Re", Call("trace", Rho))), OfReal(Call("negate", Call("log", W))))))));
    private static DocumentBlock Item(string name, string title, Formula formula, string text, DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(DescribeId.Create("log-energy-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/Quantum/Analysis/TraceClass/LogRegularization." + name),
            H(title), StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(text))), role);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
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
