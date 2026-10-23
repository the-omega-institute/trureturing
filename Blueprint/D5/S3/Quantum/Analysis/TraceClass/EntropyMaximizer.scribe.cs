using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.TraceClass;

internal sealed class EntropyMaximizerDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite continuous entropy has a unique global maximum on a closed convex state family.",
        H("A global entropy center before compactness"),
        Blocks(Describe.Lean(
            DescribeId.Create("quantum-entropy-global-maximizer"),
            DeclarationHandle.Create(
                "D5/S3/Quantum/Analysis/TraceClass/EntropyMaximizer.exists_unique_entropy_maximizer"),
            H("Bounded entropy, attainment, uniqueness and the quadratic deficit"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let H be any complete complex Hilbert space and A a nonempty closed real-convex "
                    + "subset of its actual trace-class Banach space. Every rho in A is positive and "
                    + "has real trace one. Its existing singular spectralEntropy is finite, and the "
                    + "existing realEntropy is continuous relative to A in the trace norm. In the "
                    + "formula, AllPositiveTraceOne and AllFiniteSpectralEntropy express exactly these "
                    + "pointwise conditions. For a state rho, its Reference is formed from rho, its "
                    + "positivity and the contraction inequality derived from its actual trace. "
                    + "realEntropy is the real value of this finite spectralEntropy.")),
                Paragraph(Text(
                    "Positivity identifies the trace norm with the real trace, so every state has "
                    + "norm one and any pair has distance at most two. The actual realEntropy is "
                    + "nonnegative. Fix x in A. Relative continuity gives delta>0 such that any z in A "
                    + "within delta of x has entropy below realEntropy(x)+1. Set t=min(1/2,delta/4). "
                    + "For any y in A the state z=(1-t)x+ty lies in A and has distance at most 2t<delta "
                    + "from x. Weighted entropy concavity and nonnegativity yield "
                    + "t*realEntropy(y)<=realEntropy(z)<realEntropy(x)+1. Thus the single finite "
                    + "number (realEntropy(x)+1)/t bounds entropy on all of A. This argument uses "
                    + "relative continuity at one point and does not require an ambient interior.")),
                Paragraph(Text(
                    "The full weighted quantitative entropy inequality supplies StrongConcaveOn "
                    + "with modulus 1/2. The closed family is complete in the trace-class Banach norm, "
                    + "and relative continuity supplies upper semicontinuity. Applying "
                    + "StrongConcavityAttainment.exists_unique_maximizer with the newly derived "
                    + "bound gives an actual gamma in A, IsMaxOn realEntropy A gamma, the deficit "
                    + "norm(rho-gamma)^2/8<=realEntropy(gamma)-realEntropy(rho) for every rho in A, "
                    + "and equality of every other maximizer with gamma.")),
                Paragraph(Text(
                    "No separability, finite dimension, commutativity, faithfulness, compactness, "
                    + "energy bound or prior entropy bound is assumed. Kernel fibers are retained "
                    + "by the existing spectral entropy. The boundedness and attainment argument "
                    + "is a standard consequence of concavity, continuity and completeness. The "
                    + "original Shirokov common-reference and full all-temperature Hamiltonian "
                    + "conclusions require further constructions; this entropy center alone does "
                    + "not resolve those conjectures."))),
            DescribeRole.Theorem))));

    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Implies(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Le(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Exists(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);

    private static Formula Statement()
    {
        Formula h = F.Id("H"), a = F.Id("A"), g = F.Id("gamma"), r = F.Id("rho");
        Formula e = F.Id("realEntropy"), carrier = Call("TraceClass", h);
        Formula hypotheses = And(Call("Nonempty", a), And(Call("IsClosed", a),
            And(Call("Convex", F.Id("Real"), a), And(Call("AllPositiveTraceOne", a),
            And(Call("AllFiniteSpectralEntropy", a), Call("ContinuousOn", e, a))))));
        Formula gap = All("rho", carrier, Implies(Call("Mem", r, a),
            Le(Call("multiply", Call("divide", D(1), D(8)), Call("square", Call("norm", Call("subtract", r, g)))),
                Call("subtract", Call("realEntropy", g), Call("realEntropy", r)))));
        Formula unique = All("rho", carrier, Implies(And(Call("Mem", r, a),
            Call("IsMaxOn", e, a, r)), Equal(r, g)));
        Formula maximum = Exists("gamma", carrier, And(Call("Mem", g, a),
            And(Call("IsMaxOn", e, a, g), And(gap, unique))));
        return All("H", F.Id("CompleteComplexHilbertSpace"), All("A", Call("Set", carrier),
            Implies(hypotheses, And(Call("BddAbove", Call("image", e, a)), maximum))));
    }
}
