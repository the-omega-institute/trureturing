using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.TraceClass;
internal sealed class EntropyConcavityDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/QuantumBounds/androulakis2023nussbaumszkola");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Full weighted quantitative entropy concavity in the trace-class Banach space.",
        H("Extended entropy and real strong concavity"), Blocks(
            Item("realEntropy_reference","Real entropy on its actual domain",Call("RealEntropyEqualsSpectralEntropyToRealOnReferences"),
                "For every actual positive trace-class contraction rho, realEntropy of its underlying trace-class operator equals the real value of its actual spectral entropy. This is the domain restriction in the definition. Applications interpreting the value as finite entropy supply a separate finiteness premise."),
            Item("spectralEntropy_mixture","All weights, singular references and infinite entropy",Weighted(),
                "For actual positive trace-one References rho and sigma, let a,b be nonnegative real numbers with a+b=1. mixture is the actual trace-class linear combination a rho+b sigma. Positivity and the trace calculation prove normalization, and density_le_one proves the contraction bound. No entropy identity or energy inequality is an assumed field.",
                "Apply the Hellinger trace-norm energy bound to rho relative to the mixture and to sigma relative to the same mixture. Multiply by a and b and add in ENNReal. Actual nonnegative first-slot linearity and self energy identify the upper bound with the spectral entropy of the mixture.",
                "The exact norm identities are norm(rho-tau)=b norm(rho-sigma) and norm(sigma-tau)=a norm(rho-sigma). Their weighted squared rewards add to a b norm(rho-sigma) squared divided by four, since a+b=1. There is no subtraction of infinite values and no finiteness premise on cross energy or entropy. Both zero weights and the zero times infinity convention are included.",
                "For a=1-t and b=t this is the full inequality for every t in [0,1]. At the midpoint the reward is norm(rho-sigma) squared divided by sixteen. The arguments may be noncommuting and either may have a nontrivial kernel."),
            Item("strongConcaveOn_realEntropy","Real entropy has modulus one half",Strong(),
                "realEntropy is the real value of the actual extended spectral entropy on positive trace-class contractions and is extended by zero outside that domain. Let A be any convex subset of TraceClass H consisting of actual positive trace-one densities. Assume their actual spectral entropies are finite. No compactness, entropy boundedness or upper semicontinuity is inferred from these hypotheses.",
                "The convex mixture belongs to A, so its entropy is finite as well. Applying the ENNReal real-value map to the full weighted inequality is justified by these genuine finiteness hypotheses. Real scalar multiplication on TraceClass is the restriction of its complex scalar multiplication, and its norm remains the trace norm.",
                "Mathlib defines StrongConcaveOn A m with reward a b times m/2 times the squared distance. The coefficient one fourth therefore gives modulus m=1/2. This is the full weighted condition, rather than a midpoint-only assertion. The result supplies strong concavity; existence of entropy centers and the original Shirokov common-energy and full-Hamiltonian conclusions still require their other hypotheses and constructions."))));
    private static Formula Le(Formula a,Formula b)=>new Formula.Relation(a,FormulaRelationOperator.LessThanOrEqual,b);
    private static Formula And(Formula a,Formula b)=>new Formula.Logic(a,FormulaLogicOperator.And,b);
    private static Formula Implies(Formula a,Formula b)=>new Formula.Logic(a,FormulaLogicOperator.Implies,b);
    private static Formula.BoundVariable V(string n,Formula t)=>new(FormulaIdentifier.Create(n),t);
    private static Formula Weighted()
    {
        Formula h=F.Id("H"),r=F.Id("rho"),s=F.Id("sigma"),a=F.Id("a"),b=F.Id("b");
        Formula ea=Call("ofReal",a),eb=Call("ofReal",b);
        Formula reward=Call("ofReal",Call("divide",Call("multiply",Call("multiply",a,b),Call("square",Call("traceNorm",Call("subtract",r,s)))),D(4)));
        Formula lhs=Call("add",Call("add",Call("multiply",ea,Call("spectralEntropy",r)),Call("multiply",eb,Call("spectralEntropy",s))),reward);
        Formula hyp=And(Call("PositiveTraceOne",r),And(Call("PositiveTraceOne",s),And(Le(D(0),a),And(Le(D(0),b),Equal(Call("add",a,b),D(1))))));
        return new Formula.BindMany(FormulaQuantifier.ForAll,[V("H",F.Id("CompleteComplexHilbertSpace")),V("rho",Call("Reference",h)),V("sigma",Call("Reference",h)),V("a",F.Id("Real")),V("b",F.Id("Real"))],
            Implies(hyp,Le(lhs,Call("spectralEntropy",Call("mixture",r,s,a,b)))));
    }
    private static Formula Strong()
    {
        Formula h=F.Id("H"),a=F.Id("A");
        return new Formula.BindMany(FormulaQuantifier.ForAll,[V("H",F.Id("CompleteComplexHilbertSpace")),V("A",Call("Set",Call("TraceClass",h)))],
            Implies(And(Call("Convex",a),And(Call("AllPositiveTraceOne",a),Call("AllFiniteSpectralEntropy",a))),
                Call("StrongConcaveOn",a,Call("divide",D(1),D(2)),F.Id("realEntropy"))));
    }
    private static DocumentBlock Item(string name,string title,Formula statement,params string[] texts)=>Describe.Lean(
        DescribeId.Create("quantum-entropy-"+name.Replace('_','-').ToLowerInvariant()),
        DeclarationHandle.Create("D5/S3/Quantum/Analysis/TraceClass/EntropyConcavity."+name),
        H(title),StatementSource.FromAuthor(statement),AssessedProvenance.FromLiterature(Source),
        Blocks(texts.Select(t=>Paragraph(Text(t))).ToArray()),DescribeRole.Theorem);
}
