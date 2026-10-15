using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis;

internal sealed class OrliczCommonEnergyDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Analysis/OrliczCommonEnergy.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A genuine logarithmic Orlicz moment and every positive dual scale give one continuous scalar energy with summable heat series at every positive temperature.",
        H("Orlicz Common Energy"),
        Blocks(
            Result("conjugate_nonempty_bddAbove", "The genuine conjugate has a finite supremum",
                "For real p>0 and u>=0, put Phi(p,t)=t*(log(max(1,t)))^p. The image of t>=0 under u*t-Phi(p,t) is nonempty and bounded above. Its actual conditional supremum is denoted Psi(p,u). Testing t=0 supplies an element; a pointwise bound by u*exp(u^(1/p)) supplies boundedness before the conditional supremum rules are applied."),
            Result("conjugate_nonneg", "Nonnegativity of the conjugate",
                "For every p>0 and u>=0, Psi(p,u)>=0, because the actual supremum includes the value at t=0."),
            Result("conjugate_le_majorant", "A concrete conjugate majorant",
                "For every p>0 and u>=0, Psi(p,u)<=u*exp(u^(1/p)). For t<=1 the expression is u*t. For t>1, either u<=(log t)^p and the expression is nonpositive, or (log t)^p<u and hence t<=exp(u^(1/p)). These cases bound every member of the supremum image."),
            Result("fenchel_young", "Fenchel--Young for the actual supremum",
                "For every p>0, u>=0 and t>=0, u*t<=Phi(p,t)+Psi(p,u). The value at this particular t belongs to the nonempty bounded supremum image. No convexity or dual inequality is included in the definition of Psi."),
            Result("uniform_tail_from_young", "Every-scale Young estimates imply uniform tails",
                "Let X be any type; f(x,n), A(x,n) and B(a,n) are extended nonnegative reals, with a a nonnegative real scale. Suppose sum A(x,n)<=M for every x, M is finite, a*f(x,n)<=A(x,n)+B(a,n) for every a>0, and sum B(a,n) is finite for every a>0. Then for every epsilon>0 there is one N such that sum over k>=0 of f(x,N+k)<=epsilon for every x. Choose the scale first so that M/a is small, then a tail of its finite dual series. All sums remain extended nonnegative sums throughout this argument."),
            Result("orlicz_uniform_energy_tail", "Uniform logarithmic energy tails from actual moments",
                "Let p>0, s(n)>0, h(n)>=0 and d(x,n)>=0. Define A(x,n)=ofReal(s(n)*Phi(p,d(x,n)/s(n))) and B(a,n)=ofReal(s(n)*Psi(p,a*h(n))). Suppose sum A(x,n)<=M uniformly in x with M finite, and sum B(a,n) is finite for every a>0. Then the tails of ofReal(h(n)*d(x,n)) vanish uniformly in x. Multiply Fenchel--Young at t=d(x,n)/s(n) by s(n), retaining its strictly positive denominator, and apply the every-scale estimate."),
            Result("exists_amplified_orlicz_energy", "One common monotone diverging weight",
                "Under the preceding Orlicz assumptions, for every delta>0 there is one natural-valued weight w, chosen before x, with w(n)>=1, w nondecreasing and w(n) tending to infinity. Its weighted extended energy sum is at most the original extended energy sum plus delta for every x, and its weighted tails vanish uniformly in x. This is the direct application of UniformTailAmplification to the derived tails."),
            Result("summable_of_uniform_ennreal_tails", "Uniform extended tails imply genuine real summability",
                "Let X be any type and f:X to Nat to Real satisfy f(x,n)>=0. Suppose for every NNReal epsilon>0 there exists N such that sum over k of ofReal(f(x,N+k))<=epsilon for every x. Then for every x the actual real series f(x,n) is summable. A finite extended tail at epsilon=1 gives real tail summability; adding the finite head proves the result. No Orlicz moment, normalization, faithfulness or spectral-basis premise is present."),
            Result("continuous_of_uniform_ennreal_tails", "Coordinate continuity and uniform extended tails give continuous totals",
                "Let X be any topological space and f:X to Nat to Real be nonnegative and continuous in x at each n. Suppose for every NNReal epsilon>0 there exists one N such that sum over k of ofReal(f(x,N+k))<=epsilon simultaneously for every x. Then x maps to the genuine real sum of f(x,n) is continuous. The uniform-tail summability theorem establishes finiteness first; continuous finite heads uniformly approximate the actual sum. No compactness, Orlicz moment, normalization, faithfulness or basis premise is assumed."),
            Result("exists_continuous_common_energy", "Finite continuous energy and all-temperature heat series",
                "Let X be any topological space, p>0, and s a strictly positive real sequence with HasSum s 1. Let d(x,n) be nonnegative, continuous in x for each n, and have HasSum (d x) 1 for each x. Put h(n)=-log(s(n)). Assume the actual extended moment sum of s(n)*Phi(p,d(x,n)/s(n)) is uniformly bounded by a finite M. Assume the actual extended dual sum of s(n)*Psi(p,a*h(n)) is finite for every positive nonnegative-real scale a. For every delta>0 there exists one w with all the following properties.",
                "The natural weight satisfies w(n)>=1, is nondecreasing and tends to infinity. Set H(n)=w(n)*h(n). Then H(n)>=h(n)>=0 and H tends to infinity. For every real beta>0 the real series exp(-beta*H(n)) is summable. Both h(n)*d(x,n) and H(n)*d(x,n) are genuinely summable for every x. The real energy E(x)=sum H(n)*d(x,n) is continuous on all of X, and E(x)<=sum h(n)*d(x,n)+delta for every x. For every epsilon>0 one N bounds sum over k>=0 of ofReal(H(N+k)*d(x,N+k)) by epsilon simultaneously for every x.",
                "Positivity and normalization imply s(n)<=1 and s(n) tends to zero, so h is nonnegative and tends to infinity. Uniform tails prove real summability by first proving the extended tail finite and then using the finite head. Finite coordinate sums are continuous. Their uniformly small nonnegative remainders give continuity through Mathlib's uniform approximation theorem, without compactness of X or a common summable pointwise envelope. Eventually beta*w(n)>=1, so exp(-beta*H(n))<=exp(-h(n))=s(n); comparison with the actual normalized summable reference proves heat summability. The extended amplification estimate passes to the real additive estimate only after summability is established.",
                "This is a conditional scalar result. Its nonvacuous infinite faithful-reference applications use p>1. The formal scalar implication itself requires only p>0; it does not assert existence of references satisfying every scale at smaller p. Polynomial references give the ordinary p>1 examples via the concrete majorant. No spectral Jensen inequality, trace pairing, self-adjoint operator domain or noncommuting quantum entropy identity is asserted here. Shirokov's original entropy-continuity hypotheses do not imply the fixed logarithmic-power moment premises; the unrestricted common-Hamiltonian conjectures remain outside this result. The existing common-weight theorem supplies the weight construction; the new derivation joins the genuine conjugate and extended moments to continuous scalar energy and all-temperature series. No literature priority claim is made."))));

    private static DocumentBlock.Describe Result(string name, string title, params string[] paragraphs) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Module + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(paragraphs.Select(p => Paragraph(Text(p))).ToArray()), DescribeRole.Theorem);
}
