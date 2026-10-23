using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Analysis.TraceClass;
internal sealed class SpectralEnergyDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/QuantumBounds/mathlib2026operatorlog");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Singular logarithmic energy from complete trace-class spectral data.",
        H("Full spectral energy, self entropy and domination"), Blocks(
            Item("spectralSeries_eq_regularizedSupremum", "Actual series and bounded trace regularization", SpectralIdentity(),
                "Let T be a positive trace-class contraction on an arbitrary complete complex Hilbert space. A complete orthonormal eigenbasis b has real nonnegative eigenvalues s. The native spectral theorem supplies such a full basis, retaining the whole zero eigenspace. No separability, finite dimension, countable full index or positive spectral gap is assumed. For positive trace-class rho, the weights are the actual real diagonals Re inner(b(i),rho b(i)). Their unconditional sum is the real trace of rho, with genuine summability supplied by the trace-class diagonal theorem.",
                "Set ell(0)=infinity and ell(t)=ofReal(-log t) for nonzero t. The explicit spectral series is the nonnegative sum of ofReal(diagonal(i))*ell(s(i)). Every eigenvalue lies in [0,1], as follows from the actual operator contraction. The value zero times infinity is zero, so a zero weight on a zero eigenvector contributes zero.",
                "For epsilon>0, CFC eigenvector action identifies B_epsilon(T)b(i) with [log(1+epsilon)-log(s(i)+epsilon)]b(i). Self-adjointness moves this operator across the inner product. The product B_epsilon(T)rho is genuinely trace class; its unconditional complex diagonal is summable and its sum is the actual bounded trace pairing. Mapping by the continuous real-part map yields the required summable real weighted series before conversion to ENNReal.",
                "On epsilon_n=1/(n+1), the scalar regularizations increase to ell(t). At t=0 the real value is log(n+2), which tends to infinity; at t=1 it is zero. Finite nonnegative sums commute with synchronized increasing suprema; the finite-subset characterization of an arbitrary ENNReal sum then interchanges that sum and supremum. This proves equality with the same regularizedSupremum already defined by actual operator trace pairings."),
            Item("spectralSeries_eq_spectralEnergy", "Independence of the full spectral basis", BasisIndependence(),
                "nativeResolution is chosen from the actual positive trace-class spectral theorem. spectralEnergy is the explicit eigenvalue series on that supplied basis. Any other full eigenbasis yields the same value because both series equal the actual operator supremum. The choice carries spectral equations only; no energy identity is included as an assumed field."),
            Item("spectralEnergy_nonneg_linear", "Finite nonnegative first-slot linearity", Linearity(),
                "The identified singular series inherits the actual trace pairing's arbitrary two-term nonnegative linearity. Both coefficients may vanish and either energy may be infinite. This formula asserts no countable first-slot decomposition theorem."),
            Item("spectralEnergy_scaleReference", "Scaling and actual trace mass", Scaling(),
                "For w in (0,1], scaleReference multiplies the actual reference by w. The singular energy increases by Re Tr(rho) times ofReal(-log w), without normalizing rho. The proof applies the established regularization scaling theorem only after identifying the spectral series. Strictly positive shifted operators justify every logarithm scaling law."),
            Item("spectralEnergy_self", "Actual spectral entropy is self energy", Self(),
                "spectralEntropy is the separate eigenvalue series sum of ofReal(-s(i) log s(i)), with eta(0)=0. The eigenvector equation and the unit norm of each basis vector identify the self diagonal with s(i). The zero branch uses zero times infinity equals zero; the positive branch uses the actual scalar product formula. Hence self energy equals spectral entropy for every positive trace-class contraction, in particular for normalized states."),
            Item("spectralEnergy_le_entropy_add", "Normalized noncommuting domination", Domination(false),
                "Let rho be an actual positive trace-one state, tau a positive trace-class contraction, and 0<w<=1. If tau dominates w rho in Loewner order, spectral energy of rho relative to tau is at most its actual spectral entropy plus ofReal(-log w). Normalization proves that rho is a contraction. Noncommuting reference order, singular reference scaling, the actual trace mass one, and the self-entropy identity give the bound. No faithfulness or commutation premise is added."),
            Item("spectralEnergy_lt_top_of_entropy_lt_top", "Finite entropy yields finite dominated cross energy", Domination(true),
                "Under exactly the normalized domination hypotheses, finiteness of the actual spectral entropy implies finiteness of the same singular cross energy. The finite additive logarithmic constant and the ENNReal domination bound prove this, including references with nontrivial kernel."),
            Item("lowerSemicontinuous_spectralEnergy", "Reference trace-norm lower semicontinuity", Semicontinuity(),
                "For a fixed positive trace-class rho, the actual singular spectral energy is lower semicontinuous as a function of the positive trace-class contraction reference with its trace-norm topology. This is the established regularization supremum theorem transported through the proved spectral identity. Reference order likewise reverses without commutativity. These statements supply logarithmic energy; local entropy centers, common-reference continuity and the full unbounded Hamiltonian construction require further results."))));
    private static readonly Formula Hh = F.Id("H"), T = F.Id("T"), R = F.Id("rho"), W = F.Id("w"), B = F.Id("b"), S = F.Id("s");
    private static Formula.BoundVariable V(string n, Formula t) => new(FormulaIdentifier.Create(n), t);
    private static Formula Ref => Call("Reference", Hh);
    private static Formula Tc => Call("TraceClass", Hh);
    private static Formula N(Formula x) => Call("Nonnegative", x);
    private static Formula E(Formula t, Formula r) => Call("spectralEnergy", t, r);
    private static Formula Ent(Formula r) => Call("spectralEntropy", r);
    private static Formula Plus(Formula a, Formula b) => Call("add", a, b);
    private static Formula Times(Formula a, Formula b) => Call("multiply", a, b);
    private static Formula Co(Formula x) => Call("ofReal", x);
    private static Formula Scale() => Call("scaleReference", T, W);
    private static Formula HAll(Formula.BoundVariable[] xs, Formula body) => All([V("H", F.Id("CompleteComplexHilbertSpace")), ..xs], body);
    private static Formula SpectralIdentity() => Spectral(false);
    private static Formula BasisIndependence() => Spectral(true);
    private static Formula Spectral(bool chosen) => HAll([V("T",Ref), V("w",Call("Set",Hh)),
        V("b",Call("HilbertBasis",W,F.Id("Complex"),Hh)), V("s",Call("Function",W,F.Id("Real"))), V("rho",Tc)],
        Implies(And(N(S),And(Call("EigenbasisEquation",T,B,S),N(R))),
            Equal(Call("spectralSeries",B,S,R),chosen ? E(T,R) : Call("regularizedSupremum",T,R))));
    private static Formula Linearity()
    {
        Formula g=F.Id("gamma"), a=F.Id("a"), c=F.Id("c");
        return HAll([V("T",Ref),V("rho",Tc),V("gamma",Tc),V("a",F.Id("Real")),V("c",F.Id("Real"))],
            Implies(And(N(R),And(N(g),And(N(a),N(c)))),Equal(E(T,Plus(Call("complexSmul",a,R),Call("complexSmul",c,g))),
                Plus(Times(Co(a),E(T,R)),Times(Co(c),E(T,g))))));
    }
    private static Formula Scaling() => HAll([V("T",Ref),V("rho",Tc),V("w",F.Id("Real"))],
        Implies(And(N(R),And(Call("Positive",W),Le(W,D(1)))),Equal(E(Scale(),R),
            Plus(E(T,R),Times(Co(Call("realTrace",R)),Co(Call("negate",Call("log",W))))))));
    private static Formula Self() => HAll([V("rho",Ref)],Equal(E(R,Call("traceClassValue",R)),Ent(R)));
    private static Formula Domination(bool finite)
    {
        Formula tau=F.Id("tau"), r=Call("normalizedReference",R);
        Formula hypotheses=And(N(R),And(Equal(Call("realTrace",R),D(1)),And(Call("Positive",W),And(Le(W,D(1)),Le(Call("complexSmul",W,Call("operator",R)),Call("operator",tau))))));
        if(finite) hypotheses=And(hypotheses,Call("Finite",Ent(r)));
        return HAll([V("rho",Tc),V("tau",Ref),V("w",F.Id("Real"))],Implies(hypotheses,
            finite ? Call("Finite",E(tau,R)) : Le(E(tau,R),Plus(Ent(r),Co(Call("negate",Call("log",W)))))));
    }
    private static Formula Semicontinuity() => HAll([V("rho",Tc)],Implies(N(R),Call("LowerSemicontinuous",Call("spectralEnergyAt",R,Ref))));
    private static DocumentBlock Item(string name,string title,Formula formula,params string[] texts) => Describe.Lean(
        DescribeId.Create("singular-"+name.Replace('_','-').ToLowerInvariant()),
        DeclarationHandle.Create("D5/S3/Quantum/Analysis/TraceClass/SpectralEnergy."+name),H(title),StatementSource.FromAuthor(formula),
        AssessedProvenance.FromRepo(Source),Blocks(texts.Select(t=>Paragraph(Text(t))).ToArray()),DescribeRole.Theorem);
    private static Formula Le(Formula a,Formula b) => new Formula.Relation(a,FormulaRelationOperator.LessThanOrEqual,b);
    private static Formula And(Formula a,Formula b) => new Formula.Logic(a,FormulaLogicOperator.And,b);
    private static Formula Implies(Formula a,Formula b) => new Formula.Logic(a,FormulaLogicOperator.Implies,b);
    private static Formula All(Formula.BoundVariable[] xs,Formula body) => new Formula.BindMany(FormulaQuantifier.ForAll,[..xs],body);
}
