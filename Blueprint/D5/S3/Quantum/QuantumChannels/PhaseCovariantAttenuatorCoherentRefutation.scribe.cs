using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.QuantumChannels;

internal sealed class PhaseCovariantAttenuatorCoherentRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/QuantumChannels/PhaseCovariantAttenuatorCoherentRefutation.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/QuantumStates/vanherstraeten2024nongaussian");
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The full bosonic attenuator and the coherent-state output-entropy question.",
        H("PhaseCovariantAttenuatorCoherentRefutation"),
        Blocks(
            Paragraph(Text("The one-mode space is lp(Function.const(Nat,Complex),2) and the two-mode space is lp(Function.const(Nat,lp(Function.const(Nat,Complex),2)),2). The occupation vector at n is lp.single 2 n (Complex.ofReal 1). All state and environment supports are unrestricted. conjStarAlgEquiv is Mathlib LinearIsometryEquiv.conjStarAlgEquiv, mapping T to U composed with T and U inverse. Function names are the displayed Lean definitions or the explicitly stated Mathlib operations. Application parentheses retain grouping; NatSub is truncated natural subtraction, val is the natural value of a finite index, toReal is the natural-to-real cast and Complex.ofReal is the real-to-complex cast. Fields carrying proofs are omitted from constructor formulas; when a named proof parameter occurs in a function signature it appears as an argument of that function.")),
            Node("claim", Disp(Eqn(Id("claim"),All("eta",Real(),All("hEta",Icc(E),All("p",Prob(),Ex("alpha",Complex(),All("rho",State(),Leq(Entropy(Op(Call("attenuator",E,HE,P,Call("coherentDensity",A)))),Entropy(Op(Call("attenuator",E,HE,P,Q))))))))))), "Conjecture 2 (Phase-covariant attenuator), section IV.B, arXiv v2 PDF p. 12: \"The minimum output entropy of a phase-covariant attenuator channel ℳ<sub>η,𝐩</sub> is achieved by coherent states, ∀η,𝐩.\" eta ranges over [0,1], p over every probability vector on Nat, alpha over all complex amplitudes, and rho over all positive trace-one operators on the full Fock space. The existential amplitude precedes the universal density input. Entropy is the infimum over complete countable bases of diagonal Shannon entropy. Equality with spectral von Neumann entropy for every density operator is literature-attested; its infinite-dimensional equivalence is not claimed as kernel-proved. Finite spectral equality and arbitrary-unitary invariance supply the entropy calculations used here.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source)),
            Node("result", Disp(new Formula.Not(Id("claim"))), "Take eta=1/2, p=(7/8)delta_1+(1/8)delta_5 and the input |1><1|. Vacuum output has diagonal (113,117,10,10,5,1)/256; the one-photon output has diagonal (115,8,117,0,5,8,3)/256. Displacement covariance and the entropy invariance obtained by transporting all complete bases show that every coherent input has the vacuum output entropy. The exact comparison 115^2*8^16*3^3=100507677308957491200>10^20, together with log(115)>log(113), proves strictly smaller one-photon output entropy. This excludes every coherent state as a minimizer for this channel; it makes no global-minimality assertion about |1>. Conjecture 1 for pure Fock environments remains open.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source), new OpenProblemResolutionClaim(ProblemSlugRef.Create("van-herstraeten-guha-cerf-2024-phase-covariant-attenuator-coherent-refutation"), ResolutionKind.Refuted))), []));
    private static DocumentBlock Node(string name, Formula formula, string prose, DescribeRole role, AssessedProvenance provenance, OpenProblemResolutionClaim? resolution = null) => Describe.Lean(
        DescribeId.Create("fockatt-phasecovariantattenuatorcoherentrefutation-"+name.Replace("_", "").ToLowerInvariant()), DeclarationHandle.Create(Prefix+name), H(name),
        StatementSource.FromAuthor(formula), provenance, Blocks(Paragraph(Text(prose))), role, resolution);

    private static Formula Parenthesized(Formula x) => Seq(Open, x, Close);
    private static Formula Id(string s) => FormulaDsl.Id(s);
    private static Formula Call(string s, params Formula[] xs) => new Formula.Apply(Seq(Operatorname, Grp(Id(s.Replace(".", "").Replace("_", "")))), [.. xs]);
    private static Formula All(string v, Formula t, Formula b) => Seq(Forall, Sp, Id(v), Sp, Colon, Sp, t, Comma, Sp, Parenthesized(b));
    private static Formula Ex(string v, Formula t, Formula b) => Seq(Exists, Sp, Id(v), Sp, Colon, Sp, t, Comma, Sp, Parenthesized(b));
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Leq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula Real() => Seq(Mathbb,Grp(Id("R")));
    private static Formula Complex() => Seq(Mathbb,Grp(Id("C")));
    private static Formula Prob() => Id("ProbabilityVector");
    private static Formula State() => Id("DensityOperator");
    private static Formula A => Id("alpha");
    private static Formula E => Id("eta");
    private static Formula HE => Id("hEta");
    private static Formula P => Id("p");
    private static Formula Q => Id("rho");
    private static Formula Op(Formula x) => Call("operator",x);
    private static Formula Entropy(Formula x) => Call("vonNeumannEntropy",x);
    private static Formula Icc(Formula x) => new Formula.Relation(x, FormulaRelationOperator.MemberOf, Call("Set.Icc", D(0), D(1)));
}
