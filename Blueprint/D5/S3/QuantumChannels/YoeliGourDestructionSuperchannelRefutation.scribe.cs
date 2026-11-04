using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumChannels;

internal sealed class YoeliGourDestructionSuperchannelRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuantumChannels/YoeliGourDestructionSuperchannelRefutation.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Resource/yoeligour2026instability");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Qutrit complete dephasing obstructs an exact superchannel fixed-point description of destruction covariance.",
        H("Destruction covariance need not be a superchannel fixed set"), Blocks(
            Describe.Lean(DescribeId.Create("destruction"), DeclarationHandle.Create(Prefix + "IsDestruction"),
                H("Admissible destruction channels"), StatementSource.FromAuthor(DestructionFormula()),
                AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(
                    "Framework, PDF page 1: \"The resource theory of instability therefore considers systems as pairs (A, Δᴬ), where A ≅ ℂᵈ and Δᴬ is an idempotent “destruction” channel.\" \"We assume Δᴬ fixes at least one full-rank state, ensuring the Heisenberg dual Δᴬ* is a faithful conditional expectation (a standard operator-algebraic concept, see Appendix A and [40–46]).\" IsChannel means completely positive and trace preserving. A full-rank density matrix is represented by Matrix.PosDef together with trace one; the fixed state is quantified explicitly."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("claim"), DeclarationHandle.Create(Prefix + "claim"),
                H("The universal fixed-set assertion"), StatementSource.FromAuthor(Disp(Eq(V("claim"), ClaimBody()))),
                AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(
                    "Open directions, PDF page 5, after Eq. (29): \"Moreover, a key open question is whether destruction-covariant channels themselves arise as fixed points of an idempotent superchannel.\" Framework, PDF page 1, Eq. (1): \"In instability theory, we take the free operations between systems A and B to be the destruction-covariant channels 𝒩 obeying\" 𝒩ᴬ→ᴮ ∘ Δᴬ = Δᴮ ∘ 𝒩ᴬ→ᴮ. The assertion means exact equality of the fixed CPTP channels with the destruction-covariant CPTP channels, for every pair of admissible nonzero systems. IsQuantumSuperchannel is the existing full-map-space predicate: CP preservation, complete CP preservation with arbitrary auxiliary systems, and TP preservation. Idempotence is equality of the full linear supermap. The dimensions a and b are positive; Fin indices start at zero."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(Prefix + "result"),
                H("A negative answer from qutrit dephasing"), StatementSource.FromAuthor(Disp(Not(ClaimBody()))),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(
                    "Choose both dimensions equal to three and both destruction channels equal to complete dephasing. The depolarizing channel forces the induced completely positive Choi map to be unital. Sixteen normalized Choi vectors of monomial unitaries span the nine-dimensional Choi space and have connected nonzero-overlap graph. Connected-probe rigidity forces the superchannel to be identity. Conjugation by the rational rotation with block ((3/5, −4/5), (4/5, 3/5)) then contradicts exactness: it is CPTP but does not commute with dephasing. The rigidity argument uses no superchannel idempotence and assumes no trace preservation on arbitrary Choi matrices. The equal-dimension qubit case and arbitrary destruction maps are separate questions."))), DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("yoeli-gour-destruction-superchannel"),
                    ResolutionKind.Refuted)))));

    private static Formula DestructionFormula()
    {
        Formula d = V("d"), delta = V("Delta"), rho = V("rho");
        Formula state = Exists("rho", Mat(d), And(QCall("Matrix", "PosDef", rho),
            And(Eq(QCall("Matrix", "trace", rho), D(1)), Eq(App(delta, rho), rho))));
        return Disp(All("d", N, All("Delta", Map(d, d),
            Eq(Call("IsDestruction", delta), And(Channel(delta), And(Eq(Comp(delta, delta), delta), state))))));
    }

    private static Formula ClaimBody()
    {
        Formula a = V("a"), b = V("b"), da = V("DeltaA"), db = V("DeltaB"), theta = V("Theta"), n = V("N");
        Formula fixedSet = All("N", Map(a, b), Imp(Channel(n), Iff(Eq(App(theta, n), n),
            Eq(Comp(n, da), Comp(db, n)))));
        Formula superchannel = QCall("D5.S3.QuantumChannels.DalySuperchannelMinimalExtension", "IsQuantumSuperchannel", theta);
        Formula existence = Exists("Theta", Linear(Map(a, b), Map(a, b)),
            And(superchannel, And(Eq(Comp(theta, theta), theta), fixedSet)));
        Formula body = Imp(Call("IsDestruction", da), Imp(Call("IsDestruction", db), existence));
        body = All("DeltaA", Map(a, a), All("DeltaB", Map(b, b), body));
        body = All("b", N, Imp(Lt(D(0), b), body));
        return All("a", N, Imp(Lt(D(0), a), body));
    }

    private static Formula V(string name) => F.Id(name);
    private static Formula Named(string name) => Seq(Operatorname, Grp(V(name)));
    private static Formula Qualified(string path)
    {
        string[] parts = path.Split('.');
        Formula result = Named(parts[0]);
        for (int i = 1; i < parts.Length; i++) result = Seq(result, Dot, Named(parts[i]));
        return result;
    }
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Call(string name, params Formula[] args) => App(Named(name), args);
    private static Formula QCall(string owner, string name, params Formula[] args) => App(Qualified(owner + "." + name), args);
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula All(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Exists(string name, Formula type, Formula body) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Lt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Iff, Parenthesized(b));
    private static Formula Not(Formula a) => Seq(Neg, Sp, Parenthesized(a));
    private static Formula N => Seq(Mathbb, Grp(V("N")));
    private static Formula C => Seq(Mathbb, Grp(V("C")));
    private static Formula Mat(Formula d) => Call("Matrix", Call("Fin", d), Call("Fin", d), C);
    private static Formula Map(Formula a, Formula b) => Call("MatrixMap", Call("Fin", a), Call("Fin", b), C);
    private static Formula Linear(Formula a, Formula b) => Seq(Parenthesized(a), Sp, new Formula.Subscript(To, C), Sp, Parenthesized(b));
    private static Formula Comp(Formula a, Formula b) => QCall("LinearMap", "comp", a, b);
    private static Formula Channel(Formula n) => QCall("D5.S3.Quantum.QuantumChannels.EntanglementAssistedCommunicationValue", "IsChannel", n);
}
