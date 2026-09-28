using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DependencyTopology;

internal sealed class SupportFamilyNotIntersectionClosedDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/DependencyTopology/SupportFamilyNotIntersectionClosed.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Lawful proof supports need not be intersection closed or the finite downsets of any fixed digraph.",
        H("Alternative proofs obstruct intersection closure"),
        Blocks(
            Paragraph(Text(
                "KernelData specifies accepted proofs, finite axiom and reference readouts, "
                + "permitted axioms, negation and model semantics. SourceLaws requires soundness "
                + "in every permitted-axiom model, a finite closed acyclic certificate for every "
                + "proved proposition, and consistency between a proposition and its negation.")),
            Node("supportFamily", "The support family",
                Disp(Seq(Call("supportFamily", F.Id("k")), Sp, Eq, Sp,
                    OpenBrace, F.Id("S"), Sp, Mid, Sp, Exists, Sp,
                    F.Id("C"), Colon, Sp, Call("CertifiedNodes", F.Id("k")), Comma, Sp,
                    F.Id("S"), Sp, Eq, Sp, Call("nodes", F.Id("C")), CloseBrace)),
                "The family consists of the finite node sets of all certified cores. "
                + "A core selects one accepted proof per node, uses only permitted axioms, "
                + "contains every selected proof's references, and has an acyclic reference graph. "
                + "Different members of the support family may select different proofs of the same proposition.",
                DescribeRole.Definition),
            Node("IntersectionClosed", "Binary intersection closure",
                Disp(Seq(Call("IntersectionClosed", F.Id("A")), Sp, Iff, Sp,
                    Forall, Sp, F.Id("S"), Comma, Sp, F.Id("T"), Sp, InMacro, Sp, F.Id("A"), Comma, Sp,
                    Call("inter", F.Id("S"), F.Id("T")), Sp, InMacro, Sp, F.Id("A"))),
                "Here inter denotes set intersection. This property includes intersections that are empty; no nonemptiness assumption is imposed.",
                DescribeRole.Definition),
            Node("graphFamily", "The finite downsets of a digraph",
                Disp(Seq(Call("graphFamily", F.Id("e")), Sp, Eq, Sp,
                    OpenBrace, F.Id("S"), Sp, Mid, Sp, Call("Finite", F.Id("S")), Sp, Land, Sp,
                    Open, Forall, Sp, F.Id("p"), Sp, InMacro, Sp, F.Id("S"), Comma, Sp,
                    Forall, Sp, F.Id("q"), Comma, Sp, Call("e", F.Id("q"), F.Id("p")), Sp,
                    Implies, Sp, F.Id("q"), Sp, InMacro, Sp, F.Id("S"), Close, CloseBrace)),
                "The edge relation is arbitrary and is on the same proposition type as the support family. "
                + "Membership requires finiteness and closure under every direct predecessor. "
                + "No acyclicity assumption is needed for the intersection argument.", DescribeRole.Definition),
            Node("claim", "A universal closure or representation principle", ClaimFormula(),
                "The proposed principle quantifies over all proposition, proof, axiom and model types "
                + "and all kernel data satisfying SourceLaws. It allows either binary intersection closure "
                + "or representation as the finite downsets of some fixed digraph. Its negation therefore "
                + "gives one lawful structure for which both alternatives fail.", DescribeRole.Definition),
            Node("result", "Both alternatives fail for one lawful kernel",
                Disp(new Formula.Not(F.Id("claim"))),
                "Take six signed propositions: a, b, q and their negatives. Negation flips the sign; "
                + "a proposition holds exactly when its sign is positive. There is one model, with empty "
                + "permitted axioms. Four proofs conclude a, b, q and q respectively. The first two have "
                + "no references; the last two reference a and b respectively. All axiom readouts are empty. "
                + "Only the three positive propositions are proved, so soundness and consistency hold. "
                + "The two cores {a,q} and {b,q} have closed accepted witnesses and strictly increasing "
                + "ranks along edges, so they are acyclic and provide certificates for every proved proposition. "
                + "Their intersection is {q}. Every accepted proof of q requires a or b, so this singleton "
                + "admits no closed witness. Finally, finite downsets of any fixed relation are closed "
                + "under intersection: each predecessor belongs to both sets. Thus this same support "
                + "family cannot be the finite downsets of any fixed digraph, including any fixed acyclic digraph.",
                DescribeRole.Theorem))));

    private static Formula ClaimFormula() => Disp(Seq(
        F.Id("claim"), Sp, Iff, Sp, Open,
        Forall, Sp, F.Id("P"), Comma, Sp, F.Id("Proof"), Comma, Sp,
        F.Id("Ax"), Comma, Sp, F.Id("Model"), Colon, Sp, F.Id("Type"), Comma, Sp,
        Forall, Sp, F.Id("k"), Colon, Sp,
        Call("KernelData", F.Id("P"), F.Id("Proof"), F.Id("Ax"), F.Id("Model")), Comma, Sp,
        Call("SourceLaws", F.Id("k")), Sp, Implies, Sp, Open,
        Call("IntersectionClosed", Call("supportFamily", F.Id("k"))), Sp, Lor, Sp,
        Open, Exists, Sp, F.Id("e"), Colon, Sp, F.Id("P"), Sp, To, Sp,
        F.Id("P"), Sp, To, Sp, F.Id("Prop"), Comma, Sp,
        Call("supportFamily", F.Id("k")), Sp, Eq, Sp, Call("graphFamily", F.Id("e")),
        Close, Close, Close));

    private static DocumentBlock Node(string selector, string title, Formula formula,
        string prose, DescribeRole role) => Describe.Lean(
            DescribeId.Create("support-" + selector.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + selector), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
