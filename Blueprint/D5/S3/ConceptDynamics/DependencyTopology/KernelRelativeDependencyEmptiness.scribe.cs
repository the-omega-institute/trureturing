using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.DependencyTopology;

internal sealed class KernelRelativeDependencyEmptinessDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/ConceptDynamics/DependencyTopology/KernelRelativeDependencyEmptiness.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Equal provable images with shared proof readouts do not determine dependency emptiness.",
        H("Dependency emptiness depends on the accepted proofs"),
        Blocks(
            Paragraph(Text(
                "A kernel specifies acceptance, finite axiom and reference readouts, a permitted "
                + "axiom set, negation and model semantics. Proved means that some accepted proof "
                + "uses only permitted axioms. SourceLaws requires soundness in every model of the "
                + "permitted axioms, a finite closed acyclic certificate for every proved proposition, "
                + "and consistency between each proposition and its negation.")),
            Node("Qualified", "Qualified proofs", Disp(Seq(
                Call("Qualified", F.Id("k"), F.Id("pi"), F.Id("p")), Sp, Iff, Sp,
                Call("accept", F.Id("k"), F.Id("pi"), F.Id("p")), Sp, Eq, Sp, F.Id("true"),
                Sp, Land, Sp, Open, Forall, Sp, F.Id("a"), Sp, InMacro, Sp,
                Call("axioms", F.Id("k"), F.Id("pi")), Comma, Sp,
                F.Id("a"), Sp, InMacro, Sp, Call("permitted", F.Id("k")), Close)),
                "Qualification checks the particular proof, including every axiom in its readout. "
                + "It does not select a unique proof of the conclusion.", DescribeRole.Definition),
            Node("DependencyEmpty", "Dependency emptiness", Disp(Seq(
                Call("DependencyEmpty", F.Id("k"), F.Id("p")), Sp, Iff, Sp,
                Forall, Sp, F.Id("pi"), Comma, Sp,
                Call("Qualified", F.Id("k"), F.Id("pi"), F.Id("p")), Sp, Implies, Sp, Open,
                Call("refs", F.Id("k"), F.Id("pi")), Sp, Neq, Sp, Emptyset,
                Sp, Lor, Sp, Call("axioms", F.Id("k"), F.Id("pi")), Sp, Neq, Sp, Emptyset, Close)),
                "Every qualified proof must have a nonempty reference readout or a nonempty axiom "
                + "readout. This is a universal property of all qualified proofs, rather than a "
                + "property of one selected certificate. With no qualified proofs it holds vacuously; "
                + "the separating proposition below is proved in both kernels.", DescribeRole.Definition),
            Node("SharedData", "The common interface", Disp(Seq(
                Call("SharedData", F.Id("k1"), F.Id("k2")), Sp, Iff, Sp,
                Same("axioms"), Sp, Land, Sp, Same("refs"), Sp, Land, Sp,
                Same("permitted"), Sp, Land, Sp, Same("neg"), Sp, Land, Sp,
                Same("models"), Sp, Land, Sp, Same("holds"))),
                "Both kernels already have the same proposition, proof, axiom and model types. "
                + "SharedData equates their entire axiom and reference functions, permitted sets, "
                + "negations, model predicates and evaluation predicates. Only acceptance may differ.",
                DescribeRole.Definition),
            Node("claim", "Determination by the common data and the provable image", ClaimFormula(),
                "The proposed principle quantifies over all four carrier types and both kernels. "
                + "It assumes SharedData, both SourceLaws, an actual model of the common permitted "
                + "axioms, and equality of the complete provable images. It concludes that every "
                + "proposition proved in the first kernel has the same dependency-emptiness value "
                + "in both. Thus the negation concerns determination of this property, and does "
                + "not negate the existence of a separating pair.", DescribeRole.Definition),
            Node("ProofSymbol", "The common proof alphabet", Disp(Seq(
                F.Id("ProofSymbol"), Sp, Eq, Sp, OpenBrace, F.Id("alpha"), Comma, Sp,
                F.Id("beta"), Comma, Sp, F.Id("delta"), CloseBrace)),
                "There are exactly three proof symbols, with decidable equality. The proposition "
                + "type is the ordinary implication/falsity Formula syntax, with natural-number "
                + "variables, syntactic negation and Boolean valuation semantics.", DescribeRole.Definition),
            Node("Q", "The first tautology", Disp(Seq(
                F.Id("Q"), Sp, Eq, Sp, Open, Neg, Sp, F.Id("p"), Sp, Implies, Sp,
                Neg, Sp, F.Id("p"), Close)),
                "Here p is variable zero. Disjunction A or B is represented by not A implies B; "
                + "therefore Q is precisely the implication/falsity encoding of p or not p. "
                + "The two negated occurrences expand to implication into falsity.", DescribeRole.Definition),
            Node("P", "The second tautology", Disp(Seq(
                F.Id("P"), Sp, Eq, Sp, Open, F.Id("p"), Sp, Implies, Sp, F.Id("p"), Close)),
                "The same variable zero occurs on both sides. P and Q are syntactically distinct "
                + "formulas, although both evaluate to true under every Boolean valuation.", DescribeRole.Definition),
            Node("kernel", "The paired acceptance tables", Disp(Seq(
                F.Id("k1"), Sp, Eq, Sp, Call("kernel", F.Id("false")), Comma, Sp,
                F.Id("k2"), Sp, Eq, Sp, Call("kernel", F.Id("true")))),
                "The first kernel accepts exactly (alpha,Q) and (beta,P). The second accepts "
                + "exactly those two pairs and (delta,P). Every other pair is rejected. In both "
                + "kernels all axiom readouts and the permitted axiom set are empty. The reference "
                + "readout of beta is {Q}; those of alpha and delta are empty. Models are all "
                + "Boolean valuations of the variables, every valuation satisfies the permitted "
                + "axioms, and a formula holds exactly when its Boolean evaluation is true.",
                DescribeRole.Definition),
            Node("result", "The common data do not determine dependency emptiness",
                Disp(new Formula.Not(F.Id("claim"))),
                "Both complete provable images are exactly {Q,P}. The qualified proofs over P "
                + "are exactly {beta} in the first kernel and {beta,delta} in the second. These "
                + "different fibers have the same conclusion image. The first fiber contains only "
                + "a proof referencing Q, whereas the second also contains delta with both readouts "
                + "empty. Hence P is dependency empty in the first kernel and is not dependency "
                + "empty in the second. These are statements about every qualified proof, not only "
                + "about the witnesses chosen for the following certificates. "
                + "For each kernel the singleton {Q}, with proof alpha, is a certificate for Q. "
                + "The set {Q,P}, selecting alpha at Q and beta at P, is a certificate for P. "
                + "Both selections are accepted, have permitted axiom readouts, and contain all "
                + "their references. The singleton has no edge; the two-point certificate has "
                + "only the edge from Q to P. Assign Q rank zero and P rank one. The reused strict "
                + "dependency-coordinate theorem proves acyclicity of these actual selected edges. "
                + "These certificates establish certificate completeness for every proved formula. "
                + "Universal truth of P and Q establishes soundness. At the all-false valuation, "
                + "no formula and its syntactic negation can both be true, which proves consistency. "
                + "That valuation is also an explicit model, so model semantics is nonempty. "
                + "Applying the proposed principle to this same pair would transfer dependency "
                + "emptiness of P from the first kernel to the second, contradicting delta.",
                DescribeRole.Theorem))));

    private static Formula Same(string readout) => Seq(
        Call(readout, F.Id("k1")), Sp, Eq, Sp, Call(readout, F.Id("k2")));

    private static Formula ClaimFormula() => Disp(Seq(
        F.Id("claim"), Sp, Iff, Sp, Open,
        Forall, Sp, F.Id("A"), Comma, Sp, F.Id("Proof"), Comma, Sp, F.Id("Ax"), Comma, Sp,
        F.Id("Model"), Colon, Sp, F.Id("Type"), Comma, Sp,
        Forall, Sp, F.Id("k1"), Comma, Sp, F.Id("k2"), Colon, Sp,
        Call("KernelData", F.Id("A"), F.Id("Proof"), F.Id("Ax"), F.Id("Model")), Comma, Sp,
        Call("SharedData", F.Id("k1"), F.Id("k2")), Sp, Implies, Sp,
        Call("SourceLaws", F.Id("k1")), Sp, Implies, Sp,
        Call("SourceLaws", F.Id("k2")), Sp, Implies, Sp,
        Open, Exists, Sp, F.Id("M"), Comma, Sp,
        Call("models", F.Id("k1"), F.Id("M"), Call("permitted", F.Id("k1"))), Close,
        Sp, Implies, Sp, Open, Forall, Sp, F.Id("p"), Comma, Sp,
        Call("Proved", F.Id("k1"), F.Id("p")), Sp, Iff, Sp,
        Call("Proved", F.Id("k2"), F.Id("p")), Close, Sp, Implies, Sp,
        Forall, Sp, F.Id("p"), Comma, Sp, Call("Proved", F.Id("k1"), F.Id("p")),
        Sp, Implies, Sp, Open, Call("DependencyEmpty", F.Id("k1"), F.Id("p")),
        Sp, Iff, Sp, Call("DependencyEmpty", F.Id("k2"), F.Id("p")), Close, Close));

    private static DocumentBlock Node(string selector, string title, Formula formula,
        string prose, DescribeRole role) => Describe.Lean(
            DescribeId.Create("kernel-relative-" + selector.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + selector), H(title),
            StatementSource.FromAuthor(formula), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(prose))), role);
}
