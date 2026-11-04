using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.InverseLimit;

internal sealed class CountableContinuousReflectionDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Topology/InverseLimit/CountableContinuousReflection.";

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(F.Id(name), [.. arguments]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Exists(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Statement()
    {
        Formula stage = F.Id("CountableStage");
        Formula stageOpp = F.Id("CountableStageOpp");
        Formula beta = F.Id("beta");
        Formula obj(Formula j) => Call("Fobj", j);
        Formula point = Call("Cpt");
        Formula componentNonempty = All("j", stageOpp, Call("Nonempty", obj(F.Id("j"))));
        Formula surjectiveBonding = All("i", stageOpp, All("j", stageOpp,
            All("a", Call("Hom", F.Id("i"), F.Id("j")),
                Call("Surjective", Call("Fmap", F.Id("a"))))));
        Formula conclusion = Exists("beta", stage,
            And(Call("Le", F.Id("base"), beta),
                Exists("g", Call("ContinuousMap", obj(Call("op", beta)), F.Id("Real")),
                    All("x", point, Eq(Call("f", F.Id("x")),
                        Call("g", Call("Cprojection", Call("op", beta), F.Id("x"))))))));
        return Disp(All("F", Call("Functor", stageOpp, F.Id("Profinite1")),
            Imp(componentNonempty, All("C", Call("Cone", F.Id("F")),
                Imp(And(Call("IsLimit", F.Id("C")), surjectiveBonding),
                    All("base", stage, All("f", Call("ContinuousMap", point, F.Id("Real")),
                        conclusion)))))));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every continuous real test on an omega-one profinite inverse limit factors exactly through one proper stage above any prescribed base.",
        H("Continuous real tests reflect below omega-one"),
        Blocks(
            Paragraph(Text(
                "CountableStage is the subtype of ordinals strictly below omega-one. F is an actual functor from its opposite preorder category to Profinite at universe one. "
                + "Every stage is nonempty and every actual bonding map is surjective. C is an actual cone with an IsLimit witness. "
                + "For each prescribed base and each continuous real-valued f on C.pt, the theorem constructs a proper beta at least base and a continuous real-valued g on F(op beta), with exact equality at every point. "
                + "In the display Fobj, Fmap, Cpt and Cprojection denote the actual functor objects, bonding maps, cone point and projection evaluation. ContinuousMap denotes bundled continuous maps, Real is the usual topological real field, and Le is the ordinal stage order.")),
            Describe.Lean(
                DescribeId.Create("continuous-stage-reflection"),
                DeclarationHandle.Create(Owner + "exists_stage"),
                H("Exact continuous factorization at a proper stage"),
                StatementSource.FromAuthor(Statement()),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Topology/kania2026talagrand")),
                Blocks(
                    Paragraph(Text(
                        "The range of LocallyConstant.toContinuousMapAlgHom over the reals separates points of the profinite cone point. "
                        + "Mathlib's real Stone-Weierstrass theorem supplies locally constant l(n) whose pointwise errors are strictly below 1/(n+1). "
                        + "Profinite.exists_locallyConstant reflects each l(n) through an actual component j(n). "
                        + "The supremum over Option(Nat), assigning base to none and j(n) to some(n), remains below omega-one by Ordinal.iSup_lt_omega_one and lies above every chosen stage.")),
                    Paragraph(Text(
                        "Cone naturality makes each l(n) equal at any two points with equal beta projections. "
                        + "For arbitrary positive epsilon choose n with 1/(n+1) below epsilon/2. The triangle inequality bounds the distance between the original two f values by epsilon. "
                        + "Thus f is constant on every actual beta fiber. Function.factorsThrough_iff produces a total real-valued factor. "
                        + "CountableClopenReflection.projection_surjective supplies actual surjectivity of this projection; it reuses the existing compatible-thread lifting proof. "
                        + "A continuous surjection from compact C.pt to the Hausdorff stage is a quotient map, and its continuous_iff criterion proves continuity of the factor.")),
                    Paragraph(Text(
                        "This is ordinary compact inverse-limit mathematics, assembled from the cited project and pinned Mathlib APIs; no mathematical novelty is claimed. The supplemental four-slot source-selection audit remains unfinished under https://github.com/the-omega-institute/trureturing/issues/21901; no validated registration is claimed. "
                        + "In the CH signed Talagrand construction, an actual final Prefix diagram and its limit cone may instantiate F and C. For each fixed continuous real test, this supplier gives an actual proper stage above the required launch base. "
                        + "Applying any stage-level integral or convergence theorem still requires its own signed-measure hypotheses and projection identities. "
                        + "The chosen stage depends on f. This theorem does not assert one proper stage for all continuous functions, nor does it construct the CH recursion, prove all signed clauses (A)-(G), or settle Kania and Kakol's arXiv:2607.06808v2 Problem 8.2."))),
                DescribeRole.Theorem))));
}
