using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.InverseLimit;

internal sealed class SignedProperLimitDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Topology/InverseLimit/SignedProperLimit.";
    private static Formula V(string name) => F.Id(name);
    private static Formula All(string name, Formula type) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp);
    private static Formula Arrow(Formula a, Formula b) => Seq(a, Sp, Rightarrow, Sp, b);
    private static Formula Base => Seq(All("l", V("Ordinal0")), All("H", Call("Prefix", V("l"))));
    private static Formula MainStatement() => Disp(Seq(Base,
        Arrow(Call("IsSuccLimit", V("l")),
        Arrow(Call("Lt", V("l"), V("omegaOne")),
        Arrow(Call("Lt", V("omega"), V("l")),
            Seq(All("D", Call("Data", V("H"))),
                Arrow(Call("Laws", V("H"), V("D")),
                    Call("Nonempty", Call("Extension", V("H"), V("D"))))))))));
    private static Formula OntoStatement() => Disp(Seq(Base,
        Arrow(Call("IsSuccLimit", V("l")),
            Seq(All("a", Call("Coord", V("l"))),
                Call("Surjective", Call("projection", V("H"), V("a")))))));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Joint preservation at the literal proper countable coordinate limit, with fixed parity reservoirs and full signed every-choice convergence.",
        H("Signed proper countable limit extension"),
        Blocks(
            Paragraph(Text(
                "Coord(a) is the set of ordinals below a and Cube(a) is Coord(a) to Bool. "
                + "Prefix(l) contains a closed nonempty subset of Cube(a) for every a<l, literal restriction compatibility, "
                + "and surjectivity of all old restrictions. It includes finite initial stages. "
                + "LimitSpace(H) is the literal subset of Cube(l) whose restriction belongs to every old carrier. "
                + "The new projection is coordinate restriction. coneIsLimit constructs the universal map: "
                + "coordinate xi is read at succ(xi)<l, with cone naturality proving all old-stage equations. "
                + "Compactness follows from closedness in the cube. properMetric selects a compatible metric only under l<omegaOne.")),
            Describe.Lean(
                DescribeId.Create("proper-limit-projections-onto"),
                DeclarationHandle.Create(Owner + "projection_surjective"),
                H("Onto literal limit restrictions"),
                StatementSource.FromAuthor(OntoStatement()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "This consumed topology adapter uses compact_projection_image on the actual old diagram. "
                    + "Old onto maps put every old point in the eventual range. The explicitly proved coneIsLimit "
                    + "transports the compatible thread to the literal coordinate subset. Countability is not needed for this statement."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("joint-signed-proper-limit-extension"),
                DeclarationHandle.Create(Owner + "exists_joint_proper_limit_extension"),
                H("Complete proper-stage preservation"),
                StatementSource.FromAuthor(MainStatement()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "RegularSigned(K) consists of actual finite signed Borel measures with both Jordan parts regular. "
                        + "Data retains the proper-stage bound, I(r,a), J(r,d,a), fixed N(r,d,e), clopen birth supports V(r,n), and the full signed birth enumeration nu(r,d,n) for every d<omegaOne, including future labels. Mass one is required only at born rows omega<=r. "
                        + "Only omega<=r<a<l is an I domain; J additionally requires d<a. Off-domain total-function values carry no obligations. "
                        + "The assumptions use no positivity or support restriction beyond what is needed here, so every original supported signed class is included. "
                        + "Laws contains A: J subset I; B: the two fixed N pieces are disjoint; C: each J intersect N piece is infinite; "
                        + "DI and DJ: later sets are contained modulo finite sets in every earlier defined set. "
                        + "E quantifies over every coordinate r<=xi<a and every pair in the entire pulled-back support with the same row projection. "
                        + "F quantifies over every global all-Nat regular signed selection of mass one and exact row pushforward. "
                        + "Its conclusion is an actual regular signed represented weak-star limit of mass at most one along atTop intersect principal(J).")),
                    Paragraph(Text(
                        "Extension supplies new I and J for every omega<=r<l and every d<l, reusing Data.N literally. "
                        + "It contains the proved IsLimit of the actual coordinate cone, onto projections, A through D against every earlier defined domain, "
                        + "whole-support E for every r<=xi<l, nonempty actual norm-preserving lift classes, and represented signed every-choice F in the same filter form. "
                        + "No new-stage E, F, unexplained IsLimit, desired represented limit, or final omegaOne bookkeeping is a premise.")),
                    Paragraph(Text(
                        "For each row, a monotone cofinal countable sequence above it and a countable label coding instantiate the existing "
                        + "CountableJointFusion theorem with finite active labels and eventual activity. Its cofinite inclusions extend to every old stage by cofinality and old DI/DJ. "
                        + "E transports through one stage above the requested coordinate. NormPreservingLiftExistence gives actual class nonvacuity.")),
                    Paragraph(Text(
                        "For an arbitrary global new selection and one fixed clopen, Profinite.exists_isClopen_of_cofiltered gives exact descent. "
                        + "Enlarge its stage above row and label. Project the selection for every natural index; the two variation contractions, "
                        + "with mass one at both ends, prove the intermediate projection has mass one. Compact metric regularity supplies both Jordan parts. "
                        + "Apply old F directly to this global projection, then restrict along the new J. The exact clopen preimage identity "
                        + "gives Cauchy evaluations along the increasing enumeration of the infinite new J. "
                        + "ClopenCauchyConvergence supplies an actual represented regular signed weak-star limit, and enumeration transports it to the original filter. "
                        + "Each clopen chooses its own stage; no uniform eventual assertion over all observables is inferred.")),
                    Paragraph(Text(
                        "This is a local limit-extension unit of the full signed construction. It does not supply successor splitting, "
                        + "CH enumeration, the transfinite recursion, anti-homeomorphism or analytic endpoints, or a solution of Problem 8.2."))),
                DescribeRole.Theorem))));
}
