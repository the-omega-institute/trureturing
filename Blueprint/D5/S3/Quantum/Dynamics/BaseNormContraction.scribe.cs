using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Dynamics;

internal sealed class BaseNormContractionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create()
    {
        Formula vectorSpace = F.Id("V");
        Formula cone = F.Id("C");
        Formula functional = F.Id("u");
        Formula dynamics = F.Id("T");
        Formula time = F.Id("t");
        Formula otherTime = F.Id("s");
        Formula vector = F.Id("x");
        Formula timedDynamics = Seq(
            dynamics, Underscore, Grp(time));
        Formula otherDynamics = Seq(
            dynamics, Underscore, Grp(otherTime));
        Formula mappedVector = Seq(timedDynamics, Open, vector, Close);
        Formula mappedCone = Seq(otherDynamics, Open, cone, Close);
        Formula composedFunctional = Seq(
            functional, Sp, Circ, Sp, otherDynamics);
        Formula statement = Disp(Seq(
            Forall, Sp, vectorSpace, Comma, Sp, cone, Comma, Sp,
            functional, Comma, Sp, dynamics, Comma, Sp,
            time, Comma, Sp, vector, Comma, RowBreak, Grp(),
            Call("ConvexCone", cone, vectorSpace), Sp, Land, Sp,
            Call("Generates", cone, vectorSpace), Sp, Land, Sp,
            Call("StrictlyPositive", functional, cone), Sp, Land,
            RowBreak, Grp(),
            Open, Forall, Sp, otherTime, Comma, Sp,
            mappedCone, Sp, Subseteq, Sp, cone, Sp, Land, Sp,
            composedFunctional, Sp, Eq, Sp, functional, Close,
            Sp, Rightarrow, Sp, RowBreak, Grp(),
            Call("baseNorm", cone, functional, mappedVector), Sp, Leq, Sp,
            Call("baseNorm", cone, functional, vector), Dot));

        return DocumentDefinition.Create(ScribeNode.Create(
            "Positive normalization-preserving dynamics contract the cone base norm.",
            H("Base Norm Contraction"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("functional-nonneg-on-cone"),
                    DeclarationHandle.Create(
                        "D5/S3/Quantum/Dynamics/BaseNormContraction.functional_nonneg_on_cone"),
                    H("Strict positivity implies nonnegativity on the whole cone"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Forall, Sp, vectorSpace, Comma, Sp, cone, Comma, Sp,
                        functional, Comma, Sp, vector, Comma, RowBreak, Grp(),
                        Call("AddCommGroup", vectorSpace), Sp, Land, Sp,
                        Call("Module", Call("Real"), vectorSpace), Sp, Land, Sp,
                        Call("ConvexCone", cone, vectorSpace), Sp, Land, Sp,
                        Call("RealLinearFunctional", functional, vectorSpace), Sp, Land, Sp,
                        Call("StrictlyPositive", functional, cone), Sp, Land, Sp,
                        vector, Sp, InMacro, Sp, cone, Sp, Rightarrow, Sp,
                        D(0), Sp, Leq, Sp, Call("Eval", functional, vector), Dot))),
                    AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text(
                        "For any additive commutative group V with a real module structure, "
                            + "any real convex cone C and any real-linear functional u strictly "
                            + "positive on every nonzero element of C, u is nonnegative at every "
                            + "element of C, including zero. No norm, dimension, closedness or "
                            + "generating hypothesis is used. This is the original consumed lemma: "
                            + "cone_decomposition_costs_bddBelow uses it in the base-norm proof, "
                            + "and OriginalMassCalibration.original_mass_factorization applies "
                            + "it to both actual mass tensors. Public visibility adds no "
                            + "mathematical content."))),
                    DescribeRole.Theorem),
                Describe.Lean(
                    DescribeId.Create(
                        "positive-normalization-preserving-dynamics-contract-base-norm"),
                    DeclarationHandle.Create(
                        "D5/S3/Quantum/Dynamics/BaseNormContraction."
                            + "positive_normalization_preserving_dynamics_contracts_base_norm"),
                    H("Positive normalized dynamics are base-norm contractions"),
                    StatementSource.FromAuthor(statement),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "Let V be a real vector space and C a convex cone that generates V "
                                + "by differences. A real-linear functional u is strictly "
                                + "positive on every nonzero cone element.")),
                        Paragraph(Text(
                            "The base norm is constructed as the infimum of u(a)+u(b) over all "
                                + "cone decompositions x=a-b. Thus the norm object is built from "
                                + "the source cone and functional rather than assumed as an "
                                + "unrelated ambient norm.")),
                        Paragraph(Text(
                            "For every time, the real-linear dynamics maps C into C and preserves "
                                + "u. Applying it to any decomposition of x produces a cone "
                                + "decomposition of the evolved vector with exactly the same "
                                + "cost.")),
                        Paragraph(Text(
                            "The decomposition-cost set for x is therefore contained in the one "
                                + "for its image. Reversed monotonicity of infima gives the stated "
                                + "contraction."))),
                    DescribeRole.Theorem))));
    }
}
