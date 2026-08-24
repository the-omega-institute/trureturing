using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.Dynamics;

internal sealed class LinearProjectionDescentCriterionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Orthogonal-projection descent is exactly vanishing directed flow, and self-adjoint dynamics make it commutation.",
        H("Linear Projection Descent Criterion"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("linear-projection-descent-criterion"),
                DeclarationHandle.Create(
                    "D5/S3/Observer/Dynamics/LinearProjectionDescentCriterion."
                        + "linear_projection_descent_criterion"),
                H("Projection descent, directed flow, and commutation"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The carrier is the finite complex Hilbert space of coordinate vectors. "
                            + "Idempotence and Hermiticity make P an orthogonal projection, and "
                            + "the complementary hidden projection is constructed as I minus P.")),
                    Paragraph(Text(
                        "The public seven-condition equivalence includes effective-image descent, "
                            + "interface congruence, absence of carry, factorization, pullback "
                            + "invariance, one-step kernel stability, and the directed cross-block "
                            + "equation.")),
                    Paragraph(Text(
                        "For self-adjoint T, taking the conjugate transpose of the visible cross "
                            + "block supplies the reverse cross block. The imported commutator "
                            + "identity then makes directed vanishing equivalent to commutation.")),
                    Paragraph(Text(
                        "The existing sixfold interface theorem and commutator identity are applied "
                            + "directly. Repository and pinned-library searches found no theorem "
                            + "packaging the added matrix clause on this carrier."))),
                DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula n = F.Id("n");
        Formula p = F.Id("P");
        Formula t = F.Id("T");
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula matrix = Call("Matrix", n, n, complex);
        Formula q = Call("toLin", p);
        Formula flow = Call("toLin", t);
        Formula cross = Seq(
            p, Sp, Cdot, Sp, t, Sp, Cdot, Sp, Open, D(1), Minus, p, Close,
            Sp, Eq, Sp, D(0));
        Formula commutator = Seq(
            p, Sp, Cdot, Sp, t, Minus, t, Sp, Cdot, Sp, p,
            Sp, Eq, Sp, D(0));
        Formula sixAndBlock = Call(
            "TFAE",
            Call("EffectiveDescent", q, flow),
            Call("InterfaceCongruence", q, flow),
            Call("NoCarry", q, flow),
            Call("FactorsThrough", Call("compose", q, flow), q),
            Call("PullbackInvariant", q, flow),
            Seq(Call("depthZeroKernel", q), Sp, Eq, Sp, Call("depthOneKernel", q, flow)),
            cross);

        return Disp(Seq(
            Begin, Grp(F.Id("gathered")),
            Forall, Sp, n, Comma, Sp, p, Comma, Sp, t, Colon, Sp, matrix, Comma,
            RowBreak, Grp(),
            Open, Call("IsIdempotentElem", p), Sp, Land, Sp, Call("IsHermitian", p), Close,
            Sp, Rightarrow, Sp,
            Open, sixAndBlock, Sp, Land, RowBreak, Grp(),
            Open, Call("IsHermitian", t), Sp, Rightarrow, Sp,
            Open, cross, Sp, Leftrightarrow, Sp, commutator, Close, Close, Close, Dot,
            End, Grp(F.Id("gathered"))));
    }
}
