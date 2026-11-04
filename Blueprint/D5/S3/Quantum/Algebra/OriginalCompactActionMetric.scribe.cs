using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Algebra;

internal sealed class OriginalCompactActionMetricDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original compact matrix action supplies an invariant positive form on the same prediction space.",
        H("An Invariant Metric on the Original Compact Action"),
        Blocks(Describe.Lean(
            DescribeId.Create("compact-action-metric"),
            DeclarationHandle.Create("D5/S3/Quantum/Algebra/OriginalCompactActionMetric.compact_action_metric"),
            H("Compactness supplies the metric and skew curve velocities"),
            StatementSource.FromAuthor(MetricFormula()), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Let W be any finite-dimensional real inner product space, including the zero space. Its initially chosen inner product is auxiliary and need not be invariant. Let G be any subgroup of the units of the continuous real endomorphism algebra of that same W, with compact underlying set in the inherited operator topology. Thus the action is the original faithful matrix action; no new representation or smaller invariant subspace is substituted. Compactness is the only additional hypothesis of the theorem.")),
                Paragraph(Text("There exists a positive definite symmetric real bilinear form B on W, encoded by InnerProductSpace.Core, invariant under every member of G. For every actual curve c from the real line to G with c(0)=1, and every ambient operator K which is the derivative at zero of the original operator-valued curve, B(Ku,v)=-B(u,Kv) for every u,v in the full W. The curve is not assumed to be a chosen exponential or an abstract Lie-algebra witness.")),
                Paragraph(Text("The proof integrates the operators g-inverse-adjoint composed with g-inverse against left Haar measure on the actual compact subgroup. The resulting Gram operator S represents B(u,v)=inner(u,Sv). Continuous integrands on the compact group are integrable; the diagonal is nonnegative and its value at the identity is strictly positive for a nonzero vector, so Haar positivity makes B definite. Left translation proves invariance. Differentiating that identity along the actual G-valued curve gives skewness.")),
                Paragraph(Text("The Gram construction is an adapted port of TauCeti's compact representation unitarization at immutable revision 57ab0f657d7fb33d7c9425bf696bec3045b0fd75, file TauCeti/RepresentationTheory/Compact/Unitarizable.lean. The original copyright and full Apache 2.0 license are retained in Lean. The inverse action avoids importing its Haar-probability infrastructure. This is an application and a source bridge, with no originality claim for Haar unitarization.")),
                Paragraph(Text("This is the metric dependency in OMEGAQ-008 Theorem 5.1. It does not assert that the original complete quotient relation holds, supply that theorem's dimension conclusion, identify a group component, classify G as SO or O, or prove the complete original rigidity equivalence. The finite-dimensional hypothesis provides the complete operator space used for integration; no parity, nonzero vector, rank, centralizer, transitivity or irreducibility assumption is added."))),
            DescribeRole.Theorem))));

    private static Formula MetricFormula()
    {
        Formula w = F.Id("W"), g = F.Id("G"), b = F.Id("B"), k = F.Id("K");
        Formula u = F.Id("u"), v = F.Id("v"), c = F.Id("c");
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula pair(Formula x, Formula y) => Call("B", x, y);
        return Disp(Seq(
            Forall, Sp, w, Comma, g, Comma, Esc,
            Call("FiniteDimensionalRealInnerProductSpace", w), Sp, Land, Sp,
            Call("SubgroupOfUnitsEnd", g, w), Sp, Land, Sp, Call("IsCompact", g),
            Sp, Rightarrow, Sp, Exists, Sp, b, Colon, Call("InnerProductSpaceCore", real, w), Comma, Esc,
            Open, Forall, Sp, F.Id("h"), Colon, g, Comma, Esc,
                Forall, Sp, u, Comma, v, Colon, w, Comma, Esc,
                pair(Call("h",u), Call("h",v)), Eq, pair(u,v), Close, Sp, Land, Sp,
            Forall, Sp, c, Colon, real, Sp, To, Sp, g, Comma, Esc,
                Call("c",D(0)), Eq, D(1), Sp, Rightarrow, Sp,
            Forall, Sp, k, Colon, Call("End",real,w), Comma, Esc,
                Call("HasDerivAt",Call("originalOperatorCurve",c),k,D(0)),
                Sp, Rightarrow, Sp, Forall, Sp, u, Comma, v, Colon, w, Comma, Esc,
                pair(Call("K",u),v), Eq, Minus, pair(u,Call("K",v))));
    }
}
