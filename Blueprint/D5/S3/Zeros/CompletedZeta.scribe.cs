using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Zeros;

internal sealed class CompletedZetaDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef IdentityTheorem =
        LibraryNoteRef.Create("D5/L/Zeros/jaiswar2021identity");
    private static readonly LibraryNoteRef CoffeyXi =
        LibraryNoteRef.Create("D5/L/Zeros/coffey2007theta");

    private static LeanDeclarationRef LeanDefinition(string value) =>
        LeanDeclarationRef.Create(
            value,
            expectedKind: LeanDeclarationKind.Definition,
            requireNoSorry: true);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeDocument.Create(
        Header(
            "D5/S3/Zeros/CompletedZeta",
            "Continuation uniqueness, an entire xi reading, and conditional zero symmetry support the O-6 route."),
        H("Completed Zeta and the Zero-Symmetry Foundation"),
        Blocks(
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("analytic-continuations-of-one-local-germ-are-unique"),
                H("Analytic continuations of one local germ are unique"),
                LeanTheorem(
                    "D5/S3/Zeros/CompletedZeta.analytic_continuation_unique"),
                LatexStatement.Create(@"$$\forall U\subseteq\mathbb{C},\ \forall f,g:\mathbb{C}\to\mathbb{C},\ \forall s_{0}\in U,\ \operatorname{AnalyticOnNhd}_{\mathbb{C}}(f,U) \land \operatorname{AnalyticOnNhd}_{\mathbb{C}}(g,U) \land \operatorname{IsPreconnected}(U) \land \operatorname{EventuallyEq}_{\operatorname{nhds}(s_{0})}(f,g) \Rightarrow \operatorname{EqOn}(f,g,U)$$"),
                DescribeProvenance.LiteratureAttested(IdentityTheorem),
                Blocks(Paragraph(Text(
                    "Two functions analytic on neighborhoods of a supplied preconnected set agree throughout that set when they agree eventually in the ambient neighborhood of one supplied point. The set and both functions are explicit inputs; the theorem constructs no continuation and proves no domain is nonempty beyond the supplied member. Compared with the ingested source atom, mathlib's identity principle replaces the explicit first-coefficient estimate, geometric-tail bound, path construction, and finite disc cover. On the O-6 path this supplies uniqueness for identifying a continued coordinate reading with the classical completed reading, but not the missing existence or identification bridge.")))
            ),
            DocumentBlock.Describe.Definition(
                DescribeId.Create("the-completed-reading-is-mathlibs-classical-completed-zeta"),
                H("The completed reading is mathlib's classical completed zeta"),
                LeanDefinition(
                    "D5/S3/Zeros/CompletedZeta.completedZetaReading"),
                DescribeProvenance.LiteratureAttested(CoffeyXi),
                Blocks(Paragraph(Text(
                    "The definition is an alias for mathlib's completed Riemann zeta. It does not define the ingested subscript-K reading directly from the coordinate heat trace, and it carries no theorem equating that heat trace with the continued function. This fixes the analytic object whose functional equation can feed the zero symmetries required below O-6 while leaving the coordinate-to-completion edge explicit.")))
            ),
            DocumentBlock.Describe.Definition(
                DescribeId.Create("the-xi-reading-totalizes-the-pole-removed-completion"),
                H("The xi reading totalizes the pole-removed completion"),
                LeanDefinition(
                    "D5/S3/Zeros/CompletedZeta.xiReading"),
                DescribeProvenance.LiteratureAttested(CoffeyXi),
                Blocks(Paragraph(Text(
                    "The entire reading is defined through mathlib's pole-removed completed zeta, including the correction that totalizes the two exceptional endpoints. It is not introduced by multiplying the meromorphic completed reading at those endpoints. This representation makes the object globally differentiable without silently assuming cancellation of poles, an analytic foundation needed before zero reflection can support O-6.")))
            ),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("away-from-the-endpoints-xi-has-the-classical-product-form"),
                H("Away from the endpoints xi has the classical product form"),
                LeanTheorem(
                    "D5/S3/Zeros/CompletedZeta.xi_reading_eq_completed_zeta"),
                LatexStatement.Create(@"$\forall s\in\mathbb{C},\ s\neq 0 \land s\neq 1 \Rightarrow \operatorname{xiReading}(s)=\frac{1}{2}s(s-1)\operatorname{completedZetaReading}(s)$"),
                DescribeProvenance.LiteratureAttested(CoffeyXi),
                Blocks(Paragraph(Text(
                    "When s is neither zero nor one, the totalized xi reading equals one half times s times s minus one times the completed-zeta reading. The two exclusions are explicit and are absent from the ingested definition's displayed global notation; endpoint values are governed by the pole-removed definition instead. The theorem does not identify completed zeta with the coordinate heat trace outside its convergence half-plane.")))
            ),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("the-xi-reading-is-entire"),
                H("The xi reading is entire"),
                LeanTheorem(
                    "D5/S3/Zeros/CompletedZeta.xi_reading_differentiable"),
                LatexStatement.Create(@"$\operatorname{Differentiable}_{\mathbb{C}}(\operatorname{xiReading})$"),
                DescribeProvenance.LiteratureAttested(CoffeyXi),
                Blocks(Paragraph(Text(
                    "The totalized xi reading is complex differentiable at every complex input. The proof uses mathlib's differentiability theorem for the pole-removed completed zeta; it does not formalize the ingested atom's Jacobi-theta, Poisson-summation, or Mellin-transform derivation. Entirety legitimizes the global zero reading used on the O-6 dependency path but supplies no positivity.")))
            ),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("the-xi-reading-is-reflection-invariant"),
                H("The xi reading is reflection invariant"),
                LeanTheorem(
                    "D5/S3/Zeros/CompletedZeta.xi_reading_reflection"),
                LatexStatement.Create(@"$\forall s\in\mathbb{C},\ \operatorname{xiReading}(1-s)=\operatorname{xiReading}(s)$"),
                DescribeProvenance.LiteratureAttested(CoffeyXi),
                Blocks(Paragraph(Text(
                    "For every complex s, evaluating xi at one minus s gives the same value as evaluating it at s. This is the ingested functional equation with its equality orientation reversed only syntactically. The proof delegates the analytic derivation to mathlib's completed-zeta reflection theorem; it neither rebuilds theta analysis nor states that all zeros lie on the fixed line. Reflection supplies one of the zero-orbit symmetries needed to connect completed zeta to O-6.")))
            ),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("supplied-symmetries-generate-a-zero-orbit-and-reverse-scaling"),
                H("Supplied symmetries generate a zero orbit and reverse scaling"),
                LeanTheorem(
                    "D5/S3/Zeros/CompletedZeta.zero_quartet_scaling_spec"),
                LatexStatement.Create(@"$$\forall H:\mathbb{C}\to\mathbb{C},\ (\forall s,\ H(\overline{s})=\overline{H(s)}) \land (\forall s,\ H(1-s)=H(s)) \Rightarrow \forall A\ [\operatorname{AddMonoid}(A)],\ \forall \ell:A\to_{+}\mathbb{R},\ \forall \rho\in\mathbb{C},\ H(\rho)=0 \Rightarrow H(\rho)=0 \land H(\overline{\rho})=0 \land H(1-\rho)=0 \land H(1-\overline{\rho})=0 \land (\forall a,\ \operatorname{scalingLedger}(\ell,1-\overline{\rho},a)=-\operatorname{scalingLedger}(\ell,\rho,a))$$"),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "For an arbitrary reading H, conjugation covariance and reflection invariance are explicit premises. From a supplied zero, Lean derives zeros at its conjugate, reflection, and conjugate reflection, then proves pointwise reversal for a supplied additive scaling ledger. The additive carrier is inhabited by its zero and the ledger length is supplied; no ZeroData value, zero enumeration, or ZeroData inhabitance is assumed or produced. Compared with the ingested theorem, real coefficients and analytic continuation are replaced by the two exact symmetry premises, while pairwise distinctness, the claim that symmetry cannot exclude off-line zeros, and the nonmultiplicative numerical instrument are omitted. This theorem gives O-6 the symmetry-controlled zero orbit whose cross-position cancellation must be distinguished from local positivity.")))
            ))));
}
