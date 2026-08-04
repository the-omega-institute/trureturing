using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

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
                Disp(Seq(Forall, Sp, F.Id("U"), Subseteq, Mathbb, Grp(F.Id("C")), Comma, Esc, Forall, Sp, F.Id("f"), Comma, F.Id("g"), Colon, Mathbb, Grp(F.Id("C")), To, Mathbb, Grp(F.Id("C")), Comma, Esc, Forall, Sp, F.Id("s"), Underscore, Grp(D(0)), InMacro, Sp, F.Id("U"), Comma, Esc, Operatorname, Grp(F.Id("AnalyticOnNhd")), Underscore, Grp(Mathbb, Grp(F.Id("C"))), Open, F.Id("f"), Comma, F.Id("U"), Close, Sp, Land, Sp, Operatorname, Grp(F.Id("AnalyticOnNhd")), Underscore, Grp(Mathbb, Grp(F.Id("C"))), Open, F.Id("g"), Comma, F.Id("U"), Close, Sp, Land, Sp, Operatorname, Grp(F.Id("IsPreconnected")), Open, F.Id("U"), Close, Sp, Land, Sp, Operatorname, Grp(F.Id("EventuallyEq")), Underscore, Grp(Operatorname, Grp(F.Id("nhds")), Open, F.Id("s"), Underscore, Grp(D(0)), Close), Open, F.Id("f"), Comma, F.Id("g"), Close, Sp, Rightarrow, Sp, Operatorname, Grp(F.Id("EqOn")), Open, F.Id("f"), Comma, F.Id("g"), Comma, F.Id("U"), Close)),
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
                In(Seq(Forall, Sp, F.Id("s"), InMacro, Mathbb, Grp(F.Id("C")), Comma, Esc, F.Id("s"), Neq, Sp, D(0), Sp, Land, Sp, F.Id("s"), Neq, Sp, D(1), Sp, Rightarrow, Sp, Operatorname, Grp(F.Id("xiReading")), Open, F.Id("s"), Close, Eq, Frac, Grp(D(1)), Grp(D(2)), F.Id("s"), Open, F.Id("s"), Minus, D(1), Close, Operatorname, Grp(F.Id("completedZetaReading")), Open, F.Id("s"), Close)),
                DescribeProvenance.LiteratureAttested(CoffeyXi),
                Blocks(Paragraph(Text(
                    "When s is neither zero nor one, the totalized xi reading equals one half times s times s minus one times the completed-zeta reading. The two exclusions are explicit and are absent from the ingested definition's displayed global notation; endpoint values are governed by the pole-removed definition instead. The theorem does not identify completed zeta with the coordinate heat trace outside its convergence half-plane.")))
            ),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("the-xi-reading-is-entire"),
                H("The xi reading is entire"),
                LeanTheorem(
                    "D5/S3/Zeros/CompletedZeta.xi_reading_differentiable"),
                In(Seq(Operatorname, Grp(F.Id("Differentiable")), Underscore, Grp(Mathbb, Grp(F.Id("C"))), Open, Operatorname, Grp(F.Id("xiReading")), Close)),
                DescribeProvenance.LiteratureAttested(CoffeyXi),
                Blocks(Paragraph(Text(
                    "The totalized xi reading is complex differentiable at every complex input. The proof uses mathlib's differentiability theorem for the pole-removed completed zeta; it does not formalize the ingested atom's Jacobi-theta, Poisson-summation, or Mellin-transform derivation. Entirety legitimizes the global zero reading used on the O-6 dependency path but supplies no positivity.")))
            ),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("the-xi-reading-is-reflection-invariant"),
                H("The xi reading is reflection invariant"),
                LeanTheorem(
                    "D5/S3/Zeros/CompletedZeta.xi_reading_reflection"),
                In(Seq(Forall, Sp, F.Id("s"), InMacro, Mathbb, Grp(F.Id("C")), Comma, Esc, Operatorname, Grp(F.Id("xiReading")), Open, D(1), Minus, F.Id("s"), Close, Eq, Operatorname, Grp(F.Id("xiReading")), Open, F.Id("s"), Close)),
                DescribeProvenance.LiteratureAttested(CoffeyXi),
                Blocks(Paragraph(Text(
                    "For every complex s, evaluating xi at one minus s gives the same value as evaluating it at s. This is the ingested functional equation with its equality orientation reversed only syntactically. The proof delegates the analytic derivation to mathlib's completed-zeta reflection theorem; it neither rebuilds theta analysis nor states that all zeros lie on the fixed line. Reflection supplies one of the zero-orbit symmetries needed to connect completed zeta to O-6.")))
            ),
            DocumentBlock.Describe.Theorem(
                DescribeId.Create("supplied-symmetries-generate-a-zero-orbit-and-reverse-scaling"),
                H("Supplied symmetries generate a zero orbit and reverse scaling"),
                LeanTheorem(
                    "D5/S3/Zeros/CompletedZeta.zero_quartet_scaling_spec"),
                Disp(Seq(Forall, Sp, F.Id("H"), Colon, Mathbb, Grp(F.Id("C")), To, Mathbb, Grp(F.Id("C")), Comma, Esc, Open, Forall, Sp, F.Id("s"), Comma, Esc, F.Id("H"), Open, Overline, Grp(F.Id("s")), Close, Eq, Overline, Grp(F.Id("H"), Open, F.Id("s"), Close), Close, Sp, Land, Sp, Open, Forall, Sp, F.Id("s"), Comma, Esc, F.Id("H"), Open, D(1), Minus, F.Id("s"), Close, Eq, F.Id("H"), Open, F.Id("s"), Close, Close, Sp, Rightarrow, Sp, Forall, Sp, F.Id("A"), Esc, OpenBracket, Operatorname, Grp(F.Id("AddMonoid")), Open, F.Id("A"), Close, CloseBracket, Comma, Esc, Forall, Sp, Ell, Colon, F.Id("A"), To, Underscore, Grp(Plus), Mathbb, Grp(F.Id("R")), Comma, Esc, Forall, Sp, Rho, InMacro, Mathbb, Grp(F.Id("C")), Comma, Esc, F.Id("H"), Open, Rho, Close, Eq, D(0), Sp, Rightarrow, Sp, F.Id("H"), Open, Rho, Close, Eq, D(0), Sp, Land, Sp, F.Id("H"), Open, Overline, Grp(Rho), Close, Eq, D(0), Sp, Land, Sp, F.Id("H"), Open, D(1), Minus, Rho, Close, Eq, D(0), Sp, Land, Sp, F.Id("H"), Open, D(1), Minus, Overline, Grp(Rho), Close, Eq, D(0), Sp, Land, Sp, Open, Forall, Sp, F.Id("a"), Comma, Esc, Operatorname, Grp(F.Id("scalingLedger")), Open, Ell, Comma, D(1), Minus, Overline, Grp(Rho), Comma, F.Id("a"), Close, Eq, Minus, Operatorname, Grp(F.Id("scalingLedger")), Open, Ell, Comma, Rho, Comma, F.Id("a"), Close, Close)),
                DescribeProvenance.RepoDerived(),
                Blocks(Paragraph(Text(
                    "For an arbitrary reading H, conjugation covariance and reflection invariance are explicit premises. From a supplied zero, Lean derives zeros at its conjugate, reflection, and conjugate reflection, then proves pointwise reversal for a supplied additive scaling ledger. The additive carrier is inhabited by its zero and the ledger length is supplied; no ZeroData value, zero enumeration, or ZeroData inhabitance is assumed or produced. Compared with the ingested theorem, real coefficients and analytic continuation are replaced by the two exact symmetry premises, while pairwise distinctness, the claim that symmetry cannot exclude off-line zeros, and the nonmultiplicative numerical instrument are omitted. This theorem gives O-6 the symmetry-controlled zero orbit whose cross-position cancellation must be distinguished from local positivity.")))
            ))));
}
