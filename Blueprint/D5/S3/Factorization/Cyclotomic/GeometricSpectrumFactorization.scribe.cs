using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Cyclotomic;

internal sealed class GeometricSpectrumFactorizationDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite geometric sum factors into the cyclotomic polynomials indexed by its "
        + "nontrivial divisors.",
        H("Cyclotomic Factorization of a Geometric Sum"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("geometric-sum-equals-cyclotomic-product"),
                DeclarationHandle.Create(
                    "D5/S3/Factorization/Cyclotomic/GeometricSpectrumFactorization."
                    + "geometric_sum_eq_cyclotomic_product"),
                H("The geometric sum is the product of its nontrivial cyclotomic factors"),
                StatementSource.FromAuthor(Disp(Seq(
                    Forall, Sp, F.Id("R"), Comma, Sp,
                    OpenBracket, Operatorname, Grp(F.Id("CommRing")),
                    Open, F.Id("R"), Close, CloseBracket, Comma, Esc,
                    Forall, Sp, F.Id("n"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("N")), Comma,
                    Sp, F.Id("n"), Gt, D(0), Sp, Rightarrow, Sp,
                    Sum, Underscore, Grp(F.Id("i"), Eq, D(0)), Caret,
                    Grp(F.Id("n"), Minus, D(1)), Sp,
                    F.Id("X"), Caret, F.Id("i"), Sp, Eq, Sp,
                    Prod, Underscore,
                    Grp(F.Id("d"), Sp, Mid, Sp, F.Id("n"), Comma, Sp,
                        F.Id("d"), Gt, D(1)), Sp,
                    Phi, Underscore, F.Id("d"), Open, F.Id("X"), Close))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For every commutative ring R and positive natural number n, the polynomial "
                        + "with one monomial in each degree from zero through n minus one equals the "
                        + "product of the d-th cyclotomic polynomials over all divisors d of n other "
                        + "than one.")),
                    Paragraph(Text(
                        "Pinned Mathlib was searched before proof construction and contains this exact "
                        + "identity as Polynomial.prod_cyclotomic_eq_geom_sum. The Lean declaration "
                        + "only reverses that equality to match the source orientation; it does not "
                        + "reconstruct the cyclotomic factorization.")),
                    Paragraph(Text(
                        "This closes only the opening factorization identity in remark 27.589, clause "
                        + "2. The coefficient-sign classification, the claimed uniqueness criterion "
                        + "for prime powers, the alternative composite decompositions, and the finite "
                        + "numerical census remain outside this declaration."))),
                DescribeRole.Theorem
            ))));
}
