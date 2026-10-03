using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Mordell;

internal sealed class EllipticTraceNormDivisibilityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Smoothness prevents a common trace and norm denominator from hiding a pole "
            + "in either polynomial coordinate.",
        H("Trace and Norm Denominators on a Weierstrass Curve"),
        Blocks(Describe.Lean(
            DescribeId.Create("elliptic-trace-norm-denominator-divisibility"),
            DeclarationHandle.Create(
                "D5/S3/Factorization/Mordell/EllipticTraceNormDivisibility."
                    + "elliptic_trace_norm_denominator_divides_coordinates"),
            H("A smooth coordinate ring has no hidden polynomial denominator"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "Let F be any field, and let W be a smooth Weierstrass curve over F. "
                        + "Set A(X) = a1 X + a3 and "
                        + "B(X) = X cubed + a2 X squared + a4 X + a6. "
                        + "Its quadratic coordinate relation is Y squared + A(X) Y - B(X) = 0. "
                        + "For p and q in F[X], the trace numerator of p + qY is 2p - qA "
                        + "and the norm numerator is p squared - pqA - q squared B.")),
                Paragraph(Text(
                    "For every nonzero polynomial d, if d divides the trace numerator "
                        + "and d squared divides the norm numerator, then d divides both "
                        + "p and q. The theorem includes fields of characteristic two and three.")),
                Paragraph(Text(
                    "At a prime polynomial where q is invertible, the trace and norm "
                        + "relations would construct a point with both partial derivatives zero "
                        + "over the residue field. Smoothness rules out this singular point. "
                        + "Thus the prime divides both coordinates; cancelling it and applying "
                        + "factorization induction accounts for every denominator multiplicity.")),
                Paragraph(Text(
                    "This criterion is a step in coordinate integrality. It alone gives "
                        + "no global isogeny point map, point independence, or canonical height."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula field = F.Id("F");
        Formula curve = F.Id("W");
        Formula d = F.Id("d");
        Formula p = F.Id("p");
        Formula q = F.Id("q");
        Formula divides = F.Id("divides");
        return Disp(Seq(
            Forall, Sp, field, Comma, Sp, Call("Field", field), Sp, Rightarrow, Sp,
            Forall, Sp, curve, Sp, InMacro, Sp, Call("Weierstrass", field), Comma, Sp,
            Call("Smooth", curve), Sp, Rightarrow, Sp,
            Forall, Sp, d, Comma, Sp, p, Comma, Sp, q, Sp, InMacro, Sp,
            Call("Polynomial", field), Comma, Sp,
            Open, d, Sp, Neq, Sp, D(0), Sp, Land, Sp,
            d, Sp, divides, Sp, Call("traceNumerator", curve, p, q), Sp, Land, Sp,
            new Formula.Power(d, D(2)), Sp, divides, Sp,
            Call("normNumerator", curve, p, q), Close, Sp, Rightarrow, Sp,
            Open, d, Sp, divides, Sp, p, Sp, Land, Sp, d, Sp, divides, Sp, q, Close));
    }
}
