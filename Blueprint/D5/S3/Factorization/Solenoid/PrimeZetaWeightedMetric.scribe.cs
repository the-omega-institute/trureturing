using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Solenoid;

internal sealed class PrimeZetaWeightedMetricDocument
    : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The normalized prime-zeta weighted p-adic distance metrizes the hidden-address product.",
        H("Prime-Zeta Weighted Metric"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("prime-zeta-weighted-metric"),
                DeclarationHandle.Create(
                    "D5/S3/Factorization/Solenoid/PrimeZetaWeightedMetric."
                        + "prime_weighted_distance_is_metric_and_induces_product_topology"),
                H("Prime-zeta weighting induces the product topology"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The carrier is the literal product, over all bundled natural primes p, "
                            + "of the p-adic integer rings. No parallel hidden-address alias is "
                            + "introduced.")),
                    Paragraph(Text(
                        "For a real exponent s greater than one, primeWeightedDistance is the "
                            + "sum of the standard p-adic coordinate distances weighted by "
                            + "p to the power minus s and normalized by the corresponding "
                            + "prime-zeta sum.")),
                    Paragraph(Text(
                        "The displayed conclusion exposes reflexivity, symmetry, the triangle "
                            + "inequality, separation, and equality between product-open sets "
                            + "and sets locally containing a weighted-distance ball.")),
                    Paragraph(Text(
                        "Prime-power summability controls the tail, while finitely many p-adic "
                            + "balls control the remaining coordinates. This proves the topology "
                            + "clause directly on the source distance rather than hiding it in a "
                            + "new metric instance."))),
                DescribeRole.Theorem))));

    private static Formula Typed(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula TheoremFormula()
    {
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula exponent = F.Id("s");
        Formula prime = F.Id("p");
        Formula address = Call(
            "Pi", Typed(prime, Call("NatPrimes")), Call("PadicInt", prime));
        Formula u = F.Id("u");
        Formula v = F.Id("v");
        Formula w = F.Id("w");
        Formula set = F.Id("T");
        Formula epsilon = F.Id("epsilon");
        Formula distanceUU = Call("primeWeightedDistance", exponent, u, u);
        Formula distanceUV = Call("primeWeightedDistance", exponent, u, v);
        Formula distanceVU = Call("primeWeightedDistance", exponent, v, u);
        Formula distanceUW = Call("primeWeightedDistance", exponent, u, w);
        Formula distanceVW = Call("primeWeightedDistance", exponent, v, w);

        return Disp(new Formula.Aligned([
            Seq(
                Forall, Sp, Typed(exponent, real), Comma, Sp,
                D(1), Sp, Lt, Sp, exponent, Sp, Rightarrow),
            Seq(
                Open, Forall, Sp, Typed(u, address), Comma, Sp,
                distanceUU, Sp, Eq, Sp, D(0), Close, Sp, Land),
            Seq(
                Open, Forall, Sp, Typed(u, address), Comma, Sp,
                Typed(v, address), Comma, Sp,
                distanceUV, Sp, Eq, Sp, distanceVU, Close, Sp, Land),
            Seq(
                Open, Forall, Sp, Typed(u, address), Comma, Sp,
                Typed(v, address), Comma, Sp, Typed(w, address), Comma, Sp,
                distanceUW, Sp, Le, Sp, distanceUV, Sp, Plus, Sp, distanceVW,
                Close, Sp, Land),
            Seq(
                Open, Forall, Sp, Typed(u, address), Comma, Sp,
                Typed(v, address), Comma, Sp,
                distanceUV, Sp, Eq, Sp, D(0), Sp, Rightarrow, Sp,
                u, Sp, Eq, Sp, v, Close, Sp, Land),
            Seq(
                Open, Forall, Sp, Typed(set, Call("Set", address)), Comma, Sp,
                Call("IsOpenIn", Call("ProductTopology", address), set), Sp,
                Leftrightarrow),
            Seq(
                Forall, Sp, Typed(u, address), Comma, Sp,
                u, Sp, InMacro, Sp, set, Comma, Sp,
                Exists, Sp, Typed(epsilon, real), Comma, Sp,
                D(0), Sp, Lt, Sp, epsilon, Sp, Land),
            Seq(
                Forall, Sp, Typed(v, address), Comma, Sp,
                Call("primeWeightedDistance", exponent, u, v), Sp, Lt, Sp,
                epsilon, Sp, Rightarrow, Sp, v, Sp, InMacro, Sp, set, Close, Dot),
        ]));
    }
}
