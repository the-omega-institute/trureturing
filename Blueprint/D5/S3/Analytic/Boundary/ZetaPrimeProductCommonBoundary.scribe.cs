using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Analytic.Boundary;

internal sealed class ZetaPrimeProductCommonBoundaryDocument
    : IScribeDocumentDefinition
{
    private const string Declaration =
        "D5/S3/Analytic/Boundary/ZetaPrimeProductCommonBoundary."
            + "zeta_prime_product_common_boundary";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The zeta partition, prime activation product, local entropy, and parameter "
            + "sensitivity all cross their convergence boundary at one.",
        H("Zeta Prime-Product Common Boundary"),
        Blocks(Describe.Lean(
            DescribeId.Create("zeta-prime-product-common-boundary"),
            DeclarationHandle.Create(Declaration),
            H("Five concrete thresholds meet at s equals one"),
            StatementSource.FromAuthor(TheoremFormula()),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text(
                    "For a positive real parameter s, the zeta partition is the sum of "
                        + "the logarithmic Gibbs weights, while q at prime p is the source "
                        + "activation probability p to the power minus s. The exponent law "
                        + "is the canonical independent product of the corresponding "
                        + "zero-start geometric coordinate laws.")),
                Paragraph(Text(
                    "The integer and prime p-series criteria put partition finiteness and "
                        + "activation summability exactly above one. Below and at one, the "
                        + "accepted product theorem gives finite-support profiles measure zero; "
                        + "above one, the first Borel-Cantelli lemma gives them measure one.")),
                Paragraph(Text(
                    "The displayed H term is the source geometric-coordinate entropy and the "
                        + "displayed J term is its Fisher sensitivity summand. Lower comparison "
                        + "with prime activation forces divergence through the boundary, while "
                        + "logarithm-weighted p-series bounds give summability above it."))),
            DescribeRole.Theorem))));

    private static Formula TheoremFormula()
    {
        Formula s = F.Id("s");
        Formula p = F.Id("p");
        Formula primeSet = Seq(Mathbb, Grp(F.Id("P")));
        Formula q = Seq(F.Id("q"), Underscore, Grp(p, Comma, s));
        Formula qFamily = Seq(p, Mapsto, Sp, q);
        Formula pToMinusS = Seq(p, Caret, Grp(Minus, s));
        Formula partition = Call("partitionFunction", s);
        Formula localLaw = Seq(GammaLower, Underscore, Grp(p, Comma, s));
        Formula globalLaw = Seq(Gamma, Underscore, Grp(s));
        Formula entropy = Seq(
            F.Id("H"), Underscore, Grp(p), Open, s, Close);
        Formula sensitivity = Seq(
            F.Id("J"), Underscore, Grp(p), Open, s, Close);
        Formula oneMinusQ = Seq(D(1), Sp, Minus, Sp, q);
        Formula entropyValue = Seq(
            Minus, Call("log", oneMinusQ), Sp, Plus, Sp,
            s, Sp, Call("log", p), Sp,
            Frac, Grp(q), Grp(oneMinusQ));
        Formula sensitivityValue = Seq(
            Frac,
            Grp(Seq(Call("log", p), Caret, Grp(D(2)), Sp, q)),
            Grp(Seq(Open, oneMinusQ, Close, Caret, Grp(D(2)))));
        Formula aboveOne = Seq(D(1), Sp, Lt, Sp, s);

        Formula partitionClause = Seq(
            Open, partition, Sp, Neq, Sp, Infty, Sp,
            Leftrightarrow, Sp, aboveOne, Close);
        Formula activationClause = Seq(
            Open, Call("Summable", qFamily), Sp,
            Leftrightarrow, Sp, aboveOne, Close);
        Formula supportClause = Seq(
            Open, Call("Pr", globalLaw, F.Id("FiniteSupportProfiles")),
            Sp, Eq, Sp, D(1), Sp, Leftrightarrow, Sp, aboveOne, Close);
        Formula entropyClause = Seq(
            Open, Call("Summable", Seq(p, Mapsto, Sp, entropy)), Sp,
            Leftrightarrow, Sp, aboveOne, Close);
        Formula sensitivityClause = Seq(
            Open, Call("Summable", Seq(p, Mapsto, Sp, sensitivity)), Sp,
            Leftrightarrow, Sp, aboveOne, Close);

        return Disp(new Formula.Aligned([
            Seq(Forall, Sp, s, InMacro, Sp, Mathbb, Grp(F.Id("R")), Comma, Sp,
                D(0), Sp, Lt, Sp, s, Sp, Rightarrow),
            Seq(
                Forall, Sp, p, InMacro, Sp, primeSet, Comma, Sp,
                q, Sp, Eq, Sp, pToMinusS, Comma, Sp,
                localLaw, Sp, Eq, Sp,
                Call("geometricMeasure", oneMinusQ), Comma),
            Seq(
                globalLaw, Sp, Eq, Sp,
                Call("infinitePi", Seq(p, Mapsto, Sp, localLaw)), Comma, Sp,
                entropy, Sp, Eq, Sp, entropyValue, Comma),
            Seq(sensitivity, Sp, Eq, Sp, sensitivityValue, Comma),
            Seq(partitionClause, Sp, Land),
            Seq(activationClause, Sp, Land),
            Seq(supportClause, Sp, Land),
            Seq(entropyClause, Sp, Land),
            Seq(sensitivityClause, Dot),
        ]));
    }
}
