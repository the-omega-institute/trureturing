using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Robin.PriceRecord;

internal sealed class CurvatureCorrectedArithmeticSurplusDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The full prime-power arithmetic surplus pays the literal log-log curvature loss.",
        H("Arithmetic surplus after curvature"),
        Blocks(
            Describe.Lean(
            DescribeId.Create("root-scale-surplus-after-curvature"),
            DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/CurvatureCorrectedArithmeticSurplus.arithmetic_surplus_sub_curvature_root_scale"),
            H("The quantitative root-scale remainder"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For z>11, 0<M<1/2 and every positive integer n on the exact initial prime support, the full signed surplus minus K exceeds 1/(4000*sqrt(z)*log(z)), where K=log(log(z))+M/(z*log(z))-log(log(z+M)). The existing curvature bound and old arithmetic estimate prove K<Delta/2. The all-z root-scale theorem supplies Delta>1/(2000*sqrt(z)*log(z)); thus half of the actual surplus remains. No exponent, containment, signed-integral or extremality premise is added."))), DescribeRole.Theorem),
            Describe.Lean(
            DescribeId.Create("full-prime-power-surplus-after-curvature"),
            DeclarationHandle.Create("D5/S3/Arith/Robin/PriceRecord/CurvatureCorrectedArithmeticSurplus.arithmetic_surplus_dominates_loglog_curvature"),
            H("A strict positive remainder for the actual finite state"),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("For z>11, 0<M<1/2, and an actual positive integer n with exactly the prime support p<=z, with no assumption that n contains all prime powers up to z, let K=log(log(z))+M/(z*log(z))-log(log(z+M)). Then 0<K<(log(z)+1)/(8*z^2*log(z)^2), and the full arithmetic surplus minus K exceeds log(2)/(12*z*log(z)). The surplus uses the literal tail(n), log(n)-Chebyshev.psi(z), and all omitted prime-power layers k>=2; prime-power equality remains in psi.")),
                Paragraph(Text("The private curvature estimate uses two applications of log(1+u)>=u-u^2/2, obtained from the existing rational lower bound 2*u/(u+2)<=log(1+u). Existing strict log-log tangency gives K>0. The stronger actual full_prime_power_arithmetic_surplus theorem supplies the arithmetic lower bound for arbitrary positive valuations on this exact support, including underfilled prime-power inventories. Its signed deficit argument retains the entire reference tail; no hcontains premise is used. This finite-state inequality assumes neither a desired residual sign nor a signed-integral identity, and asserts no RH conclusion."))),
            DescribeRole.Theorem))));
}
