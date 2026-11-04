using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Weil.Mertens.IntegratedExplicit;
internal sealed class ActualKernelMomentLiteralVDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complete literal-V moment obstruction.",
        H("Consuming literal-V source"), Blocks(
            Describe.Lean(DescribeId.Create("literal-v-energy-moment-obstruction"),
                DeclarationHandle.Create("D5/S3/Weil/Mertens/IntegratedExplicit/ActualKernelMomentLiteralV.literal_V_energy_moment_obstruction"),
                H("Explicit literal V energy obstruction"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every natural number q>=1 and every D>=log(2)+1/16, an explicit family indexed by Fin(q) x Fin(3) x Bool has 6q listed atoms in [0,1/16] union [log(2),log(2)+1/16]. Put ell=1/(16q), r=exp(-ell/4), and nu=delta(0)-(1+r)delta(ell/2)+r delta(ell). The family is (I-T_log(2))(I-T_ell)^(q-1)nu. Its complex polynomial moments vanish through degree q and its positive exponential moment vanishes. Its degree q+1 moment and its x exp(x/2) moment are nonzero. The original prefix energy is strictly positive and the inclusive full Mangoldt expression satisfies V/E<=-1/(65536q^2), including q=1 and every later prime-power cutoff.")),
                    Paragraph(Text("Finite differences give the exact residuals (-1)^(q+1)(q+1)! log(2) ell^q(1-r)/2 and (ell/2)(1-exp(log(2)/2))(1-exp(ell/2))^(q-1)(exp(ell/4)-1). The actual finite resolvent identity makes the three-atom response vanish outside [-ell,ell]. Translation separation scales energy and W by the same positive sum of squared binomial coefficients. The two log(2)-separated copies have energy 2N Eg and S(log(2))=-N Wg. Combining the two continuum shifts before estimating gives a bound 4h exp((log(2)+h)/2)N Wg, where h=1/16. All integer terms from 3 onward and the boundary vanish exactly. The scalar estimate Wg>=r^2 ell^3/48 supplies the stated energy constant. This is a literal-V obstruction at fixed support; it makes no full-K or RH claim and asserts no necessary dependence of moment order on D."))),
                DescribeRole.Theorem))));
}
