using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Estimation.DataProcessing;

internal sealed class BorelIidStrictPeakLowerDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Finite rational-cut approximations transport the strict-peak lower surface to arbitrary Borel laws.",
        H("Borel Independent Strict Peaks via Finite Sources"),
        Blocks(Describe.Lean(
            DescribeId.Create("borel-iid-lower-surface"),
            DeclarationHandle.Create("D5/S3/Estimation/DataProcessing/BorelIidStrictPeakLower.borel_iid_lower_surface"),
            H("The universal Borel lower bound"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(),
            Blocks(
                Paragraph(Text("Let mu be any Borel probability measure on the real line. The actual source is the five-fold product measure on Fin 5 -> R, and its modeMass values are the integrals of the strict-peak classifier indicators. The code order is null, left endpoint, right endpoint, both endpoints, middle. No CDF formula defines these probabilities. The independently defined law satisfies X=integral a(v)^2 dmu(v), where a(v)=mu((-infinity,v)).")),
                Paragraph(Text("The five masses are nonnegative and sum to one. Put X=modeMass(1)+modeMass(3) and D=modeMass(0)modeMass(3)-modeMass(1)modeMass(2). Then modeMass(2)+modeMass(3)=modeMass(4)=X, 0<=X<=1/3, D>=-X/15, and D>=-1/45. There exists s in [0,1] with s^3=1-3X such that D+X/15 >= s^3(1-s)(1+s+7s^2-3s^3-3s^4)/45 >= 0. If 0<X<1/3, then D>-X/15. For every real c the quantitative atom deficit gives 3X+mu({c})^3<=1 and D+1/45>=mu({c})^3/45. Every positive-mass atom therefore makes D>-1/45, including laws with infinite support. Also X=0 if and only if mu is a Dirac measure. The joint mass satisfies X-1/5<=modeMass(3)<=2/15, so X=1/3 if and only if D=-1/45; this endpoint implies every singleton has measure zero.")),
                Paragraph(Text("Enumerate rational cuts and map x to the number of the first n cuts lying strictly below x. This is a measurable monotone map into Fin(n+1). Equal inputs stay equal at every stage, and each strictly ordered pair is eventually separated by a rational cut. Thus the classifier of every actual five-sample tuple eventually agrees with its original classifier. Bounded convergence proves convergence of all five probabilities, including laws with atoms.")),
                Paragraph(Text("The coordinatewise pushforward of the common five-fold product source is the product of its finite pushforward letter law. Finite product integration equals the independently defined weighted source sum. The finite determinant inequality therefore passes to the original law by continuity. Three mutually exclusive strict maxima and the all-c tuple give the finite atom deficit. The quantized cell containing c has mass at least mu({c}), so this deficit survives passage to the original source. Compactness of the chosen cubic roots in [0,1] transports the full correction along a convergent subsequence; its polynomial factor is strictly positive in the interior. The lower-CDF identity follows from two applications of bounded convergence to the same quantization: first for each strict-comparison probability, then for its square. For the zero endpoint, the vanishing lower-CDF square integral forces both independent order directions to have zero probability. Swapping the two samples gives a common almost-sure constant, whose pushforward law is Dirac. The implication from an atomless law to X=1/3 remains unproved here, as does the original full atomless equality classification. Strictness at every finite stage alone is not passed to the limit."))),
            DescribeRole.Theorem))));
}
