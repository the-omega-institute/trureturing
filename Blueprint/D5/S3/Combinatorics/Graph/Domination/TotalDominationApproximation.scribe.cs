using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Domination;

internal sealed class TotalDominationApproximationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/Domination/TotalDominationApproximation.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The same integer exponent approximates both logarithmic coordinates of a complex target.",
        H("Joint logarithmic power-root approximation"), Blocks(
            Paragraph(Text("The complex exponential is the existing Mathlib exponential. No graph or density hypothesis enters this analytic lemma. The conclusion chooses a single natural exponent for both the modulus and angle; it does not combine separately optimal branches.")),
            Node("joint_power_root_approximation", "Joint radial and angular approximation",
                "For every complex xi with nonzero real part and every positive real epsilon there is a natural N such that, for all real t and alpha with N+2<t/xi.re, there exist a positive natural k and a complex w satisfying w^k=exp(t+alpha*I) and norm(w-exp(xi))<epsilon. Let p=t/xi.re and k=floor(p). The same k obeys k>N and abs(t/k-xi.re)<=abs(xi.re)/k. Round (k*xi.im-alpha)/(2*pi) to an integer j and set v=t/k+((alpha+2*pi*j)/k)*I. Exact exponential periodicity gives (exp(v))^k=exp(t+alpha*I), while abs(v.im-xi.im)<=pi/k. Thus norm(v-xi)<delta for the continuity radius delta of exp at xi. The bound on N is chosen before t and alpha. This is an elementary logarithmic approximation ingredient, with all rounding, powers and continuity checked in Lean; no literature-priority claim is made.")), []));

    private static DocumentBlock Node(string selector, string title, string prose) =>
        Describe.Lean(DescribeId.Create("td-approx-" + selector.Replace("_", "-").ToLowerInvariant()), DeclarationHandle.Create(Prefix + selector),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
}
