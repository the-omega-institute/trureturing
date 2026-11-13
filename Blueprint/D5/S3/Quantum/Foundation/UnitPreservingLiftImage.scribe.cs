using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class UnitPreservingLiftImageDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Foundation/UnitPreservingLiftImage.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Retaining the original unit gives a closed cone lift, its exact minimum-cost perspective and the full compact convex normalized readout image.",
        H("Original-unit lift images"), Blocks(
        Paragraph(Text("This is the cone-geometric statement of Proposition 123.8 of Quantum Origin Same Readback and Parallel Reset Calibration, with an arbitrary real normed readout space W. The quantum coordinates use W=R cubed. V is any finite dimensional real normed carrier; C is its entire closed pointed cone and u is strictly positive on every nonzero cone vector. The original p belongs to the whole base K={x in C : u(x)=1}. The original linear g is nonnegative on all C and vanishes at p; the original linear H vanishes at p. Every cone vector with g=0 is a nonnegative multiple of p. These are the original zero-face facts supplied before Proposition 123.8, rather than a hypothesis of attainment or closedness of the projected image. No EB3 model is substituted for those data: the cone theorem applies before the choice of a matrix model, and makes no assertion of the other native quantum hypotheses.")),
        Describe.Lean(DescribeId.Create("fiber"), DeclarationHandle.Create(Owner + "fiber"),
            H("All feasible original lifts"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For every z in W, the fiber contains every y in the same C with g(y)=1 and H(y)=z. No selected finite readout, effect menu or sampling is used."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("domain"), DeclarationHandle.Create(Owner + "domain"),
            H("Entire feasible readout domain"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The whole domain consists of the z with a nonempty full lift fiber. The theorem identifies it with all H(x)/g(x) for original normalized x distinct from p; g is strictly positive at each such x by the original zero-face hypothesis."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("least-unit"), DeclarationHandle.Create(Owner + "leastUnit"),
            H("Feasible original unit infimum"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Take the real infimum of u over the entire original fiber. Its real value is used only on the feasible domain, where the theorem proves an actual global minimizer."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("unit-cost"), DeclarationHandle.Create(Owner + "unitCost"),
            H("Extended original unit cost"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The extended real cost is the real fiber infimum on its entire feasible domain and positive infinity off the domain. The same original u supplies every cost. It is not a new functional on a quotient."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("lift-map"), DeclarationHandle.Create(Owner + "liftMap"),
            H("Keep the original unit coordinate"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("The linear map sends every original y to (u(y),g(y),H(y)). In particular p has image (1,0,0), whereas zero has image (0,0,0)."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("whole-image"), DeclarationHandle.Create(Owner + "unit_preserving_lift_image"),
            H("Closed cone, exact cost perspective and entire unit slice"), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Under the stated whole-cone hypotheses, the full image of C under (u,g,H) is closed and convex and is stable under every nonnegative scalar. For all real t,s and every z in W, (t,s,z) belongs exactly when either t>=0 and s=z=0, or s>0, z/s is feasible and s times its least original unit cost is at most t. Thus the zero-mass ray and every positive-mass fiber are both retained, including their endpoints. The entire normalized image (g,H)(K) is compact and convex. Its membership criterion is exactly the preceding criterion at t=1, with the zero point included. Every feasible cost is attained by an actual y in C, and that same y is no more expensive than any other feasible original lift. The domain is exactly the normalized original ratio image. Finally, for every real submodule L containing p, u cannot factor through the quotient by L: the quotient kills p while u(p)=1.")),
                Paragraph(Text("The existing mass_cap_compact and base_compact statements supply full original compact caps. For a fixed feasible readout, intersect one such cap with the closed full readout fiber; its continuous minimum is global because every cheaper candidate lies in that cap. For a convergent sequence of full lifted readings, the retained unit coordinate bounds all original preimages in one such cap. A convergent original subsequence then lifts the limiting reading, proving closedness even though the original cone is unbounded. To realize every point above the cost perspective, scale an actual minimum lift by s and add (t-s times its cost) p. This addition changes only the original unit coordinate and stays inside the same cone. It constructs each required point separately and supplies no linear selection of minimizers.")),
                Paragraph(Text("The exact formulas include the entire original mixed base and every cone point. No positive linear section, positive retraction, common preparation, physical instrument or dynamics follows. Neither a global upper bound on costs nor cost-one contact with an original ball is assumed or proved here. The cost-layer and actual support-point identities of Theorem 123.7 and the boundary minimum of Definition 123.9 remain separate obligations. This is a repository-derived cone statement using pinned compactness and subsequence results; literature priority is not asserted."))), DescribeRole.Theorem)))));
}
