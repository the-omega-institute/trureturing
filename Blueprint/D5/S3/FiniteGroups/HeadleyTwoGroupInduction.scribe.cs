using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups;

internal sealed class HeadleyTwoGroupInductionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every finite noncyclic additive abelian two-group has a cyclic ordering of its nonzero elements whose directed differences run through those same elements exactly once.",
        H("R-cycles for all noncyclic finite abelian two-groups"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("headley-all-noncyclic-two-groups-r-cycle"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/HeadleyTwoGroupInduction.finite_noncyclic_two_group_r_cycle"),
                H("The unbounded two-primary induction"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let G be a finite additive abelian group whose multiplicative type tag is a two-group, and suppose G is not cyclic. Then G has an RCycle: a permutation fixing zero and acting as a single cycle on every nonzero element, together with a permutation equal to successor(x)-x at every x. The conclusion includes all elementary ranks at least two, in particular C2 cubed, and the R-only group C2 times C4.")),
                    Paragraph(Text("The finite abelian structure theorem gives cyclic prime-power coordinates. Every positive factor prime divides the two-primary group cardinality and is therefore two; zero exponents are retained as trivial factors. Noncyclicity forces two positive exponents. Induction is on their unrestricted natural exponent sum and is generalized over all finite coordinate families.")),
                    Paragraph(Text("For an elementary family, a primitive unit acts transitively on the nonzero elements of a finite field. Its additive displacement is multiplication by that unit minus one, which is another permutation because the field has at least four elements. This relates the multiplicative group action to the directed additive-difference inventory, and a basis transports the resulting cycle to the original elementary coordinates.")),
                    Paragraph(Text("When exactly two positive factors have minimum exponent one, E4 and the explicit seven-vertex C2 times C4 word give the small leaves. For larger second exponent the original rank-two powerTwoRStar construction supplies the cycle. Every other case lowers exactly two positive exponents, retaining two positive coordinates and decreasing the sum by two. The actual reduction kernel is the doubled-coordinate range, is additively equivalent to that decremented coordinate family, and has quotient E4. The nonsplit extension theorem combines the recursively obtained kernel R-cycle with the E4 R-star quotient. It does not assume the extension is a direct product or that the kernel is R-star.")),
                    Paragraph(Text("This is a formal reconstruction of the R-sequenceability induction associated with P. Headley, R-sequenceability and R-star-sequenceability of abelian 2-groups, Discrete Mathematics 131, 345-350, DOI 10.1016/0012-365X(94)90396-4, using the explicit kernel splice and the original uniform rank-two construction. No originality claim is made. The elementary and order-eight cycles are leaves of this unbounded construction.")),
                    Paragraph(Text("A subsequent odd-factor argument can use this R-cycle on a doubled kernel and an R-star quotient of type E4 times an odd group. An R-only seed is not itself an input to the odd R-star product theorem. This theorem neither asserts R-star for every noncyclic two-group nor completes that final odd-factor assembly, the proper-fullset consumer, or the arbitrary-subset and AM problems."))),
                DescribeRole.Theorem))));
}
