using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuadraticForms;

internal sealed class SymmetricRankOneGuardsDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/QuadraticForms/SymmetricRankOneGuards.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Uncancelled integer polynomial guards propagate the zero-nullity scalar state and give a finite exact set of candidate shifts.",
        H("Polynomial guards and finite candidate shifts"),
        Blocks(
            Paragraph(Text("Use a common real shift x and integer polynomials P(i), Q(i) for the child response ratios. At a proper cotree leaf with parent label q take P = −1 and Q = X + q. At an internal node of label c with parent label q use t = c − q, with join labeled 1, union labeled 2, and q = 0 at the root.")),
            Paragraph(Text("An induction using the degree and propagation statements gives monic subtree guards and nullity zero at shifts outside their root union. At a candidate shift use the exact flagged, resonant or nonresonant transition at the same shift in every block. The union includes poles and counts coincident roots once.")),
            Entry("responseNumerator", "Common response numerator",
                Seq(V("P"), Eq, Sum, Sp, Call("P", V("i")), Sp, Prod, Sp, Call("Q", V("j"))), DescribeRole.Definition,
                "Sum over all child indices i. In the ith summand the product is over all j other than i."),
            Entry("responseGuard", "Uncancelled output guard",
                Seq(V("Q"), Eq, V("R"), Plus, V("t"), V("P")), DescribeRole.Definition,
                "R is the product of all child guards over the integer polynomial ring. The coupling adds t times the common numerator P to R."),
            Entry("update_block_of_guard_ne_zero", "Scalar propagation at a common shift",
                Seq(V("k"), Eq, D(0), Sp, Land, Sp, Call("Response", V("U"), V("u"), Seq(Frac, Grp(Call("P", V("x"))), Grp(Call("Q", V("x")))))), DescribeRole.Theorem,
                "Take a finite family of finite-dimensional real symmetric blocks with product direction u. At x every child guard and the output guard must be nonzero. If each child has zero nullity and response P(i)(x)/Q(i)(x), then the real coupling by the integer t has zero nullity and response P(x)/Q(x). The ratio comes from the nonresonant update of the block sum."),
            Entry("responseGuard_degrees", "Guard and numerator degrees",
                Seq(Call("deg", V("P")), Eq, V("N"), Minus, D(1), Sp, Land, Sp, Call("lc", V("P")), Eq, Minus, V("N"), Sp, Land, Sp, Call("Monic", V("Q")), Sp, Land, Sp, Call("deg", V("Q")), Eq, V("N")), DescribeRole.Theorem,
                "For a nonempty finite child family, suppose each size n(i) is positive, Q(i) is monic of natural degree n(i), and P(i) has natural degree n(i) − 1 and leading coefficient −n(i). The displayed N is the sum of those sizes. The coefficient sum is −N, and adding the lower-degree term tP preserves the monic leading term of R."),
            Entry("realGuardCandidates", "Distinct real roots of the guards",
                Seq(V("C"), Eq, Cup, Sp, Call("roots", Call("Q", V("i")))), DescribeRole.Definition,
                "The union runs over the specified finite index set s. Each guard is mapped from the integers to the reals before its roots are taken, and root multiplicities are discarded."),
            Entry("realGuardCandidates_spec", "The finite exact shift criterion",
                Seq(Call("card", V("C")), Sp, Leq, Sp, Sum, Sp, Call("deg", Call("Q", V("i"))), Sp, Land, Sp, Open, Open, Exists, Sp, V("x"), Comma, Sp, Call("target", V("x")), Close, Sp, Iff, Sp, Open, Exists, Sp, V("x"), Sp, InMacro, Sp, V("C"), Comma, Sp, Call("target", V("x")), Close, Close), DescribeRole.Theorem,
                "All guards indexed by s are nonzero polynomials. Assume the target predicate fails at every real x where all those guards are nonzero. The sum runs over s, and the existential equivalence uses the same target at each candidate, including eligibility and saturation when those form the target. The finite set is a mathematical real-root criterion."))));

    private static DocumentBlock Entry(string name, string title, Formula statement,
        DescribeRole role, string explanation) => Describe.Lean(
        DescribeId.Create(name.Replace('_', '-').ToLowerInvariant()),
        DeclarationHandle.Create(Owner + name), H(title), StatementSource.FromAuthor(Disp(statement)),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(explanation))), role);

    private static Formula V(string name) => F.Id(name);

}
