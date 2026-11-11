using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups;

internal sealed class UniformPartitionAutomorphismsDocument : IScribeDocumentDefinition
{
    private static Formula V(string s) => F.Id(s);
    private static Formula Call(string s, params Formula[] a) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(s))), [.. a]);
    private static Formula All(string s, Formula t, Formula b) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), t, b);
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Context(Formula f) =>
        All("K", V("Typeu"), All("L", V("Typev"), f));
    private static DocumentBlock.Describe Desc(string name, string title, Formula f,
        string text, DescribeRole role = DescribeRole.Definition) =>
        Describe.Lean(DescribeId.Create("uniform-partition-" +
                (name == "Coordinates" ? "coordinate-type" : name.Replace('_', '-').ToLowerInvariant())),
            DeclarationHandle.Create("D5/S3/FiniteGroups/UniformPartitionAutomorphisms." + name),
            H(title), StatementSource.FromAuthor(Disp(f)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create()
    {
        var k = V("K"); var l = V("L");
        var aut = Call("Aut", k, l); var coords = Call("Coordinates", k, l);
        var pk = Call("Perm", k); var pl = Call("Perm", l);
        var family = Arrow(k, pl);
        Formula Nonempty(Formula f) => Imp(Call("Nonempty", l), f);
        var card = Eq(Call("card", aut), new Formula.Binary(
            Call("power", Call("factorial", Call("card", l)), Call("card", k)),
            FormulaBinaryOperator.Multiply, Call("factorial", Call("card", k))));
        return DocumentDefinition.Create(ScribeNode.Create(
            "The full symmetry group of a uniform partition has unique destination-indexed semidirect coordinates.",
            H("Uniform partition automorphisms"), Blocks(
                Paragraph(Text("For x and y in K times L, the relation is equality of first coordinates. "
                    + "Aut is exactly the existing SuccessorQuotient.relationAut subgroup for this relation: "
                    + "its permutations preserve and reflect the relation. Coordinates use the standard Mathlib "
                    + "SemidirectProduct with a family of permutations of L and a permutation of K. "
                    + "Permutation products compose the right factor first.")),
                Desc("Aut", "The full partition symmetry subgroup", Context(
                    Call("Subgroup", Call("Perm", Call("Product", k, l)))),
                    "The subgroup consists of precisely those p for which the first coordinates of p(x) and p(y) "
                    + "are equal if and only if the first coordinates of x and y are equal."),
                Desc("reindex", "Relabeling destination fibers", Context(
                    Call("MonoidHom", pk, Call("MulAut", family))),
                    "For a block permutation alpha, reindex(alpha)(tau)(w) is tau(alpha inverse(w)). "
                    + "This is Mathlib's multiplicative arrow congruence, with its homomorphism law checked pointwise."),
                Desc("Coordinates", "The standard semidirect product", Context(
                    Eq(coords, Call("SemidirectProduct", family, pk, Call("reindex", k, l)))),
                    "Writing coordinates as (sigma,alpha), their product with (tau,beta) is (eta,alpha beta), "
                    + "where eta(w)=sigma(w) tau(alpha inverse(w)). This is the natural action on the block index set; "
                    + "it is not a regular action on the whole block permutation group."),
                Desc("assemble", "Action of the coordinates", Context(
                    Arrow(family, Arrow(pk, aut))),
                    "assemble(s,a) sends (v,t) to (a(v),s(a(v))(t)). It is built with prodCongr followed by "
                    + "prodCongrRight; injectivity of a proves preservation and reflection of the partition relation."),
                Desc("coordinates", "Unique explicit coordinates", Context(Nonempty(
                    Call("Equiv", aut, coords))),
                    "Choose any t in the nonempty fiber type. For p in Aut, alpha(v) is the first coordinate of p(v,t). "
                    + "Relation preservation makes this independent of the fiber coordinate; reflection makes alpha injective, "
                    + "and preimages of (w,t) make it onto. At destination w, sigma(w)(t) is the second coordinate of "
                    + "p(alpha inverse(w),t). Injectivity and surjectivity of p prove that every sigma(w) is a permutation. "
                    + "Assembly and extraction are inverse in both directions. Consequently both alpha and sigma are unique, "
                    + "including for empty K and singleton L. Empty L is excluded: if K has multiple permutations, "
                    + "the action on an empty product cannot determine alpha."),
                Desc("automorphismEquiv", "The full symmetry group isomorphism", Context(Nonempty(
                    Call("MulEquiv", aut, coords))),
                    "The coordinate equivalence is multiplicative. Composing two assembled actions gives precisely "
                    + "eta(w)=sigma(w) tau(alpha inverse(w)); the inverse-index cancellation is verified in Lean. "
                    + "No centralizer or cyclic ordering is imposed."),
                Desc("card_aut", "Exact finite group order", Context(Imp(
                    And(Call("Finite", k), And(Call("Finite", l), Call("Nonempty", l))), card)),
                    "The proved coordinate equivalence identifies the carrier with (K to Perm L) times Perm K. "
                    + "Mathlib's permutation cardinality and function cardinality then give the factorial formula. "
                    + "The empty block-index set gives order one, and singleton fibers give the full permutation group on K.",
                    DescribeRole.Theorem),
                Paragraph(Text("This construction supplies the full uniform-block symmetry structure needed after "
                    + "reconstructing a partition from its saturated subsets. FinitePartitionAlgebraAntiequivalence already "
                    + "provides that reconstruction; MersenneDifferenceZeroSubsets already relates physical zero subsets "
                    + "to rotational invariance. Transport through an arithmetic gcd-residue chart remains a separate obligation. "
                    + "A rotation centralizer retains cyclic order inside each orbit, which saturated subsets do not observe. "
                    + "For orbit lengths three on two blocks the full order is 72, while the rotation centralizer has order 18. "
                    + "For orbit lengths two on three blocks the full order is 48; a regular wreath product indexed by all "
                    + "six block permutations would instead have order 384. These comparisons explain the structural distinction; "
                    + "this module proves the generic classification and does not claim the arithmetic transport or literature novelty."))
            ), []));
    }
}
