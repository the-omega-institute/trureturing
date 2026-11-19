using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.RegularRepresentation;

internal sealed class RegularNormalizerSaturationDocument : IScribeDocumentDefinition
{
    private static Formula V(string s) => F.Id(s);
    private static Formula Call(string s, params Formula[] a) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(s))), [.. a]);
    private static Formula QualifiedCall(string ns, string name, params Formula[] a) =>
        new Formula.Apply(Seq(Seq(Operatorname, Grp(V(ns))), Dot,
            Seq(Operatorname, Grp(V(name)))), [.. a]);
    private static Formula All(string s, Formula t, Formula b) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), t, b);
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Le(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.LessThanOrEqual, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Or(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Or, b);
    private static Formula Iff(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Scope(Formula b) =>
        All("K", V("Typeu"), All("H", V("Typev"),
            Seq(OpenBracket, Call("Group", V("H")), CloseBracket, Comma, Sp,
                OpenBracket, Call("Nonempty", V("K")), CloseBracket, Comma, Sp, b)));

    public DocumentDefinition Create()
    {
        var k = V("K");
        var h = V("H");
        var card = QualifiedCall("Nat", "card", h);
        var normalizer = QualifiedCall("DiagonalRegularNormalizer", "diagonalNormalizer", k, h);
        var partitionAut = QualifiedCall("UniformPartitionAutomorphisms", "Aut", k, h);
        var squaresOne = All("h", h, Eq(Mul(V("h"), V("h")), D(1)));
        var classification = Scope(Iff(Eq(normalizer, partitionAut),
            And(Call("Finite", h),
                Or(Le(card, D(2)),
                    And(Call("Subsingleton", k),
                        Or(Eq(card, D(3)), And(Eq(card, D(4)), squaresOne)))))));

        return DocumentDefinition.Create(ScribeNode.Create(
            "For an arbitrary group H and nonempty label type K, the actual diagonal regular normalizer equals the full partition automorphism subgroup exactly when H is finite and either has at most two elements, or K is subsingleton and H has order three or exponent-two order four.",
            H("When the Orbit Partition Captures the Diagonal Regular Normalizer"), Blocks(
                Paragraph(Text("Let K : Type u and H : Type v, where u and v are independent "
                    + "universes, H is a group and K is nonempty. In Sym(K times H), let "
                    + "L(h)(i,x) = (i,h*x). The diagonal subgroup D is the actual range of "
                    + "the homomorphism h mapping to L(h): one h translates every fiber "
                    + "simultaneously. Its orbits are exactly the first-coordinate fibers. "
                    + "Let W = UniformPartitionAutomorphisms.Aut K H. This is the full "
                    + "subgroup of ambient permutations p satisfying fst(p(z)) = fst(p(w)) "
                    + "if and only if fst(z) = fst(w), for every z and w in K times H. "
                    + "It preserves and reflects the complete partition relation and permits "
                    + "permuting the fibers. The displayed equality is between "
                    + "DiagonalRegularNormalizer.diagonalNormalizer K H and W as subgroups "
                    + "of this actual ambient symmetric group.")),
                Describe.Lean(
                    DescribeId.Create("regular-normalizer-saturation-diagonalnormalizer-eq-partitionaut-iff"),
                    DeclarationHandle.Create("D5/S3/FiniteGroups/RegularRepresentation/RegularNormalizerSaturation.diagonalNormalizer_eq_partitionAut_iff"),
                    H("Exact saturation for arbitrary groups and nonempty labels"),
                    StatementSource.FromAuthor(Disp(classification)), AssessedProvenance.FromRepo(),
                    Blocks(Paragraph(Text("The explicit Finite H conjunct is part of the theorem. "
                        + "Nat.card H is zero for an infinite type, so the inequality "
                        + "Nat.card H at most two alone would admit every infinite group. "
                        + "No finite instance on H or finiteness assumption on K is a hypothesis."))),
                    DescribeRole.Theorem),
                Paragraph(Text("Every normalizing permutation lies in W. The existing "
                    + "partition-coordinate equivalence writes any p in W as "
                    + "p(i,x) = (sigma(i),f(i)(x)), with sigma a permutation of K and each "
                    + "f(i) a permutation of H. Set b(i) = f(i)(1) and right-normalize by "
                    + "theta(i)(x) = f(i)(x)*b(i) inverse. Each theta(i) fixes one. "
                    + "The already-proved diagonal-normalizer coordinates say precisely "
                    + "that p normalizes D when all theta(i) equal a single multiplicative "
                    + "automorphism alpha of H. Then f(i)(x) = alpha(x)*b(i), and "
                    + "p*L(h)*p inverse = L(alpha(h)). Right normalization keeps this "
                    + "formula valid for noncommutative groups.")),
                Paragraph(Text("If the normalizer equals W, apply the same identity-fixing "
                    + "permutation f on every fiber. Coordinate extraction gives one alpha "
                    + "equal to f, so every such f preserves multiplication. This forces "
                    + "a finite cover of H by one of two transposition arguments, without "
                    + "starting from a finite carrier.")),
                Paragraph(Text("First suppose a*a differs from one. The three elements "
                    + "1, a and a*a are distinct. If x lay outside them, the transposition "
                    + "of a*a and x would fix 1 and a. Multiplicativity would give "
                    + "x = f(a*a) = f(a)*f(a) = a*a, a contradiction. Thus these three "
                    + "elements cover H, proving finiteness and order three.")),
                Paragraph(Text("Otherwise every element squares to one. If there are "
                    + "distinct nonidentity elements a and b, then 1, a, b and a*b are "
                    + "distinct. An element x outside them could be transposed with a*b "
                    + "while fixing 1, a and b. Multiplicativity would force "
                    + "x = f(a*b) = f(a)*f(b) = a*b. Hence those four elements cover H. "
                    + "If there are no two distinct nonidentity elements, H is covered "
                    + "by one or two elements. These covers give the explicit finiteness "
                    + "conclusion even for an initially arbitrary group.")),
                Paragraph(Text("A second obstruction concerns agreement across labels. "
                    + "Given distinct nonidentity a and b and distinct labels i and j, "
                    + "use the transposition of a and b on fiber i and the identity on "
                    + "every other fiber. All normalized maps fix one. A common alpha "
                    + "would send a to b on fiber i and to a on fiber j, which is "
                    + "impossible. Thus if H has more than two elements, saturation "
                    + "forces K to be subsingleton.")),
                Paragraph(Text("For sufficiency, an identity-fixing permutation of a group "
                    + "of order at most two is the identity. For order three, the proof "
                    + "uses pow_card_eq_one' and the three-element cover to show "
                    + "multiplicativity. For order four with all squares one, Mathlib "
                    + "already supplies IsKleinFour.mulEquiv in "
                    + "Mathlib.GroupTheory.SpecificGroups.KleinFour. The square condition "
                    + "gives Monoid.exponent H dividing two; exponent one would imply "
                    + "Subsingleton H by Monoid.exp_eq_one_iff and hence cardinality one. "
                    + "This constructs IsKleinFour H with cardinality four and exponent "
                    + "two. Applying the existing multiplicative equivalence to an "
                    + "identity-fixing permutation supplies its map_mul law.")),
                Paragraph(Text("Now normalize the recovered fibers of any p in W. With "
                    + "at most two group elements they are all the identity; with one "
                    + "label the single normalized map is multiplicative in either "
                    + "exceptional case. They therefore share one alpha. Reconstructing "
                    + "the imported normalizer coordinates yields the actual p, proving "
                    + "the reverse subgroup inclusion.")),
                Paragraph(Text("Up to group isomorphism, one orbit permits exactly the "
                    + "trivial group, C2, C3 and V4. Two or more labels permit exactly "
                    + "the trivial group and C2, including infinitely many labels. "
                    + "Nonempty labels exclude every infinite H. The partition forgets "
                    + "both multiplication within each fiber and the requirement that "
                    + "one automorphism govern all fibers; the two obstructions explain "
                    + "exactly when that lost information matters.")),
                Paragraph(Text("Separately, when K is empty, K times H is empty and its "
                    + "symmetric group is trivial. The diagonal range, its normalizer "
                    + "and the full partition automorphism group are then the same "
                    + "trivial ambient group for every H. This observation is outside "
                    + "the displayed theorem's nonempty-label hypothesis.")),
                Paragraph(Text("The classification of groups whose identity-fixing "
                    + "bijections are always automorphisms is prior mathematical work. "
                    + "See Mikko Korhonen's answer 491536 to Mathematics Stack Exchange "
                    + "question 452596, with Pete L. Clark's answer 452657 excluding "
                    + "infinite groups and Tobias Kildetoft's answer 452609 treating "
                    + "the finite case: "
                    + "https://math.stackexchange.com/questions/452596/is-a-bijection-from-a-group-to-itself-automatically-an-isomorphism-if-it-maps-th "
                    + "The order-four sufficiency reuses Mathlib's "
                    + "IsKleinFour.mulEquiv. The local formal content is the finite-cover "
                    + "obstruction and common-alpha saturation argument using the "
                    + "existing coordinate extraction."))
            ), []));
    }
}
