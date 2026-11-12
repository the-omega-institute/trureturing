using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.RegularRepresentation;

internal sealed class DiagonalRegularNormalizerDocument : IScribeDocumentDefinition
{
    private static Formula V(string s) => F.Id(s);
    private static Formula App(Formula f, params Formula[] a) => new Formula.Apply(f, [.. a]);
    private static Formula Call(string s, params Formula[] a) =>
        App(Seq(Operatorname, Grp(V(s))), a);
    private static Formula All(string s, Formula t, Formula b) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(s), t, b);
    private static Formula Some(string s, Formula t, Formula b) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(s), t, b);
    private static Formula Eq(Formula a, Formula b) =>
        new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula Iff(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Pair(Formula a, Formula b) => Seq(Open, a, Comma, Sp, b, Close);
    private static Formula Product(Formula a, Formula b) => Seq(a, Sp, Times, Sp, b);
    private static Formula Mul(Formula a, Formula b) =>
        new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Perm(Formula t) => Call("Perm", t);
    private static Formula GroupAut(Formula t) => Call("MulAut", t);
    private static Formula Fst(Formula t) => Call("fst", t);
    private static Formula Snd(Formula t) => Call("snd", t);
    private static Formula KH() => Product(V("K"), V("H"));
    private static Formula DiagonalHom() => Call("diagonalHom", V("K"), V("H"));
    private static Formula Diagonal() => Call("diagonal", V("K"), V("H"));
    private static Formula Normalizer() => Call("diagonalNormalizer", V("K"), V("H"));
    private static Formula Parameters() => Call("Parameters", V("K"), V("H"));
    private static Formula AmbientNormalizer() =>
        App(new Formula.Subscript(Seq(Operatorname, Grp(V("N"))), Perm(KH())), Diagonal());
    private static Formula Scope(Formula b, bool nonempty = false)
    {
        if (nonempty)
            b = Seq(OpenBracket, Call("Nonempty", V("K")), CloseBracket, Comma, Sp, b);
        b = Seq(OpenBracket, Call("Group", V("H")), CloseBracket, Comma, Sp, b);
        return All("K", V("Typeu"), All("H", V("Typev"), b));
    }
    private static Formula CoordinateValue(Formula t, Formula i, Formula x) =>
        Pair(App(Fst(t), i), Mul(App(Fst(Snd(t)), x), App(Snd(Snd(t)), i)));
    private static Formula CoordinateLaw(Formula p, Formula t) =>
        All("i", V("K"), All("x", V("H"),
            Eq(App(p, Pair(V("i"), V("x"))), CoordinateValue(t, V("i"), V("x")))));

    private static DocumentBlock.Describe Desc(string name, string title, Formula f,
        string text, DescribeRole role = DescribeRole.Theorem) =>
        Describe.Lean(
            DescribeId.Create("diagonal-regular-normalizer-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/FiniteGroups/RegularRepresentation/DiagonalRegularNormalizer." + name),
            H(title), StatementSource.FromAuthor(Disp(f)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create()
    {
        var k = V("K");
        var h = V("H");
        var p = V("p");
        var t = V("t");
        var s = V("s");
        var i = V("i");
        var x = V("x");
        var sigma = V("sigma");
        var alpha = V("alpha");
        var b = V("b");
        var triple = Pair(sigma, Pair(alpha, b));
        var e = Call("normalizerEquiv", k, h, p);

        var diagonalHom = Scope(All("h", h, All("i", k, All("x", h,
            Eq(App(App(DiagonalHom(), V("h")), Pair(i, x)), Pair(i, Mul(V("h"), x)))))));
        var diagonal = Scope(Eq(Diagonal(),
            new Formula.SetBuilder(App(DiagonalHom(), V("h")), V("h"), h)));
        var normalizer = Scope(Eq(Normalizer(), AmbientNormalizer()));
        var parameters = Scope(Eq(Parameters(),
            Product(Perm(k), Seq(Open, Product(GroupAut(h),
                Seq(Open, new Formula.TypeArrow(k, h), Close)), Close))));
        var coordinatePerm = Scope(All("sigma", Perm(k), All("alpha", GroupAut(h),
            All("b", new Formula.TypeArrow(k, h), All("i", k, All("x", h,
                Eq(App(Call("coordinatePerm", k, h, triple), Pair(i, x)),
                    Pair(App(sigma, i), Mul(App(alpha, x), App(b, i))))))))));
        var equivalence = Scope(Seq(Call("normalizerEquiv", k, h), Colon, Sp,
            Call("Equiv", Normalizer(), Parameters())),
            nonempty: true);
        var evaluation = Scope(All("p", Normalizer(), CoordinateLaw(p, e)), nonempty: true);
        var uniqueCoordinates = Some("t", Parameters(), And(CoordinateLaw(p, t),
            All("s", Parameters(), Imp(CoordinateLaw(p, s), Eq(s, t)))));
        var classification = Scope(All("p", Perm(KH()),
            Iff(new Formula.Relation(p, FormulaRelationOperator.MemberOf, AmbientNormalizer()),
                uniqueCoordinates)), nonempty: true);

        return DocumentDefinition.Create(ScribeNode.Create(
            "For any group H and nonempty label type K, the ambient normalizer of simultaneous left translations on K times H has unique coordinates consisting of a label permutation, one common group automorphism and source-indexed right translations, with an explicit equivalence of types and evaluation law.",
            H("Coordinates of the Diagonal Regular Normalizer"), Blocks(
                Paragraph(Text("Let K : Type u and H : Type v be arbitrary types, with H a group. "
                    + "Write Sym(K times H) for Equiv.Perm (K times H), with multiplication given by "
                    + "composition. For h in H, the same left translation L(h) acts on every label: "
                    + "L(h)(i,x) = (i,h*x). The subgroup D is the actual range of h mapping to L(h), "
                    + "and N is its normalizer in this ambient symmetric group. The formulas below "
                    + "use diagonalHom, diagonal and diagonalNormalizer for L, D and N. "
                    + "Typeu and Typev denote arbitrary, independently chosen type universes.")),
                Desc("diagonalHom", "Simultaneous left translation on every label", diagonalHom,
                    "diagonalHom K H is a monoid homomorphism from H to Perm (K times H). "
                    + "The label action is trivial and the action on H is left multiplication, "
                    + "so its evaluation is exactly the displayed formula.", DescribeRole.Definition),
                Desc("diagonal", "The diagonal subgroup is the actual translation range", diagonal,
                    "The displayed set is range (diagonalHom K H), regarded as a subgroup of "
                    + "Perm (K times H). Its elements use one and the same h at every label. "
                    + "There is no independently chosen translation parameter for each label in D.",
                    DescribeRole.Definition),
                Desc("diagonalNormalizer", "The normalizer in the ambient symmetric group", normalizer,
                    "N with subscript Perm (K times H) denotes Subgroup.normalizer of the underlying "
                    + "set of D in that ambient group. Thus p belongs to N exactly when conjugation "
                    + "by the actual permutation p preserves D in both directions.", DescribeRole.Definition),
                Desc("Parameters", "The type of permutation, automorphism and translation coordinates", parameters,
                    "A parameter is the right-associated triple (sigma,alpha,b), where sigma is a "
                    + "permutation of K, alpha is a multiplicative group automorphism of H, and b "
                    + "is a function from K to H. In the formulas fst(t), fst(snd(t)) and snd(snd(t)) "
                    + "are these three coordinates. This is a product type; no group operation on "
                    + "triples is specified.", DescribeRole.Definition),
                Desc("coordinatePerm", "The ambient permutation determined by coordinates", coordinatePerm,
                    "Equiv.prodCongrRight first applies alpha followed by right multiplication "
                    + "by b(i) on the H coordinate, and Equiv.prodCongr then applies sigma to the "
                    + "label. The translation is indexed by the source label i. The order alpha(x)*b(i) "
                    + "is essential for a possibly noncommutative H: these are right translations.",
                    DescribeRole.Definition),
                Desc("normalizerEquiv", "An equivalence of types between the actual normalizer and coordinates", equivalence,
                    "With nonempty K, normalizerEquiv is a type equivalence N to Parameters K H. "
                    + "Its inverse sends a triple to coordinatePerm together with membership in the "
                    + "actual ambient normalizer. It is not stated as a group equivalence, and "
                    + "no multiplication law for the parameter triples is part of this definition.",
                    DescribeRole.Definition),
                Desc("normalizerEquiv_eval", "Evaluation of the coordinates of a normalizing permutation", evaluation,
                    "For p in N, take t = normalizerEquiv K H p. The formula is p(i,x) = "
                    + "(sigma(i),alpha(x)*b(i)) with exactly the three projections of t. This "
                    + "evaluation supplies the coordinate equality in the forward implication "
                    + "of the membership classification and identifies the reconstructed permutation."),
                Desc("mem_normalizer_iff_existsUnique_coordinates", "Full ambient-normalizer classification with unique coordinates", classification,
                    "For every ambient permutation p, membership in N is equivalent to existence "
                    + "of a triple with the coordinate formula for every i and x, together with "
                    + "equality of every other such triple to it. The displayed existential and "
                    + "universal condition expands unique existence in the right-associated product "
                    + "Perm K times MulAut H times (K to H). A single alpha governs every label."),
                Paragraph(Text("To reconstruct coordinates, first identify H with the actual diagonal "
                    + "range by the faithful-action equivalence Equiv.Perm.subgroupOfMulAction. "
                    + "Normalization gives an automorphism of D through Subgroup.normalizerMonoidHom. "
                    + "Transport it with MulAut.congr to obtain alpha on H before selecting any "
                    + "reference label. Conjugation in the ambient group gives "
                    + "L(alpha(h)) = p*L(h)*p inverse, hence the twisted equivariance equation "
                    + "p(i,h*x) = (fst(p(i,x)),alpha(h)*snd(p(i,x))). "
                    + "Thus the common automorphism comes from one conjugation action, rather "
                    + "than separate choices on different blocks.")),
                Paragraph(Text("Set k(i) = fst(p(i,1)) and b(i) = snd(p(i,1)). Substituting x at "
                    + "the identity into twisted equivariance gives p(i,x) = (k(i),alpha(x)*b(i)). "
                    + "It remains to prove that k is a permutation. If k(i) = k(j), choose "
                    + "x = alpha inverse (b(i)*b(j) inverse). Then p(j,x) = p(i,1), so injectivity "
                    + "of p forces i = j. To reach a label j, take any preimage of (j,1) under p; "
                    + "the coordinate formula shows that its source label maps to j under k. "
                    + "These arguments give both injectivity and surjectivity without finiteness, "
                    + "so k determines sigma in Perm K.")),
                Paragraph(Text("Conversely, the coordinate construction is an actual bijection of "
                    + "K times H. Computing its conjugation gives p*L(h)*p inverse = L(alpha(h)) "
                    + "in Sym(K times H). Surjectivity of alpha, or equivalently applying alpha "
                    + "inverse, gives the reverse range inclusion as well, proving membership "
                    + "in the ambient normalizer. For uniqueness, evaluate two coordinate "
                    + "descriptions at (i,1) to recover sigma and b. At one label, equality "
                    + "alpha(x)*b(i) = beta(x)*b(i) and right cancellation recover alpha for "
                    + "every x. This last step uses Nonempty K.")),
                Paragraph(Text("Trivial H and infinite K or H are included: no nontriviality, "
                    + "Fintype, cardinality or commutativity assumption is used. Nonempty K is "
                    + "essential for this uniform uniqueness assertion; if K is empty, distinct "
                    + "automorphisms of H can describe the same empty permutation. This theorem "
                    + "classifies normalization of the diagonal regular action. Preservation "
                    + "of the label partition alone does not impose its common-automorphism "
                    + "condition, and is a different symmetry question.")),
                Paragraph(Text("For finite nonempty K with cardinality r and a finite cyclic group H of order m, "
                    + "normalizerEquiv gives cardinality r! times m^r times phi(m). The permutation "
                    + "factor contributes r!, functions K to H contribute m^r, and IsCyclic.card_mulAut "
                    + "gives phi(m) automorphisms. The single common alpha supplies one totient factor, "
                    + "not a separate automorphism choice for each label. This count uses the type "
                    + "equivalence and does not require a group law on parameter triples.")),
                Paragraph(Text("For n > 0 and a a natural number, put t = (finRotate n)^a, H = Subgroup.zpowers t, "
                    + "r = gcd(n,a) and m = n/r. The subgroup H acts freely on Fin n: an element fixing "
                    + "one point commutes with the transitive full rotation and therefore fixes all points. "
                    + "For Omega the H-orbit quotient, the existing Mathlib selfEquivOrbitsQuotientProd "
                    + "chart has inverse (omega,h) mapping to h acting on omega.out; its verified "
                    + "equivariance transports the actual subgroup H, by ambient permutation congruence, "
                    + "onto the diagonal range on Omega times H. Normalizer transport therefore applies "
                    + "to the actual chosen subgroup. Here |H| = m and n = |Omega|m = rm with m > 0, "
                    + "so |Omega| = r. Thus the exact normalizer cardinality is r! times m^r times phi(m). "
                    + "This includes a = 0, n = 1 and m = 1; for n = 6 and a = 2 the normalizer has "
                    + "36 elements while the complete orbit-relation automorphism group has 72. "
                    + "The latter comparison is a mathematical consequence, not a new library theorem."))
            ), []));
    }
}
