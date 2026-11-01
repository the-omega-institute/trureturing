using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Topology.TauCeti.Algebra.Homology;

internal sealed class OrderedCechCoverDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Topology/TauCeti/Algebra/Homology/OrderedCechCover.";
    private static Formula V(string name) => F.Id(name);
    private static Formula All(string name, Formula type) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp);
    private static Formula Inst(string name, params Formula[] args) =>
        Seq(OpenBracket, Call(name, args), CloseBracket, Sp);
    private static Formula CategoryContext =>
        Seq(All("C", Call("Type", V("u"))), Inst("Category", V("v"), V("C")),
            Inst("HasCoproducts", V("w"), V("C")));
    private static Formula DomainContext =>
        Seq(All("iota", Call("Type", V("w"))), All("A", Call("Type", V("w"))));
    private static Formula FamilyContext =>
        Seq(All("R", V("C")), All("P", Seq(V("iota"), Sp, To, Sp, Call("Set", V("A")))));
    private static Formula AdditiveContext =>
        Seq(Grp(), Inst("Preadditive", V("C")), Inst("LinearOrder", V("iota")));
    private static Formula ZeroContext => Seq(Grp(), Inst("HasZeroObject", V("C")));
    private static Formula[] Context(bool additive, bool zero) => zero
        ? (additive ? [CategoryContext, DomainContext, FamilyContext, AdditiveContext, ZeroContext]
            : [CategoryContext, DomainContext, FamilyContext, ZeroContext])
        : (additive ? [CategoryContext, DomainContext, FamilyContext, AdditiveContext]
            : [CategoryContext, DomainContext, FamilyContext]);
    private static Formula K => Call("complex", V("R"), V("P"));
    private static Formula Free => Call("coproduct", V("A"), V("R"));
    private static Formula Single => Call("singleZero", Free);
    private static Formula Epsilon => Call("augmentation", V("R"), V("P"));
    private static Formula FunctorDefinition => Disp(new Formula.Aligned([
        .. Context(false, false),
        Seq(Call("freeFunctor", V("R"), V("P")), Colon, Sp,
            Call("Functor", Call("op", Call("Finset", V("iota"))), V("C"))),
        Seq(Forall, Sp, V("s"), Colon, Sp, Call("Finset", V("iota")), Comma, Sp,
            Seq(Call("obj", Call("freeFunctor", V("R"), V("P")), Call("op", V("s"))), Sp, Eq, Sp,
                Call("coproduct", Call("intersectionPoints", V("P"), V("s")), V("R"))))
    ]));
    private static Formula ComplexDefinition => Disp(new Formula.Aligned([
        .. Context(true, false), Seq(K, Colon, Sp, Call("ChainComplex", V("C"), V("Nat"))),
        Seq(All("p", V("Nat")), Call("X", K, V("p")), Sp, Eq, Sp,
            Call("coproduct", Call("finsetsOfCard", V("iota"), Call("succ", V("p"))),
                Call("intersectionFreeObjects", V("R"), V("P"))))
    ]));
    private static Formula AugmentationDefinition => Disp(new Formula.Aligned([
        .. Context(true, true), Seq(Epsilon, Colon, Sp, Call("Hom", K, Single)),
        Seq(Forall, Sp, V("s"), Colon, Sp, Call("finsetsOfCard", V("iota"), D(1)), Comma, Sp,
            Seq(Forall, Sp, V("a"), Colon, Sp, Call("intersectionPoints", V("P"), V("s")), Comma, Sp,
                Seq(Call("degreeZeroPointImage", Epsilon, V("s"), V("a")), Sp, Eq, Sp,
                    Call("pointInclusion", Call("val", V("a")), Free))))
    ]));
    private static Formula Equivalence => Disp(new Formula.Aligned([
        .. Context(true, true),
        Seq(Call("iUnion", V("P")), Sp, Eq, Sp, Call("univ", V("A")), Sp, Rightarrow),
        Seq(Exists, Sp, V("E"), Colon, Sp, Call("HomotopyEquiv", K, Single), Comma, Sp,
            Call("hom", V("E")), Sp, Eq, Sp, Epsilon)
    ]));
    private static AssessedProvenance Source => AssessedProvenance.FromLiterature(
        LibraryNoteRef.Create("D5/L/Topology/tauceti2026orderedcechcover"));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual ordered free complex of an arbitrary set cover contracts onto the free object on its points.",
        H("The ordered free complex of a set cover"), Blocks(
            Paragraph(Text("There are three independent universes: C has objects in Type u and morphisms in Type v; "
                + "the linearly ordered index type iota and the point type A lie in Type w. "
                + "HasCoproducts(w,C) means that every Type w-indexed family has its existing categorical coproduct. "
                + "The coefficient is an arbitrary object R. Preadditivity supplies addition and integer signs on morphisms. "
                + "A zero object is used for the complex concentrated in degree zero. "
                + "No finiteness or nonemptiness assumption is made on iota or A.")),
            Describe.Lean(DescribeId.Create("intersection-coproduct-functor"),
                DeclarationHandle.Create(Owner + "freeFunctor"), H("The actual intersection objects"),
                StatementSource.FromAuthor(FunctorDefinition), Source,
                Blocks(Paragraph(Text("For a finite set s of indices, intersectionPoints(P,s) is the subtype of points a of A "
                    + "such that a belongs to P(i) for every i in s. The empty intersection has all of A as its points. "
                    + "The object at s is the coproduct of one copy of R for each such point. "
                    + "For t contained in s, the map from the object at s to the object at t is induced by the actual inclusion "
                    + "of intersection points. It sends each point summand to the summand of the same point."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("ordered-free-complex"), DeclarationHandle.Create(Owner + "complex"),
                H("The ordered deletion differential"), StatementSource.FromAuthor(ComplexDefinition), Source,
                Blocks(Paragraph(Text("For every natural degree p, finsetsOfCard(iota,succ(p)) is the subtype of finite index sets "
                    + "with p+1 elements; intersectionFreeObjects(R,P) is the preceding functor evaluated at such a set. "
                    + "On the summand (s,a) in degree p+1 the differential is the sum over i in s of the summand "
                    + "(s without i,a), multiplied by (-1) to the number of j in s with j<i. "
                    + "This is the increasing-order finite-set deletion sign. The composite of consecutive differentials vanishes "
                    + "in every natural degree. Increasing enumerations identify successive deletions with the Fin simplicial "
                    + "identity, so the alternating double-sum cancellation applies to the actual intersection inclusions."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("actual-augmentation"), DeclarationHandle.Create(Owner + "augmentation"),
                H("The specified augmentation"), StatementSource.FromAuthor(AugmentationDefinition), Source,
                Blocks(Paragraph(Text("singleZero is the chain complex concentrated at zero with object coproduct(A,R). "
                    + "Here degreeZeroPointImage denotes composition with the two actual summand inclusions for a singleton s "
                    + "and a point a belonging to its intersection. The augmentation sends this summand to the a summand "
                    + "of coproduct(A,R). Its components in positive degrees are zero. The two faces of every degree-one "
                    + "summand have the same point image and opposite signs, so this is a chain map. "
                    + "Its definition uses the family P without requiring a cover equation or a contraction."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("chosen-vertex-chain-contraction"),
                DeclarationHandle.Create(Owner + "augmentation_homotopy_equiv"),
                H("A homotopy inverse for the same augmentation"), StatementSource.FromAuthor(Equivalence), Source,
                Blocks(Paragraph(Text("Assume that the union of P(i) over all iota is A. Choose for each point a an index c(a) "
                    + "with a in P(c(a)). The section sends a to the summand ({c(a)},a). In degree p the homotopy inserts c(a) "
                    + "into s with sign (-1) to the number of indices of s strictly less than c(a); it is zero if c(a) is already "
                    + "in s. These maps are defined by coproduct descent, without finite-support or finite-cover assumptions.")),
                    Paragraph(Text("Write composition in categorical order. The section followed by the augmentation is the identity. "
                        + "In degree zero, H(0) followed by d(0) is the identity minus augmentation followed by section. "
                        + "In degree p+1, d(p) followed by H(p), plus H(p+1) followed by d(p+1), is the identity. "
                        + "If c(a) is present, all cone-face terms vanish except deletion of c(a), whose total sign is +1. "
                        + "If c(a) is absent, deletion of the inserted vertex contributes (s,a), and all other terms cancel "
                        + "against the homotopy after deletion. At degree zero the remaining cone face is exactly the chosen section. "
                        + "The native chain-homotopy construction assembles these identities into E, whose forward map is exactly "
                        + "the independently defined augmentation.")),
                    Paragraph(Text("The result includes empty intersections, zero coefficient objects, infinite index and point types, "
                        + "and empty covers whenever their union is A. If iota is empty, the cover equation forces A to be empty. "
                        + "There is no topology, good-cover, abelian-category, module, field, extra-exactness or supplied-contraction "
                        + "hypothesis. This statement concerns the ordered free complex of a set cover; no singular-chain total-complex "
                        + "comparison is asserted."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("cover-preserving-chain-map"),
                DeclarationHandle.Create(Owner + "map"), H("Maps on the same intersection generators"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For point types A and B, families P and Q with the same ordered index type, "
                    + "and a function f from A to B taking P(i) into Q(i) for every i, there is a chain map from "
                    + "the ordered free complex of P to that of Q. It sends each generator (s,a) to (s,f(a)). "
                    + "The finite index set and every deletion sign are preserved. These maps preserve identity "
                    + "and composition."))), DescribeRole.Definition))));
}
