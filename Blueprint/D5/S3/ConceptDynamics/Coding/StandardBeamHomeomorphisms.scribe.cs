using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding;

internal sealed class StandardBeamHomeomorphismsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Coding/StandardBeamHomeomorphisms.";
    private static Formula I(string name) => F.Id(name);
    private static Formula.BoundVariable B(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);
    private static Formula Forall(Formula body, params Formula.BoundVariable[] variables) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
    private static Formula Exists(Formula body, params Formula.BoundVariable[] variables) =>
        new Formula.BindMany(FormulaQuantifier.Exists, [.. variables], body);
    private static Formula Apply(Formula f, params Formula[] arguments) =>
        new Formula.Apply(f, [.. arguments]);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Iff(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Member(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "All commuting history homeomorphisms and derived whole-ray geometry.",
        H("All commuting history homeomorphisms and derived whole-ray geometry"),
        Blocks(
            Paragraph(Text("Display conventions. Type ranges over the source universes; class-instance binders show the stated finite, decidable, algebraic and topological hypotheses. Essential G requires an actual incoming and outgoing edge at every vertex. History G is the subtype of all Int-indexed edge sequences satisfying target(x k)=source(x (k+1)); coordinate is subtype evaluation. Homeomorph, Equiv and MonoidHom display Lean homeomorphism, equivalence and multiplicative-hom types. IntModule is Module Int; IntEnd is Module.End Int; IntLinearMap and IntLinearEquiv are the corresponding Int-linear types. recordType and typeAlias label a structure or abbreviation, and hasType labels a definition's result type. image is whole Set.image; compose is LinearMap.comp; linearIdentity is LinearMap.id; endSum is linear-map addition. power is the source's natural power, rightMultiply is Matrix.vecMul, and intCast is the Nat-to-Int coercion. Other display aliases are expanded in their owning records; proof arguments are determined by the displayed telescope, not new hypotheses.")),
            Describe.Lean(DescribeId.Create("all-unit-shift-commuting-homeomorphisms"),
                DeclarationHandle.Create(Prefix + "fullAutSubgroup"),
                H("The full subgroup has no supplied window or beam-support field"),
                StatementSource.FromAuthor(Disp(
                    Forall(
                        Forall(
                            Iff(
                                Member(I("f"), Call("fullAutSubgroup", I("G"))),
                                Forall(
                                    Equal(
                                        Apply(I("f"), Call("shift", I("G"), I("x"))),
                                        Call("shift", I("G"), Apply(I("f"), I("x")))),
                                    B("x", Call("History", I("G"))))),
                            B("f", Call("Homeomorph", Call("History", I("G")), Call("History", I("G"))))),
                        B("V", I("Type")),
                        B("E", I("Type")),
                        B("G", Call("DirectedMultigraph", I("V"), I("E"))),
                        B("finiteV", Call("Fintype", I("V"))),
                        B("finiteE", Call("Fintype", I("E"))),
                        B("decV", Call("DecidableEq", I("V"))),
                        B("topV", Call("TopologicalSpace", I("V"))),
                        B("discreteV", Call("DiscreteTopology", I("V"))),
                        B("topE", Call("TopologicalSpace", I("E"))),
                        B("discreteE", Call("DiscreteTopology", I("E")))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("homeomorph(h) means h.val for a member of FullAut G, the subtype fullAutSubgroup G of History G homeomorphisms. Membership requires exactly f(shift x)=shift(f x) for all histories. Multiplication is (g*h)(x)=g(h(x)); inversion is the actual homeomorphism inverse. The finite vertex and edge types have their given discrete topologies. No endpoint preservation, action support, window, entropy, mixing or essentiality is part of this membership condition."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("compactness-derived-forward-inverse-windows"),
                DeclarationHandle.Create(Prefix + "fullAut_has_two_windows"),
                H("Compactness derives both windows for every full automorphism"),
                StatementSource.FromAuthor(Disp(
                    Forall(
                        Forall(
                            Exists(
                                And(
                                    Call("Controls", I("G"), Call("homeomorph", I("h")), I("a"), I("b")),
                                    Call(
                                        "Controls",
                                        I("G"),
                                        Call("symm", Call("homeomorph", I("h"))),
                                        I("c"),
                                        I("d"))),
                                B("a", I("Nat")),
                                B("b", I("Nat")),
                                B("c", I("Nat")),
                                B("d", I("Nat"))),
                            B("h", Call("FullAut", I("G")))),
                        B("V", I("Type")),
                        B("E", I("Type")),
                        B("G", Call("DirectedMultigraph", I("V"), I("E"))),
                        B("finiteV", Call("Fintype", I("V"))),
                        B("finiteE", Call("Fintype", I("E"))),
                        B("decV", Call("DecidableEq", I("V"))),
                        B("topV", Call("TopologicalSpace", I("V"))),
                        B("discreteV", Call("DiscreteTopology", I("V"))),
                        B("topE", Call("TopologicalSpace", I("E"))),
                        B("discreteE", Call("DiscreteTopology", I("E")))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Controls G f a b means forall x y : History G, forall k:Int, if forall t:Int with k-a<=t<=k+b the edges x t and y t agree, then (f x) k=(f y) k. All radii are natural, and the displayed inverse is h.val.symm. The legal history subspace is closed in a finite discrete product, hence compact. Continuity of the output at zero gives local finite-coordinate cylinders; a finite subcover gives uniform finite control. Commutation with all integer translates transfers this to every k. Apply the same argument to h inverse; locality is a consequence, not an assumed domain restriction."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("every-full-automorphism-whole-ray-image"),
                DeclarationHandle.Create(Prefix + "image_ray_atCut"),
                H("An image contains whole intrinsic rays at a controlled cut"),
                StatementSource.FromAuthor(Disp(
                    Forall(
                        Forall(
                            Call(
                                "AtCut",
                                I("G"),
                                Call(
                                    "image",
                                    Call("homeomorph", I("h")),
                                    Call("ray", I("G"), I("alpha"), I("n"))),
                                Call("laterCut", I("n"), I("d"))),
                            B("h", Call("FullAut", I("G"))),
                            B("a", I("Nat")),
                            B("b", I("Nat")),
                            B("c", I("Nat")),
                            B("d", I("Nat")),
                            B("hab", Call("Controls", I("G"), Call("homeomorph", I("h")), I("a"), I("b"))),
                            B(
                                "hcd",
                                Call(
                                    "Controls",
                                    I("G"),
                                    Call("symm", Call("homeomorph", I("h"))),
                                    I("c"),
                                    I("d"))),
                            B("alpha", Call("History", I("G"))),
                            B("n", I("Int"))),
                        B("V", I("Type")),
                        B("E", I("Type")),
                        B("G", Call("DirectedMultigraph", I("V"), I("E"))),
                        B("finiteV", Call("Fintype", I("V"))),
                        B("finiteE", Call("Fintype", I("E"))),
                        B("decV", Call("DecidableEq", I("V"))),
                        B("topV", Call("TopologicalSpace", I("V"))),
                        B("discreteV", Call("DiscreteTopology", I("V"))),
                        B("topE", Call("TopologicalSpace", I("E"))),
                        B("discreteE", Call("DiscreteTopology", I("E"))),
                        B("hG", Call("Essential", I("G")))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("image denotes the entire Set.image, not the images of selected representatives. laterCut(n,d)=n+(d:Int). The forward window places the image in ray G (h alpha) (n-b). The inverse window proves that every image point brings its whole (n+d)-ray, allowing every legal future. Finite numbered refinement between n-b and n+d bounds intrinsic pieces by Delta^(b+d). image_isBeam extends this to any finite intrinsic beam; the two displayed window hypotheses are derived for every h by fullAut_has_two_windows."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("conjugated-splice-whole-ray-image"),
                DeclarationHandle.Create(Prefix + "conjugateSplice_rayImage"),
                H("The conjugate maps an entire intrinsic ray onto the entire target ray"),
                StatementSource.FromAuthor(Disp(
                    Forall(
                        Forall(
                            Equal(
                                Call(
                                    "image",
                                    Call(
                                        "conjugateSplice",
                                        I("G"),
                                        I("h"),
                                        I("alpha"),
                                        I("beta"),
                                        I("n"),
                                        I("ep")),
                                    Call(
                                        "restrictedRay",
                                        I("G"),
                                        I("y"),
                                        Call("conjugateCut", I("n"), I("a"), I("b"), I("d")))),
                                Call(
                                    "restrictedRay",
                                    I("G"),
                                    Apply(
                                        Call(
                                            "conjugateSplice",
                                            I("G"),
                                            I("h"),
                                            I("alpha"),
                                            I("beta"),
                                            I("n"),
                                            I("ep")),
                                        I("y")),
                                    Call("conjugateCut", I("n"), I("a"), I("b"), I("d")))),
                            B("h", Call("FullAut", I("G"))),
                            B("a", I("Nat")),
                            B("b", I("Nat")),
                            B("c", I("Nat")),
                            B("d", I("Nat")),
                            B("hab", Call("Controls", I("G"), Call("homeomorph", I("h")), I("a"), I("b"))),
                            B(
                                "hcd",
                                Call(
                                    "Controls",
                                    I("G"),
                                    Call("symm", Call("homeomorph", I("h"))),
                                    I("c"),
                                    I("d"))),
                            B("alpha", Call("History", I("G"))),
                            B("beta", Call("History", I("G"))),
                            B("n", I("Int")),
                            B(
                                "ep",
                                Equal(
                                    Call("endpoint", I("G"), I("alpha"), I("n")),
                                    Call("endpoint", I("G"), I("beta"), I("n")))),
                            B(
                                "y",
                                Call(
                                    "image",
                                    Call("homeomorph", I("h")),
                                    Call("ray", I("G"), I("alpha"), I("n"))))),
                        B("V", I("Type")),
                        B("E", I("Type")),
                        B("G", Call("DirectedMultigraph", I("V"), I("E"))),
                        B("finiteV", Call("Fintype", I("V"))),
                        B("finiteE", Call("Fintype", I("E"))),
                        B("decV", Call("DecidableEq", I("V"))),
                        B("topV", Call("TopologicalSpace", I("V"))),
                        B("discreteV", Call("DiscreteTopology", I("V"))),
                        B("topE", Call("TopologicalSpace", I("E"))),
                        B("discreteE", Call("DiscreteTopology", I("E")))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("conjugateSplice is h composed with spliceEquiv(alpha,beta,n,ep) and h inverse, restricted to the two actual image subsets. conjugateCut(n,a,b,d)=n+a+b+d with integer casts. restrictedRay(y,ell) is {z in the appropriate image subtype | z.val belongs to ray G y.val ell}; on the right it is a subset of h image of beta's ray. The theorem is exact equality of these sets.")),
                    Paragraph(Text("The conjugate keeps every future edge k>n+a. The forward and inverse Controls force equal pasts through ell to map to equal pasts through ell. Conjugating the reverse splice proves reverse inclusion. At ell the next edge agrees, so legal seams DERIVE endpoint equality. conjugateSplice_on_ray identifies each restriction with the actual past splice. With Essential G, conjugatePartsEquiv and its endpoint theorem give the endpoint-preserving bijection needed for quotient compatibility."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("actual-unit-left-shift-whole-ray"),
                DeclarationHandle.Create(Prefix + "shift_ray"),
                H("The actual shift decreases every integer cut by one"),
                StatementSource.FromAuthor(Disp(
                    Forall(
                        Forall(
                            Equal(
                                Call("image", Call("shiftMap", I("G")), Call("ray", I("G"), I("alpha"), I("n"))),
                                Call(
                                    "ray",
                                    I("G"),
                                    Call("shift", I("G"), I("alpha")),
                                    Call("previousCut", I("n")))),
                            B("alpha", Call("History", I("G"))),
                            B("n", I("Int"))),
                        B("V", I("Type")),
                        B("E", I("Type")),
                        B("G", Call("DirectedMultigraph", I("V"), I("E"))),
                        B("finiteV", Call("Fintype", I("V"))),
                        B("finiteE", Call("Fintype", I("E"))),
                        B("decV", Call("DecidableEq", I("V"))),
                        B("topV", Call("TopologicalSpace", I("V"))),
                        B("discreteV", Call("DiscreteTopology", I("V"))),
                        B("topE", Call("TopologicalSpace", I("E"))),
                        B("discreteE", Call("DiscreteTopology", I("E")))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("shiftMap G is the function FiniteWindowTableCriterion.shift G, and shift G alpha evaluates alpha at k+1. previousCut(n)=n-1. The inverse reindexes at k-1, proving equality for the whole set. shift_ray_endpoint keeps G.target(alpha n) at the new cut. The statement covers cut zero and negative cuts."))),
                DescribeRole.Theorem))));
}
