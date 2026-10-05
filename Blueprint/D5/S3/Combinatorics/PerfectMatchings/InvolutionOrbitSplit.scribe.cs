using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.PerfectMatchings;

internal sealed class InvolutionOrbitSplitDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/PerfectMatchings/InvolutionOrbitSplit.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two fixed-point-free involutions split every matching component into two integer-power orbits of their product.",
        H("Product Orbits of Two Perfect Matchings"),
        Blocks(
            Paragraph(Text(
                "Let s and t be involutions of any type, and let r = s * t, with t applied first. "
                + "Connectivity means a finite path of s-edges and t-edges. Rotation orbits use all integer powers "
                + "of r and include singleton orbits. No finiteness or freeness of the rotation action is assumed. "
                + "In the formulas Component(s,t,x) is the set of y connected to x; OrbitClasses(r,C) "
                + "is the set of RotationOrbit(r,y) for y in C; PairSet(A,B) is {A,B}.")),
            Describe.Lean(DescribeId.Create("reflection-exclusion"),
                DeclarationHandle.Create(Prefix + "fixedPointFree_iff_reflection_exclusion"),
                H("Excluding Reflection Stabilizers"), StatementSource.FromAuthor(ReflectionFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Both generators have no fixed points exactly when every r^k s has no fixed points. "
                    + "For even k = 2j the reflection is conjugate to s by r^j; for odd k = 2j + 1 it is "
                    + "conjugate to t by r^(j+1). This covers negative exponents as well."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("rotation-separation"),
                DeclarationHandle.Create(Prefix + "fixedPointFree_iff_rotation_separation"),
                H("The Matching Edge Separates Product Orbits"), StatementSource.FromAuthor(SeparationFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Both generators have no fixed points exactly when s(x) lies outside the r-orbit of x "
                    + "for every x. An intersection would give a reflection fixing x. Conversely, an s-fixed "
                    + "point violates separation at exponent zero, and a t-fixed point violates it at exponent one."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("alternating-reachability"),
                DeclarationHandle.Create(Prefix + "connected_iff_rotation_orbits"),
                H("Exact Alternating Reachability"), StatementSource.FromAuthor(ReachabilityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For arbitrary involutions, y is connected to x exactly when it lies in the r-orbit of x "
                    + "or in the r-orbit of s(x). Path induction gives the forward implication; positive and "
                    + "negative product powers give actual paths for the reverse implication. The two candidates "
                    + "may coincide when a generator has a fixed point."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("component-split"),
                DeclarationHandle.Create(Prefix + "component_split"),
                H("Disjoint Components and Matching Exchange"), StatementSource.FromAuthor(SplitFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "When both involutions have no fixed points, the two product orbits are nonempty and disjoint, "
                    + "and their union is precisely the matching component of x. The images of the first orbit under "
                    + "either s or t equal the second orbit; involutivity also exchanges them in the reverse direction."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("exactly-two-orbit-classes"),
                DeclarationHandle.Create(Prefix + "component_orbit_classes"),
                H("Exactly Two Product Orbit Classes"), StatementSource.FromAuthor(ClassesFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The set of all product orbits represented inside one matching component is precisely the pair "
                    + "of distinct orbits represented by x and s(x). If s = t, the product is the identity and each "
                    + "matching component still has two distinct singleton product orbits."))), DescribeRole.Theorem))));

    private static Formula All(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);
    private static Formula And(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Or(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Or, b);
    private static Formula Iff(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Iff, b);
    private static Formula Imp(Formula a, Formula b) =>
        new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula App(Formula f, Formula x) => new Formula.Apply(f, [x]);
    private static Formula Pow(Formula r, Formula k) => new Formula.Power(r, k);
    private static Formula X() => F.Id("X");
    private static Formula S() => F.Id("s");
    private static Formula T() => F.Id("t");
    private static Formula R() => Multiply(S(), T());
    private static Formula Inv(Formula f) => All("z", X(),
        Equal(App(f, App(f, F.Id("z"))), F.Id("z")));
    private static Formula Free(Formula f) => All("z", X(),
        NotEqual(App(f, F.Id("z")), F.Id("z")));
    private static Formula Orbit(Formula x) => Call("RotationOrbit", R(), x);
    private static Formula C(Formula x) => Call("Component", S(), T(), x);
    private static Formula Same(Formula x, Formula y) => Call("SameCycle", R(), x, y);
    private static Formula Header(Formula body, bool free = false) =>
        Disp(All("X", F.Id("Type"), All("s", Call("Perm", X()),
            All("t", Call("Perm", X()), Imp(And(Inv(S()), Inv(T())),
                free ? Imp(And(Free(S()), Free(T())), body) : body)))));

    private static Formula ReflectionFormula() => Header(Iff(And(Free(S()), Free(T())),
        All("k", F.Id("Int"), All("x", X(), NotEqual(
            App(Multiply(Pow(R(), F.Id("k")), S()), F.Id("x")), F.Id("x"))))));

    private static Formula SeparationFormula() => Header(Iff(And(Free(S()), Free(T())),
        All("x", X(), new Formula.Not(Same(F.Id("x"), App(S(), F.Id("x")))))));

    private static Formula ReachabilityFormula() => Header(All("x", X(), All("y", X(),
        Iff(Call("Connected", S(), T(), F.Id("x"), F.Id("y")),
            Or(Same(F.Id("x"), F.Id("y")), Same(App(S(), F.Id("x")), F.Id("y")))))));

    private static Formula SplitFormula()
    {
        var x = F.Id("x"); var a = Orbit(x); var b = Orbit(App(S(), x));
        return Header(All("x", X(),
            And(Call("Disjoint", a, b), And(Call("Nonempty", a),
                And(Call("Nonempty", b), And(Equal(C(x), Call("Union", a, b)),
                    And(Equal(Call("Image", S(), a), b), Equal(Call("Image", T(), a), b))))))), true);
    }

    private static Formula ClassesFormula()
    {
        var x = F.Id("x"); var a = Orbit(x); var b = Orbit(App(S(), x));
        return Header(All("x", X(),
            And(Equal(Call("OrbitClasses", R(), C(x)), Call("PairSet", a, b)),
                NotEqual(a, b))), true);
    }

}
