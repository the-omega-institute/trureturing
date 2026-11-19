using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Circle.Orbit;

internal sealed class MersenneZeroSymmetriesDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Circle/Orbit/MersenneZeroSymmetries.";
    private static Formula V(string s) => F.Id(s);
    private static Formula Call(string s, params Formula[] a) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(s), [.. a]);
    private static Formula Eq(Formula x, Formula y) =>
        new Formula.Relation(x, FormulaRelationOperator.Equal, y);
    private static Formula IffOf(Formula x, Formula y) =>
        new Formula.Logic(x, FormulaLogicOperator.Iff, y);
    private static Formula Imp(Formula x, Formula y) =>
        new Formula.Logic(x, FormulaLogicOperator.Implies, y);
    private static Formula Q(Formula f, params (string Name, Formula Domain)[] vs)
    {
        for (var i = vs.Length - 1; i >= 0; --i)
            f = new Formula.Bind(FormulaQuantifier.ForAll,
                FormulaIdentifier.Create(vs[i].Name), vs[i].Domain, f);
        return f;
    }
    private static DocumentBlock.Describe Desc(string name, string title, Formula f,
        string text, DescribeRole role = DescribeRole.Definition) =>
        Describe.Lean(DescribeId.Create("mersenne-symmetry-" + name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title),
            StatementSource.FromAuthor(Disp(f)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(text))), role);

    public DocumentDefinition Create()
    {
        var n = V("n"); var a = V("a"); var i = V("i"); var j = V("j");
        var nat = new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
        var g = Call("gcd", n, a); var ell = Call("div", n, g);
        var labels = Call("Fin", n);
        var rho = new Formula.Power(Call("finRotate", n), a);
        var same = Call("SameCycle", rho, i, j);
        var chart = Call("residueChart", n, a);
        var positive = new Formula.Relation(new Formula.Number(0), FormulaRelationOperator.LessThan, n);
        Formula AllNA(Formula f) => Q(f, ("n", nat), ("a", nat));
        Formula AllLabels(Formula f) => AllNA(Imp(positive,
            Q(f, ("i", labels), ("j", labels))));
        var group = Call("ZeroFamilyAut", n, a);
        var coords = Call("Coordinates", Call("Fin", g), Call("Fin", ell));
        var order = new Formula.Binary(new Formula.Power(Call("factorial", ell), g),
            FormulaBinaryOperator.Multiply, Call("factorial", g));

        return DocumentDefinition.Create(ScribeNode.Create(
            "The full literal integer-zero-family symmetry group of a Mersenne-difference source has gcd residue blocks and natural-index semidirect coordinates.",
            H("Gcd orbit coordinates and Mersenne zero-family symmetries"), Blocks(
                Paragraph(Text("Fix n>0 and a any natural number. Keep every physical label in Fin(n), with its integer value SourceWidth.actualSource(n,2^a-1). A permutation belongs to ZeroFamilyAut(n,a) exactly when, for every finite physical subset A, the source sum on its image is zero if and only if the source sum on A is zero. Set g=gcd(n,a), ell=n/g and rho=(finRotate n)^a. The existing MersenneDifferenceZeroSubsets.actual_zero_iff_rotation identifies this literal zero condition with rho-invariance. Its subset-count theorem is reused as context, not reproved here.")),
                Desc("sameCycle_iff_residue", "Exact arithmetic orbit relation", AllLabels(IffOf(same,
                    Eq(Call("mod", Call("val", i), g), Call("mod", Call("val", j), g)))),
                    "Conjugation by ZMod.finEquiv sends rotation to translation by one, including modulus one. Integer powers translate by z*a. Divisibility by g proves necessity of residue equality. Conversely, g divides j-i; Int.gcd_a_modEq supplies a Bezout coefficient, and multiplication by the quotient constructs an integer z with i+z*a congruent to j modulo n. This constructs a SameCycle witness, rather than just comparing the numbers of orbits.", DescribeRole.Theorem),
                Desc("residueChart", "Residue and quotient coordinates", AllNA(
                    Call("Equiv", labels, Call("Product", Call("Fin", g), Call("Fin", ell)))),
                    "The chart is finProdFinEquiv inverse, after transporting ell*g=n, and then swapping factors. It sends a physical index i to (i mod g,i div g). The first coordinate labels its orbit; the second labels all ell elements of that orbit. The arithmetic identity follows from g dividing n; no additional division bijection is implemented."),
                Desc("sameCycle_iff_chart", "Orbit relation in the chart", AllLabels(IffOf(same,
                    Eq(Call("fst", Call("apply", chart, i)), Call("fst", Call("apply", chart, j))))),
                    "The first-coordinate equality is the exact residue theorem through the implemented equivalence. It is consumed by conjugation of the relation-automorphism subgroup.", DescribeRole.Theorem),
                Desc("ZeroFamilyAut", "Literal zero-family subgroup", AllNA(
                    Call("Subgroup", Call("Perm", labels))),
                    "Membership requires the zero-sum equivalence in both directions for every A. Composition follows by successive image actions; inverse closure uses the equivalence on the inverse image. This definition keeps the actual integer source, not a modular surrogate or a centralizer."),
                Desc("zeroFamilyAut_eq_orbitAut", "The zero family reconstructs the orbit partition", AllNA(Imp(positive,
                    Eq(group, Call("relationAut", Call("SameCycle", rho))))),
                    "For a finite permutation, invariant subsets have membership constant on SameCycle, by natural-power induction and inverse images. The class of q(x) is invariant. The reverse family implication makes its inverse image under q invariant; it contains x and therefore every y in x's orbit. This proves forward orbit preservation by q. Repeating the argument with q inverse proves reflection. Conversely, preserving and reflecting SameCycle transports every saturated subset. This private consumed reconstruction bridge does not duplicate the general function-algebra antiequivalence.", DescribeRole.Theorem),
                Desc("zeroFamilyEquiv", "Complete semidirect classification", AllNA(Imp(positive,
                    Call("MulEquiv", group, coords))),
                    "Conjugating physical permutations by residueChart carries ZeroFamilyAut onto UniformPartitionAutomorphisms.Aut(Fin(g),Fin(ell)). The existing automorphismEquiv then supplies all coordinates and their uniqueness. The coordinates are (sigma,alpha), with alpha permuting the g blocks and sigma(w) permuting Fin(ell) at destination w. Multiplication is (sigma,alpha)(tau,beta)=(eta,alpha beta), where eta(w)=sigma(w)*tau(alpha inverse(w)). The action on a chart label (v,t) is (alpha(v),sigma(alpha(v))(t)). Only the natural set of g block indices is used; a regular wreath product on all elements of Sym(g) has the wrong index set."),
                Desc("card_zeroFamilyAut", "Exact factorial order", AllNA(Imp(positive, Eq(Call("card", group), order))),
                    "The group isomorphism followed by the inverse generic automorphismEquiv transports the actual group to the uniform-partition automorphism group. Its existing card_aut yields (ell!)^g*g!. Positivity of n implies g>0 and ell>0, so its nonempty-fiber hypothesis is proved internally.", DescribeRole.Theorem),
                Paragraph(Text("All exponents remain in scope. When n divides a, including a=0, g=n and ell=1: the source is zero and the group is Sym(n). When gcd(n,a)=1 there is one orbit and again the whole Sym(n), since the zero family then consists of the empty and full subsets. For n=1 the group is trivial. No cyclic ordering inside a block is retained by the zero family; its group can exceed the rotation centralizer. These are mathematical consequences for this exact source family, not claims about arbitrary sources, the full Circle problem, or literature novelty."))
            ), []));
    }
}
