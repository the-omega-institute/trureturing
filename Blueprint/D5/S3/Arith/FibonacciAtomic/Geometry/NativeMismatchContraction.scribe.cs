using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Geometry;

internal sealed class NativeMismatchContractionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Geometry/NativeMismatchContraction.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Two native substitution steps contract the discounted first-disagreement mass of every finite source pair.",
        H("Native First-Disagreement Contraction"), Blocks(
            Describe.Lean(DescribeId.Create("nativemismatchcontraction-mass"),
                DeclarationHandle.Create(Prefix + "mass"), H("Discounted Frontier Mass"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("Source is the existing free magma on Bool: true is alpha, false is beta, and multiplication is the ordered binary branch. The substitution rho sends alpha to beta, beta to the branch (beta,alpha), and acts on both children of a branch.")),
                    Paragraph(Text("For a rational q and source trees s,t, mass(q,s,t) is the finite sum of q to the length of p over p in frontier(s,t). This is the existing binary first-disagreement frontier, with false denoting the left direction and true the right. Equal subtrees contribute nothing; different root replies contribute the empty address; a common branch prefixes the two child frontiers. Matching terminated leaves are deleted.")),
                    Paragraph(Text("Write E(s)=rho squared applied to s. E(alpha)=(beta,alpha), E(beta)=((beta,alpha),beta), and E(s,u)=(E(s),E(u)). Thus every E-image has a branch at its root.")),
                    Paragraph(Text("For rational discounts, the canonical ordered-field embedding into the reals preserves this finite sum, its powers, products and inequalities. The rational mass therefore represents the same binary real-valued discounted frontier quantity at rational q. No statement about a tuple of more than two sources is asserted."))), DescribeRole.Definition),
            Result("root_cases", "Complete Root Cases", RootFormula(),
                "The four conjuncts include equal sources, both orders of distinct leaves, both orders of a leaf against any branch, and arbitrary pairs of branches. The endpoint q=1/2 is included.",
                "Induction on a source, with the other source arbitrary, bounds every child-pair mass by one: a root disagreement has mass one, equality has mass zero, and a common branch has mass at most q times (1+1). Every transformed root branches, so its two child masses give the mixed-root bound. The distinct-leaf frontier consists precisely of the one-letter left and right addresses."),
            Result("two_step_contraction", "Two-Step Native Contraction", ContractionFormula(),
                "For every finite nonempty native source pair and every rational 0<q<=1/2, applying rho twice reduces the mass by a factor at most 2q. For 0<q<1/2 this factor is strictly below one; at the endpoint the estimate is nonexpansive.",
                "Structural induction handles both trees without a height bound. At distinct leaves or a mixed root, the original mass is one and the complete root cases apply. At common branches, multiply the sum of the two child induction estimates by q and use the original and transformed branch recursions. Equal inputs have mass zero on both sides."),
            Result("even_iterates", "All Even Iterates", IterateFormula(),
                "The estimate holds for all natural n, including zero, and for equal as well as unequal inputs. It retains the same original finite sources throughout.",
                "The zero-step estimate is equality. For a successor, apply the two-step estimate to the two actual images at time 2n, then multiply the induction estimate by the nonnegative factor 2q. Iteration addition and the power identity yield the factor (2q) to the power n+1."))));

    private static DocumentBlock Result(string name, string title, Formula formula, string statement, string proof) =>
        Describe.Lean(DescribeId.Create("nativemismatchcontraction-" + name.Replace("_", "")),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(statement)), Paragraph(Text(proof))), DescribeRole.Theorem);

    private static Formula V(string s) => F.Id(s);
    private static Formula Par(Formula x) => Seq(Open, x, Close);
    private static Formula Call(string s, params Formula[] xs) => new Formula.Apply(Seq(Operatorname, Grp(V(s))), [.. xs]);
    private static Formula All(string s, Formula t, Formula x) => Seq(Forall, Sp, V(s), Colon, Sp, t, Comma, Sp, Par(x));
    private static Formula Eq(Formula x, Formula y) => Seq(x, Sp, F.Eq, Sp, y);
    private static Formula Le(Formula x, Formula y) => Seq(x, Sp, Leq, Sp, y);
    private static Formula Lt(Formula x, Formula y) => Seq(x, Sp, F.Lt, Sp, y);
    private static Formula Ne(Formula x, Formula y) => Seq(x, Sp, Neq, Sp, y);
    private static Formula Imp(Formula x, Formula y) => Seq(Par(x), Sp, Rightarrow, Sp, Par(y));
    private static Formula And(Formula x, Formula y) => Seq(Par(x), Sp, Land, Sp, Par(y));
    private static Formula Add(Formula x, Formula y) => Seq(Par(x), Sp, Plus, Sp, Par(y));
    private static Formula Mul(Formula x, Formula y) => Seq(Par(x), Sp, Cdot, Sp, Par(y));
    private static Formula Pow(Formula x, Formula y) => Seq(Par(x), Caret, Grp(y));
    private static Formula Source => Call("Source");
    private static Formula RatType => Seq(Mathbb, Grp(V("Q")));
    private static Formula NatType => Seq(Mathbb, Grp(V("N")));
    private static Formula M(Formula q, Formula s, Formula t) => Call("mass", q, s, t);
    private static Formula E(Formula s) => Call("E", s);
    private static Formula Leaf(Formula b) => Call("of", b);
    private static Formula Branch(Formula s, Formula t) => Call("mul", s, t);
    private static Formula Bounds(string[] names, Formula[] types, Formula body)
    {
        for (int i = names.Length - 1; i >= 0; --i) body = All(names[i], types[i], body);
        return body;
    }
    private static Formula Discount(Formula q, Formula body) =>
        All("q", RatType, Imp(Lt(D(0), q), Imp(Le(q, Seq(Frac, Grp(D(1)), Grp(D(2)))), body)));
    private static Formula RootFormula()
    {
        Formula q = V("q"), s = V("s"), t = V("t"), u = V("u"), v = V("v"), b = V("b"), c = V("c");
        Formula equal = Bounds(["s", "t"], [Source, Source], Imp(Eq(s, t), Eq(M(q, E(s), E(t)), D(0))));
        Formula leaves = Bounds(["b", "c"], [Call("Bool"), Call("Bool")],
            Imp(Ne(b, c), Eq(M(q, E(Leaf(b)), E(Leaf(c))), Mul(D(2), q))));
        Formula mixed = Bounds(["b", "u", "v"], [Call("Bool"), Source, Source],
            And(Le(M(q, E(Leaf(b)), E(Branch(u, v))), Mul(D(2), q)),
                Le(M(q, E(Branch(u, v)), E(Leaf(b))), Mul(D(2), q))));
        Formula branches = Bounds(["s", "u", "t", "v"], [Source, Source, Source, Source],
            Eq(M(q, E(Branch(s, u)), E(Branch(t, v))),
                Mul(q, Add(M(q, E(s), E(t)), M(q, E(u), E(v))))));
        return Discount(q, And(equal, And(leaves, And(mixed, branches))));
    }
    private static Formula ContractionFormula()
    {
        Formula q = V("q"), s = V("s"), t = V("t");
        return Discount(q, Bounds(["s", "t"], [Source, Source],
            Le(M(q, E(s), E(t)), Mul(Mul(D(2), q), M(q, s, t)))));
    }
    private static Formula IterateFormula()
    {
        Formula q = V("q"), n = V("n"), s = V("s"), t = V("t");
        Formula steps = Mul(D(2), n);
        return Discount(q, Bounds(["n", "s", "t"], [NatType, Source, Source],
            Le(M(q, Call("iterate", Call("rho"), steps, s), Call("iterate", Call("rho"), steps, t)),
                Mul(Pow(Mul(D(2), q), n), M(q, s, t)))));
    }
}
