using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Geometry;

internal sealed class TrueJumpEndpointsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/Geometry/TrueJumpEndpoints.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The actual finite true-jump endpoint family determines exactly the truncated ancestral colours.",
        H("Finite True-Jump Endpoint Classification"), Blocks(
            Def("Address", "The infinite ordered address tree",
                "Addresses are all finite Boolean lists, using the existing literal address convention: false is L and true is R. The empty list is the root; appending a letter forms a child. There is no finite domain, killing, or restriction on subsequent addresses."),
            Def("childIncrement", "The incoming-increment table",
                "Increment has values zero, plus and minus, representing integers 0, 1 and -1. From zero the ordered children have increments plus and minus; from plus they have zero and plus; from minus they have minus and zero. This is exactly Continuation V, Definition 120.3, equation (120.12)."),
            Def("code", "Literal colour recursion",
                "Starting at colour zero and increment zero, fold update along the address in its given order. Each update first selects the child's increment from the table, then adds that integer modulo m to the current colour. The projections q and delta retain the colour and the incoming increment. The source is fixed independently of observations and jump budgets."),
            Def("ancestor", "Ancestors and the root boundary",
                "The kth ancestor is the prefix of length depth minus k, using truncated natural subtraction. Parent removes one final letter. Totalization beyond the root serves only intermediate formulas; no extra ancestor enters a signature."),
            Def("observation", "The exact observation",
                "The observation is the pair of cycle colour and natural depth. Thus every actual seam changes observed depth, even when it preserves colour."),
            Def("signature", "The finite signature",
                "The signature consists of depth and the list of ancestor colours with indices zero through min(h,depth), inclusive. At budget zero it retains the current colour and depth. At the root its list contains just the root colour, for every budget."),
            Def("J", "The actual neighbor kernel",
                "At the root, J samples its two literal children uniformly. At every nonroot address, J samples parent, left child and right child uniformly. These probabilities are one half and one third respectively. The kernel has no dependence on colour or budget and has no hold at the root."),
            Def("law", "The finite actual-step law",
                "The zero-step law is the point mass at the starting address. The successor law samples J at that address and then continues with the remaining finite-step law from the selected neighbor. Root returns and later departures use J at the visited address, so they retain the degree-two rule."),
            Def("Seed", "An explicit finite experiment",
                "A seed for h jumps is h independent choices from six equiprobable outcomes. In move, a root sends three outcomes to each child; a nonroot sends two outcomes to each of its three neighbors. The recursive run uses one choice and continues from the actual selected address. Equality of the uniform seed pushforward with law is proved by the exact one-step distribution identity and the product law of independent uniform choices."),
            Def("B", "Endpoint expectations",
                "B is the real integral of f composed with observation against the actual j-step address law. The finite experiment gives the same integral, and its finite sum equals the backward evaluator. This correspondence is proved for every real function; only globally bounded functions occur in the classification statement."),
            Def("Bounded", "Global test functions",
                "Bounded means that one real constant bounds the absolute value at every point of ZMod m times the natural numbers. In particular every cell indicator is an admissible test; the tests are not limited to a finite observation subset."),
            Describe.Lean(DescribeId.Create("true-jump-endpoints-classification"),
                DeclarationHandle.Create(Prefix + "bounded_endpoints_iff_signature"),
                H("All bounded endpoint tests classify the signature"),
                StatementSource.FromAuthor(ResultFormula()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every natural modulus m at least three, every natural budget h and every two literal finite addresses p and t, signature equality is equivalent to equality of B for every j from zero through h and every globally bounded real test. The family includes its initial endpoint and every intermediate endpoint.")),
                    Paragraph(Text("For the forward direction, equal current and parent colours determine the same incoming increment: the integers 0, 1 and -1 have distinct residues for all permitted moduli, including three. Applying the literal table then matches each child, while the ancestor lists match the parent move. Each matched move preserves the signature with one less unit of budget. Induction in the actual finite experiment gives equal endpoint observations, with identical degree-dependent probabilities even on routes that revisit the root.")),
                    Paragraph(Text("For the converse, the zero-step cell indicators recover the initial colour and depth n. For every k at most n, an endpoint at depth n-k after exactly k jumps requires decreasing depth at every step. Induction on k excludes both child branches and identifies the unique all-parent route. Its cell expectation is (1/3)^k at its ancestor colour and zero at every other colour. Every departure on that route is nonroot, including the case k=n. Positivity therefore recovers every colour with k at most min(h,n).")),
                    Paragraph(Text("The result formalizes Theorem 2.2 of FIB-ATOM boundary geometry: finite joint cycle and radial prediction, using its fixed infinite carrier and the recursion of Continuation V, Definition 120.3. It concerns separate true-jump endpoint expectations. It asserts no continuous-time or frozen-path law, total-variation estimate, whole-future observation, acquisition procedure, or physical conclusion."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Def(string name, string title, string prose) => Describe.Lean(
        DescribeId.Create("true-jump-endpoints-" + name.ToLowerInvariant()), DeclarationHandle.Create(Prefix + name),
        H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
        Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula V(string name) => F.Id(name);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Call(string name, params Formula[] args) =>
        args.Length == 0 ? Seq(Operatorname, Grp(V(name))) :
            new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, V(name), Colon, Sp, type, Comma, Sp, Par(body));
    private static Formula EqOf(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));
    private static Formula ResultFormula()
    {
        Formula m = V("m"), h = V("h"), p = V("p"), t = V("t"), j = V("j"), f = V("f");
        Formula nat = Call("Nat"), address = Call("Address");
        Formula tests = All("j", nat, Imp(Seq(j, Sp, Le, Sp, h),
            All("f", Seq(Par(Seq(Call("ZMod", m), Sp, Times, Sp, nat)), Sp, To, Sp, Call("Real")),
                Imp(Call("Bounded", f), EqOf(Call("B", m, p, j, f), Call("B", m, t, j, f))))));
        Formula result = Seq(EqOf(Call("signature", m, h, p), Call("signature", m, h, t)), Sp, Iff, Sp, Par(tests));
        return Disp(All("m", nat, Imp(Seq(D(3), Sp, Le, Sp, m),
            All("h", nat, All("p", address, All("t", address, result))))));
    }
}
