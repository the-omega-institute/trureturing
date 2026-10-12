using F = StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.FormulaDsl;
using static StrataLint.Scribe.DefinitionDsl;
namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.Observer;
internal sealed class NativePrefixIdentityReflectionDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "NativePrefixIdentityReflection", H("Native prefix identity reflection"), Blocks(
            Supplier("gamma_iterate", "Native mass is invariant under every iterate", "The mass counts non-atomic constructors. Iterating the interpreted native substitution preserves it, including zero-mass atoms of unbounded rank."),
            Supplier("gamma_pair", "A positive child prevents atomic collapse", "If either child has positive native mass, the parent has one plus the two child masses. No unrestricted additivity is asserted for pairs of atomic children."),
            Supplier("gamma_parent", "Native mass does not decrease toward the root", "Each child mass is at most the parent mass, including pairs whose two children have zero mass."),
            Supplier("kappa_iterate", "The native clock advances by the iterate exponent", "The clock is zero at alpha, one at beta and two plus the right child clock at a pair. Each native substitution advances it by one."),
            Supplier("gamma_comb", "Existing finite combs realize every mass", "The comb starts at alpha and repeatedly pairs the preceding comb with alpha on the right. Its native constructor mass is exactly the number of pair steps."),
            Supplier("eval_closed", "Closed expressions ignore residual valuations", "An expression whose active flag is false has no live residual occurrence. Its evaluated native tree is the same under every two source valuations, without imposing any bound on ground size."),
            Describe.Lean(
                DescribeId.Create("native-prefix-identity-reflection"),
                DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Observer/NativePrefixIdentityReflection.prefix_identity_reflection"),
                H("Equality on a live prefix cylinder reflects globally"),
                Statement(), AssessedProvenance.FromRepo(), Blocks(
                    Paragraph(Text("The native source algebra consists of all nonempty finite ordered binary trees with leaf labels alpha and beta. Native substitution sends alpha to beta, beta to the ordered pair (beta, alpha), and distributes through pairs. It is a fixed interpreted operation; its powers are not extra free constructors.")),
                    Paragraph(Text("A mixed expression contains finite ground trees, a fixed nonnegative substitution power of an original residual name, and ordered pairing. The same name always denotes the same whole source valuation, including when its occurrences carry different fixed powers. Fixed scalar atoms and fixed barrier coordinates are evaluated into grounds before the implication is applied.")),
                    Paragraph(Text("Each original coordinate has its own finite depth and pattern. A zero-depth pattern is one hole. An early observed leaf remains that leaf and contributes no descendant holes; an observed pair retains two ordered child patterns. Frontier names therefore describe exactly the reached positions, with distinct coordinates carrying disjoint private families. Every hole may receive any finite native source, independently of every other hole.")),
                    Paragraph(Text("NativeDepthPatterns.depthEquiv reconstructs every finite source from its pattern and reached subtrees. NativeDepthPatterns.frontier_geometry identifies exactly the reached depth positions and recovers every assigned subtree. Relating the supplied patterns to prescribed inclusive prefixes of actual infinite completion trees requires a separate completion-tree correspondence. Inclusive observation through depth h calls for a pattern at depth h+1. The finite-tree decomposition by itself does not provide that correspondence. Early leaves preserve their absent descendants, so the reconstruction does not replace absent regions with variables.")),
                    Paragraph(Text("The implication fixes all patterns and both expressions first. Its premise quantifies over the entire joint dependent product of hole fillings. Its conclusion quantifies over the entire original finite residual product. There is no feasibility assumption, chosen solution, source-size bound, common mass, common clock, or positive restriction on the concluding valuations. Zero residual dimension is included and reduces the comparison to fixed grounds.")),
                    Paragraph(Text("The proof recognizes the native Fibonacci atomic subtrees by a recursive optional rank. Their constructor mass is zero; an unrecognized pair has mass one plus its child masses. A pair of recognized consecutive atoms can collapse to a single higher atom, so unrestricted constructor additivity would be false. Substitution shifts the recognized rank by one and preserves this mass. Whenever a child has positive mass, atomic collapse is excluded and pair mass is exactly additive. Finite left combs realize every nonnegative mass.")),
                    Paragraph(Text("For positive hole masses, a context has an exact constant offset plus the sum of its hole masses. The offset includes the masses of maximal closed subtrees and every pair ancestor of a hole. Closed child contexts can collapse atomically; live child contexts have a positive descendant and make their ancestors additive. The induction includes pairs with one empty child frontier and patterns with no frontier.")),
                    Paragraph(Text("An expression has an exact ground-and-constructor offset plus its residual occurrence counts times the context masses. Counts retain repetitions and ignore only the fixed decorations, whose mass is invariant. Testing mass one at all holes and then increasing one selected named hole to mass two isolates that original coordinate's coefficient. Thus a cylinder equality forces equal occurrence counts and equal offsets. A residual-containing pair has strictly positive offset and cannot equal a single decorated residual on the entire cylinder.")),
                    Paragraph(Text("For two decorated occurrences of the same original name, the native right-spine clock is zero on alpha, one on beta, and two plus the right child clock on a pair. Substitution increases it by one, so equality forces equal fixed exponents by natural-number cancellation. Different names have different independent mass coefficients. Ordered-pair injection gives the two child cylinder equalities, and structural induction reflects both child identities. Residual-free expressions are independent of the valuation, including ground-versus-pair comparisons.")),
                    Paragraph(Text("This is the identity-reflection clause used in Signed Local Prefix Lifting, Lemma 2.1, displayed SLP.11, and Functional Joint Contact, Theorem 4.2. By contraposition, a global nonidentity remains a nonidentity after independent live-prefix substitution. Producing one filling that breaks a whole finite list of equalities simultaneously additionally requires the distinct uniform residual separation theorem: separate witnesses for separate negatives do not supply a common witness.")),
                    Paragraph(Text("A coordinate with no reached frontier can be fixed by its isolating leaf prefix, and is outside the live hypothesis. Coupling two original coordinates by requiring their hole values to agree is outside the independent product premise. Neither boundary is repaired by giving repeated occurrences fresh names.")),
                    Paragraph(Text("These are mathematical coordinates and exact whole-tree equalities. Applying the result to an acquired register still requires the common source-total producer, authentic epoch, complete accessible retained-state cut and full signed source fiber. It supplies no source-selection or subtree-equality port. Acquisition, four-valued arbitrary-word reads, legal serial forward updates, literal lengths, local work, memory, retention, preparation, installation and physical time remain separately paid resources. No approximation, probability guarantee or physical cost optimum follows from the implication."))
                ), DescribeRole.Theorem)
        )));

    private static DocumentBlock Supplier(string n, string title, string prose) => Describe.Lean(
        DescribeId.Create("native-prefix-supplier-" + n.Replace("_", "-")),
        DeclarationHandle.Create("D5/S3/Arith/FibonacciAtomic/Observer/NativePrefixIdentityReflection." + n),
        H(title), SupplierStatement(n), AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);
    private static StatementSource SupplierStatement(string n)
    {
        var source = V("Source");
        var gs = Call("gamma",V("s"));
        var gt = Call("gamma",V("t"));
        var gp = Call("gamma",Call("mul",V("s"),V("t")));
        Formula formula = n switch
        {
            "gamma_iterate" => All("a",V("Nat"),All("t",source,
                EqOf(Call("gamma",Call("iterate",V("substitution"),V("a"),V("t"))),Call("gamma",V("t"))))),
            "gamma_pair" => All("s,t",source,Imp(Seq(Par(Seq(D(0),Sp,Lt,Sp,gs)),Sp,Lor,Sp,Par(Seq(D(0),Sp,Lt,Sp,gt))),
                EqOf(gp,Seq(D(1),Sp,Plus,Sp,gs,Sp,Plus,Sp,gt)))),
            "gamma_parent" => All("s,t",source,Seq(Par(Seq(gs,Sp,Leq,Sp,gp)),Sp,Land,Sp,Par(Seq(gt,Sp,Leq,Sp,gp)))),
            "kappa_iterate" => All("a",V("Nat"),All("t",source,
                EqOf(Call("kappa",Call("iterate",V("substitution"),V("a"),V("t"))),Seq(Call("kappa",V("t")),Sp,Plus,Sp,V("a"))))),
            "gamma_comb" => All("r",V("Nat"),EqOf(Call("gamma",Call("comb",V("r"))),V("r"))),
            "eval_closed" => All("I",V("Type"),All("E",Call("MixedExpr",V("I")),
                Imp(EqOf(Call("active",V("E")),Call("false")),All("z,v",Arr(V("I"),source),
                    EqOf(Call("eval",V("z"),V("E")),Call("eval",V("v"),V("E"))))))),
            _ => throw new ArgumentException(n)
        };
        return StatementSource.FromAuthor(Disp(formula));
    }

    private static StatementSource Statement()
    {
        var coordinate = Call("Fin", V("m"));
        var source = V("Source");
        var patterns = Dep("i", coordinate, Call("Pattern", Call("d", V("i"))));
        var frontier = Call("Frontier", Call("p", V("i")));
        var fillings = Dep("i", coordinate, Arr(frontier, source));
        var cylinder = Seq(LambdaLower, Sp, Par(Seq(V("i"), Colon, Sp, coordinate)),
            Comma, Sp, Call("fill", Call("p", V("i")), Call("w", V("i"))));
        var live = All("i", coordinate, Call("Nonempty", frontier));
        var onCylinder = All("w", fillings,
            EqOf(Call("eval", Par(cylinder), V("A")), Call("eval", Par(cylinder), V("B"))));
        var global = All("z", Arr(coordinate, source),
            EqOf(Call("eval", V("z"), V("A")), Call("eval", V("z"), V("B"))));
        return StatementSource.FromAuthor(Disp(
            All("m", V("Nat"),
                All("d", Arr(coordinate, V("Nat")),
                    All("p", patterns,
                        Imp(live,
                            All("A,B", Call("MixedExpr", coordinate),
                                Imp(onCylinder, global))))))));
    }

    private static Formula V(string n) => F.Id(n);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Call(string n, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(n))), [.. args]);
    private static Formula EqOf(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));
    private static Formula Arr(Formula a, Formula b) => Seq(a, Sp, To, Sp, b);
    private static Formula Dep(string n, Formula t, Formula b) =>
        Arr(Par(Seq(V(n), Colon, Sp, t)), b);
    private static Formula All(string ns, Formula t, Formula b) => Seq(Forall, Sp,
        Seq(ns.Split(',').Select((n, i) => i == 0 ? V(n) : Seq(Comma, Sp, V(n))).ToArray()),
        Colon, Sp, t, Comma, Sp, Par(b));
}
