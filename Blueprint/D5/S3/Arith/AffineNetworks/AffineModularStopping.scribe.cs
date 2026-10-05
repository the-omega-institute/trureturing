using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.AffineNetworks;

internal sealed class AffineModularStoppingDocument : IScribeDocumentDefinition
{
    private const string Gid = "D5/S3/Arith/AffineNetworks/AffineModularStopping.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The independent all-path affine modulus and exact named-edge stopping theorem.",
        H("Affine modular stopping theorem 11.3"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("actual-cycle-erasure"),
                DeclarationHandle.Create(Gid + "actual_cycle_erasure"),
                H("Endpoint-preserving named-edge cycle erasure"),
                StatementSource.FromAuthor(ErasureFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Every actual directed path has a simple actual path with the same endpoints. " +
                        "Its named-edge word is an occurrence sublist of the original word, its original " +
                        "multiplier product divides the original product, and its length is at most |V|−1. " +
                        "For every prime coordinate, erasure cannot increase the sum of edge losses, " +
                        "including the infinite loss of a zero multiplier.")),
                    Paragraph(Text(
                        "The construction erases the prefix recursively. If the last edge ends at a " +
                        "vertex already in the erased prefix, it retains the actual prefix ending at that " +
                        "vertex. Otherwise it appends the same original named edge. Vertex-list uniqueness " +
                        "gives the cardinality bound; the surviving edge occurrences give product divisibility."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("affine-modular-stopping"),
                DeclarationHandle.Create(Gid + "theorem11_3"),
                H("All-path prime-loss maximum and original gcd/lcm recurrence"),
                StatementSource.FromAuthor(MainFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let m be any positive integer, including 1. The nonempty finite vertex type and " +
                        "finite named-edge type retain loops and parallel edges. Each vertex source is the " +
                        "full ZMod m, with the reduction port modulo a positive divisor d_v of m. Every edge " +
                        "is legal on every phase and carries its original arbitrary natural multiplier a_e, " +
                        "including zero, and its affine offset c_e in ZMod m. A path transports the same " +
                        "phase through the original edge word; its multiplier A_γ is the product of those " +
                        "edge occurrences, with A_empty=1.")),
                    Paragraph(Text(
                        "The modulus D_v is a positive divisor of m, independently defined as the lcm of " +
                        "d_w/gcd(d_w,A_γ) over all actual paths γ:v→w, with empty paths and prefixes retained. Its finite " +
                        "divisor image uses m.divisors and has no path-length truncation. For every prime " +
                        "p dividing m, ν_p(D_v) is the maximum of [ν_p(d_w)−Σ_e∈γ ν_p(a_e)]_+ over all " +
                        "actual paths. The same maximum is attained on a simple actual path of length at " +
                        "most |V|−1. The loss convention is ν_p(0)=+∞ and [b−∞]_+=0.")),
                    Paragraph(Text(
                        "The recurrence is defined separately by D_v^(0)=d_v and D_v^(n+1) equal to " +
                        "the lcm of d_v and every D_w^(n)/gcd(D_w^(n),a_e) for the original outgoing " +
                        "named edges e:v→w. The proof characterizes its divisibility by the quotients of " +
                        "all paths of length at most n, using actual first-edge decomposition. Erasure " +
                        "then proves D_v^(n)=D_v for every n≥|V|−1. Empty outgoing-edge sets retain d_v.")),
                    Paragraph(Text(
                        "The retained task records include all finite-path ports, prefixes and the empty " +
                        "path. Vertex and edge identities are public; control depends on obtained port " +
                        "records and internal state, and fixed fees are determined by the retained edge " +
                        "word. No phase guard, phase-dependent fee or extra reference is introduced. " +
                        "Erasure concerns the distinguishability kernel and may change offsets, outputs, " +
                        "visit counts and fees. Different primes can attain their maxima on different " +
                        "paths; the theorem does not assert one path attaining all prime optima."))),
                DescribeRole.Theorem))));

    private static Formula Loss(Formula p, Formula path) => Seq(
        Sum, Underscore, Grp(Seq(F.Id("e"), InMacro, path)),
        Nu, Underscore, Grp(p), Open, F.Id("a"), Underscore, Grp(F.Id("e")), Close);

    private static Formula ErasureFormula()
    {
        Formula v = F.Id("v");
        Formula w = F.Id("w");
        Formula gamma = GammaLower;
        Formula eta = F.Id("eta");
        Formula p = F.Id("p");
        return Disp(Seq(
            Forall, gamma, InMacro, Call("Path", v, w), Comma, Sp,
            Exists, eta, InMacro, Call("Path", v, w), Colon, Sp,
            Call("ActualSimple", eta), Land,
            Call("Sublist", Call("edges", eta), Call("edges", gamma)), Land,
            Call("A", eta), Mid, Call("A", gamma), Land,
            Call("length", eta), Leq, Bar, F.Id("V"), Bar, Minus, D(1), Land,
            Forall, p, Comma, Loss(p, eta), Leq, Loss(p, gamma)));
    }

    private static Formula MainFormula()
    {
        Formula v = F.Id("v");
        Formula w = F.Id("w");
        Formula p = F.Id("p");
        Formula n = F.Id("n");
        Formula gamma = GammaLower;
        Formula dv = Seq(F.Id("D"), Underscore, Grp(v));
        Formula delta = Seq(Nu, Underscore, Grp(p), Open,
            F.Id("d"), Underscore, Grp(w), Close);
        Formula contribution = Seq(OpenBracket, delta, Minus, Loss(p, gamma),
            CloseBracket, Underscore, Grp(Plus));
        Formula paths = Seq(w, InMacro, F.Id("V"), Comma, gamma, InMacro, Call("Path", v, w));
        Formula bound = Seq(Bar, F.Id("V"), Bar, Minus, D(1));
        Formula simplePaths = Seq(paths, Comma, Call("ActualSimple", gamma), Comma,
            Call("length", gamma), Leq, bound);
        return Disp(Seq(
            Forall, v, Comma, D(0), Lt, dv, Land, dv, Mid, F.Id("m"), Semi, Sp,
            Forall, v, Comma, p, Comma, Call("Prime", p), Land, p, Mid, F.Id("m"), Implies,
            Grp(Forall, w, Comma, gamma, InMacro, Call("Path", v, w), Comma,
                Nu, Underscore, Grp(p), Open, Call("quotient", gamma), Close, Eq, contribution), Land,
            Nu, Underscore, Grp(p), Open, dv, Close, Eq,
            Max, Underscore, Grp(paths), contribution, Eq,
            Max, Underscore, Grp(simplePaths), contribution, Semi, Sp,
            Forall, v, Comma, n, Comma, bound, Leq, n, Implies,
            Call("iterate", n, v), Eq, dv));
    }

}
