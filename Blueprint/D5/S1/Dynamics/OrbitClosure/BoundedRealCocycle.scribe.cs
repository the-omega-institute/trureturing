using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.OrbitClosure;

internal sealed class BoundedRealCocycleDocument : IScribeDocumentDefinition
{
    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, F.Id(name), Colon, Sp, type, Comma, Sp, body);
    private static Formula And(params Formula[] parts)
    {
        var result = Seq(Open, parts[0], Close);
        for (var i = 1; i < parts.Length; i++)
            result = new Formula.Logic(result, FormulaLogicOperator.And,
                Seq(Open, parts[i], Close));
        return result;
    }
    private static Formula Abs(Formula value) => Seq(Bar, value, Bar);

    public DocumentDefinition Create()
    {
        var gamma = F.Id("G");
        var xType = F.Id("X");
        var a = F.Id("a");
        var c = F.Id("c");
        var b = F.Id("b");
        var bound = F.Id("C");
        var g = F.Id("g");
        var h = F.Id("h");
        var x = F.Id("x");
        var real = Seq(Mathbb, Grp(F.Id("R")));
        var type = Seq(Operatorname, Grp(F.Id("Type")));
        var product = Seq(g, Sp, Cdot, Sp, h);
        var hypotheses = And(
            All("g", gamma, Call("Continuous", Call("slice", a, g))),
            All("g", gamma, All("h", gamma, All("x", xType,
                Seq(Call("a", product, x), Eq, Call("a", g, Call("a", h, x)))))),
            All("x", xType, Call("DenseRange", Call("orbit", a, x))),
            All("g", gamma, Call("Continuous", Call("slice", c, g))),
            All("g", gamma, All("h", gamma, All("x", xType,
                Seq(Call("c", product, x), Eq,
                    Call("c", g, Call("a", h, x)), Plus, Call("c", h, x))))));
        var transfer = And(
            Call("Continuous", F.Id("phi")),
            Seq(Call("phi", b), Eq, D(0)),
            All("g", gamma, All("x", xType,
                Seq(Call("phi", Call("a", g, x)), Minus, Call("phi", x),
                    Eq, Call("c", g, x)))),
            All("x", xType, Seq(Abs(Call("phi", x)), Sp, Le, Sp, bound)));
        var equivalence = Seq(
            Open, All("g", gamma, Seq(Abs(Call("c", g, b)), Sp, Le, Sp, bound)), Close,
            Sp, Leftrightarrow, Sp,
            Exists, Bang, Sp, F.Id("phi"), Colon, Sp, xType, Sp, To, Sp, real, Comma, Sp, transfer);
        var classes = Seq(
            OpenBracket, Call("Mul", gamma), CloseBracket, Sp,
            OpenBracket, Call("TopologicalSpace", xType), CloseBracket, Sp,
            OpenBracket, Call("CompactSpace", xType), CloseBracket, Sp,
            OpenBracket, Call("T2Space", xType), CloseBracket, Comma, Sp);
        var statement = All("G", type, All("X", type, Seq(classes,
            All("a", Seq(gamma, Sp, To, Sp, xType, Sp, To, Sp, xType),
            All("c", Seq(gamma, Sp, To, Sp, xType, Sp, To, Sp, real),
            All("b", xType, All("C", real,
                Seq(Open, hypotheses, Close, Sp, Rightarrow, Sp,
                    Open, equivalence, Close))))))));

        return DocumentDefinition.Create(ScribeNode.Create(
            "A bounded real cocycle on one dense orbit determines a unique continuous normalized potential.",
            H("Bounded Real Cocycles and Continuous Potentials"),
            Blocks(Describe.Lean(
                DescribeId.Create("bounded-real-cocycle-continuous-transfer"),
                DeclarationHandle.Create("D5/S1/Dynamics/OrbitClosure/BoundedRealCocycle."
                    + "bounded_iff_existsUnique_transfer"),
                H("Exact reconstruction from a bounded orbit"),
                StatementSource.FromAuthor(Disp(statement)),
                AssessedProvenance.FromRepo(
                    LibraryNoteRef.Create("D5/L/Cohomology/coronelnavasponce2011bounded"),
                    LibraryNoteRef.Create("D5/L/Cohomology/petkovic2026cohomology")),
                Blocks(
                    Paragraph(Text(
                        "G and X range over independent universes. G has a multiplication, and X is " +
                        "compact and Hausdorff. The notation slice(a,g) means x mapped to a(g,x); " +
                        "orbit(a,x) means g mapped to a(g,x). Each action slice and each real cocycle slice " +
                        "is continuous. Every G-orbit is dense. The displayed composition equations " +
                        "refer to this one action and this one cocycle.")),
                    Paragraph(Text(
                        "The point b is specified and C is any real number. The unique potential is continuous, " +
                        "vanishes at b, has the prescribed difference along every action map, and satisfies " +
                        "the same bound C at every point. No identity, inverse, associativity, commutativity, " +
                        "finite generation or topology on G is required. Action maps may be noninvertible. " +
                        "Density and the given b imply that G is inhabited. Negative C makes both sides " +
                        "impossible; C = 0 is included. In particular the result applies to every semigroup " +
                        "acting minimally on a compact metric space.")),
                    Paragraph(Text(
                        "For F_g(x,t) = (a(g,x), t + c(g,x)), the cocycle identity makes the closure of the " +
                        "actual skew orbit {(a(g,b), c(g,b))} forward invariant. The one-point bound places " +
                        "this closure inside the compact product X times [-C,C]. Intersections of descending " +
                        "chains of nonempty compact sets preserve invariance under every F_g. Zorn's lemma " +
                        "therefore gives a minimal nonempty compact invariant subset K. Its projection to X " +
                        "is compact and closed, contains a dense orbit, and hence equals X.")),
                    Paragraph(Text(
                        "Suppose a fibre of K contains heights v and w, and put d = w - v. Vertical translation " +
                        "by -d commutes with every F_g. The intersection of K with the inverse image of K " +
                        "under this translation is nonempty, compact and forward invariant. Minimality makes " +
                        "it contain K. The global minimum and maximum heights of K then force d = 0. Thus " +
                        "each fibre has exactly one point. The projection from K to X is a continuous " +
                        "bijection from a compact space to a Hausdorff space, so its inverse is continuous. " +
                        "The second coordinate of that inverse is a continuous transfer psi.")),
                    Paragraph(Text(
                        "Subtract psi(b) to normalize the transfer. On the dense orbit of b, the resulting " +
                        "phi(a(g,b)) equals c(g,b). Closedness of the scalar bound propagates the original " +
                        "constant C to all of X. This step avoids the weaker 2C estimate obtained by separately " +
                        "bounding two heights. Equality on that same dense orbit proves uniqueness. Conversely, " +
                        "evaluating the transfer equation at b immediately recovers the one-point bound.")),
                    Paragraph(Text(
                        "Coronel, Navas and Ponce prove the broader invariant-section theorem for bounded " +
                        "isometric cocycles over minimal continuous semigroup dynamics. Real translations " +
                        "supply the mathematical provenance here. The normalized uniqueness, exact same-C " +
                        "estimate and compact Hausdorff interface are the explicit conclusions above, rather " +
                        "than a quotation of their metric-space statement. General CAT(0), Hilbert-valued, " +
                        "matrix and reflection-valued cocycles are outside this result.")),
                    Paragraph(Text(
                        "For a compatible real cocycle over a minimal Z^k action, this criterion recovers a " +
                        "continuous coboundary from a joint all-elements bound. Petkovic's smooth simultaneous " +
                        "Diophantine stability conjecture supplies a related research problem. Establishing " +
                        "that bound and minimality for a chosen circle action, smooth regularity of the " +
                        "transfer, closed range and the conjectured classification remain separate questions. " +
                        "No smooth-conjecture resolution, recovery algorithm or originality is asserted."))),
                DescribeRole.Theorem))));
    }
}
