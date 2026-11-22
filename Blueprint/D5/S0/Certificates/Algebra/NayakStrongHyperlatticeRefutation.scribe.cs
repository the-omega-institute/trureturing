using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates.Algebra;

internal sealed class NayakStrongHyperlatticeRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S0/Certificates/Algebra/NayakStrongHyperlatticeRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Certificates/nayaketal2026convexsubhyperlattices");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A five-element strong join hyperlattice has two convex subhyperlattices without a "
            + "greatest lower bound in Birkhoff order.",
        H("The Birkhoff order on convex subhyperlattices need not be a lattice"),
        Blocks(
            Definition("hyperoperation-extension", "hyperExtend", "Extension to two sets",
                MembershipExtension(),
                "For a hyperoperation j on a carrier, the result on two sets A and B is the "
                    + "union of j(x,y) over all x in A and y in B."),
            Describe.Lean(DescribeId.Create("strong-join-hyperlattice"),
                DeclarationHandle.Create(Prefix + "StrongJoinHyperlattice"),
                H("Strong join hyperlattices"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "The carrier is nonempty. The meet is a binary operation and the hyperjoin "
                    + "assigns a nonempty subset to every pair. The meet is idempotent, associative "
                    + "and commutative. Each diagonal hyperjoin contains its input. The hyperjoin "
                    + "is commutative and associative with the extension to sets, interpreting "
                    + "an element argument as its singleton.")),
                    Paragraph(Text(
                    "The first absorption law places x in the pointwise meet image of the "
                    + "singleton of x and the hyperjoin of x and y. The second places x in "
                    + "the hyperjoin of x and the meet of x and y. The strong axiom requires "
                    + "the meet of x and y to equal x whenever y belongs to their hyperjoin."))),
                DescribeRole.Definition),
            Definition("meet-order", "meetOrder", "The induced order",
                Seq(F.Id("x"), Sp, Leq, Sp, F.Id("y"), Sp, Iff, Sp,
                    Op("H", "meet", F.Id("x"), F.Id("y")), Eq, F.Id("x")),
                "Reflexivity, transitivity and antisymmetry follow from the three meet laws. "
                    + "Equivalently, y belongs to the hyperjoin of x and y. Strongness gives "
                    + "one implication. Meet commutativity, hyperjoin absorption and hyperjoin "
                    + "commutativity give the other."),
            Definition("convex-subhyperlattices", "CS", "Convex subhyperlattices",
                ConvexMembership(),
                "The subtype uses the induced order in OrdConnected. When two elements "
                    + "belong to S, their meet and every value of their hyperjoin belong to S. "
                    + "OrdConnected includes every element between two members of S."),
            Definition("birkhoff-relation", "birkhoffLE", "The two Birkhoff clauses",
                BirkhoffRelation(),
                "A and B denote the underlying sets of the two convex subhyperlattices. "
                    + "Every member of A is below some member of B, and every member of B "
                    + "is above some member of A. Both comparisons use the induced order."),
            Definition("birkhoff-order", "birkhoffOrder", "The Birkhoff partial order",
                Seq(F.Id("A"), Sp, Leq, Sp, F.Id("B"), Sp, Iff, Sp,
                    Call("birkhoffLE", F.Id("H"), F.Id("A"), F.Id("B"))),
                "The two clauses compose to give transitivity. If both comparisons hold, "
                    + "each element of either set lies between two elements of the other set. "
                    + "Order convexity then gives equality of the sets."),
            Definition("universe-conjecture", "claimAt", "The conjecture at an arbitrary carrier universe",
                Conjecture(F.Id("u")),
                "For each carrier and each strong join hyperlattice structure on it, "
                    + "use birkhoffOrder H as the local order on CS H. IsGLB and IsLUB "
                    + "require respectively a greatest common lower bound and a least common "
                    + "upper bound among all convex subhyperlattices. Both must exist for every pair."),
            Definition("section-five-conjecture", "claim", "The conjecture for carriers in Type 0",
                Conjecture(D(0)),
                "This is claimAt at universe zero. It includes all finite carriers and "
                    + "all infinite carriers in Type 0."),
            Describe.Lean(DescribeId.Create("conjecture-refuted"),
                DeclarationHandle.Create(Prefix + "result"), H("The universal conjecture is false"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Par(Conjecture(D(0)))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "Adjoin a new top t to the Boolean square with bottom 0, incomparable "
                    + "atoms a and b, and top c. Use ordinary meet. For inputs x and y, the "
                    + "hyperjoin contains their ordinary join s and contains t additionally "
                    + "exactly when s equals c and x and y differ. The ordinary join of a "
                    + "triple always occurs in either association. An additional t occurs "
                    + "precisely when the total ordinary join equals c and at least one "
                    + "input differs from c. The usual lattice absorptions and the fact that "
                    + "every hyperjoin output is above its inputs give the absorption and "
                    + "strongness laws.")),
                    Paragraph(Text(
                    "The singleton of c and the whole carrier have the two atom intervals "
                    + "from 0 to a and from 0 to b as common lower bounds. Any greatest "
                    + "lower bound must contain 0 by comparison with the whole carrier. "
                    + "Domination of the intervals provides an element above each atom. "
                    + "Convexity with 0 puts a and b in the bound, and hyperjoin closure "
                    + "puts t there. Comparison with the singleton would require t to be "
                    + "below c. The same countermodel lifts to every carrier universe."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("nayak-strong-hyperlattice-birkhoff"),
                    ResolutionKind.Refuted)))));

    private static DocumentBlock Definition(string id, string declaration, string title,
        Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(Disp(formula)), AssessedProvenance.FromLiterature(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula Par(Formula value) => Seq(Open, value, Close);

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula>();
        foreach (var argument in arguments)
        {
            if (items.Count > 0)
                items.Add(Comma);
            items.Add(argument);
        }
        return Seq(Operatorname, Grp(F.Id(name)), Par(Seq([.. items])));
    }

    private static Formula Op(string owner, string name, params Formula[] arguments) =>
        Seq(F.Id(owner), Dot, Call(name, arguments));

    private static Formula Quantified(Formula quantifier, Formula variables, Formula bound, Formula body) =>
        Seq(quantifier, Sp, Par(Seq(variables, bound)), Comma, Sp, body);

    private static Formula Member(Formula element, Formula set) => Seq(element, Sp, InMacro, Sp, set);

    private static Formula MembershipExtension()
    {
        var a = F.Id("A");
        var b = F.Id("B");
        var w = F.Id("w");
        var x = F.Id("x");
        var y = F.Id("y");
        return Seq(Member(w, Call("hyperExtend", F.Id("j"), a, b)), Sp, Iff, Sp,
            Quantified(Exists, x, Seq(Sp, InMacro, Sp, a),
                Quantified(Exists, y, Seq(Sp, InMacro, Sp, b), Member(w, Call("j", x, y)))));
    }

    private static Formula ConvexMembership()
    {
        var h = F.Id("H");
        var s = F.Id("S");
        var x = F.Id("x");
        var y = F.Id("y");
        var inS = Seq(Sp, InMacro, Sp, s);
        return Seq(Call("CS", h), Sp, Eq, Sp, OpenBrace, s, Colon, Call("Set", Alpha),
            Sp, Mid, Sp,
            Projection(s, "Nonempty"), Sp, Land, Sp,
            Par(Quantified(Forall, x, inS, Quantified(Forall, y, inS,
                Seq(Member(Op("H", "meet", x, y), s), Sp, Land, Sp,
                    Op("H", "hjoin", x, y), Sp, Subseteq, Sp, s)))),
            Sp, Land, Sp, Projection(s, "OrdConnected"), CloseBrace);
    }

    private static Formula Projection(Formula source, string name) => Seq(source, Dot, F.Id(name));

    private static Formula BirkhoffRelation()
    {
        var a = F.Id("A");
        var b = F.Id("B");
        return Seq(Call("birkhoffLE", F.Id("H"), a, b), Sp, Iff, Sp,
            Call("IsCofinalFor", Projection(a, "val"), Projection(b, "val")), Sp, Land, Sp,
            Call("IsCoinitialFor", Projection(b, "val"), Projection(a, "val")));
    }

    private static Formula Conjecture(Formula universe)
    {
        var h = F.Id("H");
        var m = F.Id("M");
        var j = F.Id("J");
        var subhyperlattices = Call("CS", h);
        var pair = Seq(OpenBrace, F.Id("X"), Comma, F.Id("Y"), CloseBrace);
        var glb = Quantified(Exists, m, Seq(Colon, subhyperlattices), Call("IsGLB", pair, m));
        var lub = Quantified(Exists, j, Seq(Colon, subhyperlattices), Call("IsLUB", pair, j));
        return Quantified(Forall, Alpha, Seq(Colon, Operatorname, Grp(F.Id("Type")), Underscore, Grp(universe)),
            Quantified(Forall, h, Seq(Colon, Call("StrongJoinHyperlattice", Alpha)),
                Quantified(Forall, Seq(F.Id("X"), Comma, F.Id("Y")), Seq(Colon, subhyperlattices),
                    Seq(Par(glb), Sp, Land, Sp, Par(lub)))));
    }
}
