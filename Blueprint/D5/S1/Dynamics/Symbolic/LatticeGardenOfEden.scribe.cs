using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Symbolic;

internal sealed class LatticeGardenOfEdenDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/Symbolic/LatticeGardenOfEden.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Entropy/wacker2016gardeneden");
    private static Formula Id(string s) => s == "φ" ? Varphi : F.Id(s);
    private static Formula Nat => Seq(Mathbb, Grp(Id("N")));
    private static Formula Int => Seq(Mathbb, Grp(Id("Z")));
    private static Formula Real => Seq(Mathbb, Grp(Id("R")));
    private static Formula Arr(Formula a, Formula b) => Seq(Open, a, Sp, To, Sp, b, Close);
    private static Formula Call(string s, params Formula[] args)
    {
        var name = new List<Formula>();
        foreach (var part in s.Split('.'))
        {
            if (name.Count > 0) name.Add(Dot);
            name.Add(Id(part));
        }
        var items = new List<Formula> { s == "φ" ? Varphi : Seq(Operatorname, Grp(Seq([.. name]))), Open };
        for (var i = 0; i < args.Length; i++)
        {
            if (i > 0) items.AddRange([Comma, Sp]);
            items.Add(args[i]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }
    private static Formula All(string s, Formula t) => Seq(Forall, Sp, Id(s), Colon, Sp, t, Comma);
    private static Formula Ex(string s, Formula t) => Seq(Exists, Sp, Id(s), Colon, Sp, t, Comma);
    private static Formula St(params Formula[] lines) => Disp(new Formula.Aligned([.. lines]));
    private static Formula Add(Formula a, Formula b) => Seq(a, Sp, Plus, Sp, b);
    private static Formula Cast(Formula n) => Call("cast", n);
    private static Formula G => Arr(Call("Fin", Id("d")), Int);
    private static Formula Config => Arr(G, Id("A"));
    private static Formula Rule => Arr(Arr(Id("S"), Id("A")), Id("A"));
    private static Formula Alphabet => Seq(All("u", Call("Universe")), All("A", Call("Type", Id("u"))));
    private static Formula Finite => Seq(Grp(), OpenBracket, Call("Finite", Id("A")), CloseBracket, Comma);
    private static Formula Setup => Seq(All("d", Nat), All("S", Call("Finset", G)), All("φ", Rule));
    private static Formula Code(Formula x) => Call("localMap", Id("S"), Id("φ"), x);
    private static Formula Pre => Call("Preinjective", Id("S"), Id("φ"));
    private static Formula Box(Formula n) => Call("box", Id("d"), Add(n, D(1)));
    private static Formula Card => Call("Nat.card", Id("A"));
    private static Formula LogCard => Call("Real.log", Cast(Card));
    private static Formula Rate => Seq(
        Call("Real.log", Cast(Call("imagePatternCount", Box(Id("n")), Id("S"), Id("φ")))),
        Slash, Call("pow", Cast(Add(Id("n"), D(1))), Id("d")));

    private static Formula ScalarLog(Formula x) => Call("Real.log", Cast(x));
    private static Formula Pow(Formula x, Formula y) => Seq(Grp(x), Caret, Grp(y));
    private static Formula ScalarDeficit => Seq(Open, Cast(Id("b")), Sp, Star, Sp, ScalarLog(Id("a")),
        Sp, Minus, Sp, ScalarLog(Seq(Pow(Id("a"), Id("b")), Sp, Minus, Sp, D(1))), Close,
        Slash, Pow(Cast(Id("b")), D(2)));
    private static Formula ScalarPackingStatement => St(
        Seq(All("a", Nat), All("b", Nat), All("k", Nat), All("u", Nat), All("v", Nat), All("f", Nat)),
        Seq(D(2), Sp, Le, Sp, Id("a"), Sp, Land, Sp, D(0), Sp, Lt, Sp, Id("b"), Sp, Land,
            Sp, D(0), Sp, Lt, Sp, Id("v"), Sp, Land, Sp, D(0), Sp, Lt, Sp, Id("f"), Sp, Land),
        Seq(Id("v"), Sp, Le, Sp, Id("k"), Sp, Star, Sp, Pow(Id("b"), D(2)), Sp, Land,
            Sp, Id("k"), Sp, Star, Sp, Id("b"), Sp, Le, Sp, Id("u"), Sp, Land),
        Seq(Id("f"), Sp, Le, Sp, Pow(Seq(Pow(Id("a"), Id("b")), Sp, Minus, Sp, D(1)), Id("k")),
            Sp, Star, Sp, Pow(Id("a"), Seq(Id("u"), Sp, Minus, Sp, Id("k"), Sp, Star, Sp, Id("b"))), Sp, Rightarrow),
        Seq(D(0), Sp, Lt, Sp, ScalarDeficit, Sp, Land),
        Seq(ScalarLog(Id("f")), Slash, Cast(Id("v")), Sp, Le, Sp, Open, Cast(Id("u")), Slash,
            Cast(Id("v")), Close, Sp, Star, Sp, ScalarLog(Id("a")), Sp, Minus, Sp, ScalarDeficit));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Surjectivity and finite-disagreement preinjectivity coincide for every finite-alphabet local rule on every finite-dimensional integer lattice.",
        H("The lattice Garden-of-Eden theorem"), Blocks(
        Paragraph(Text("Fix an arbitrary universe u, a finite A : Type(u), a natural rank d, a finite subset S of the lattice Fin(d) → Z, "
            + "and a rule φ : (S → A) → A. Full configurations are arbitrary functions from that lattice to A. "
            + "The full map Φ reads the translated S-pattern at each site. The neighborhood may be empty, nonrectangular or asymmetric. "
            + "No permutativity, local injectivity, separation into rows or coordinate directions, periodicity, finite configuration domain, "
            + "finite complete-output fiber, entropy certificate or alphabet lower bound is part of the equivalence.")),
        Describe.Lean(DescribeId.Create("full-local-map"), DeclarationHandle.Create(Owner + "localMap"),
            H("The full local map"), StatementSource.FromAuthor(St(
                Alphabet, Setup, All("x", Config), All("z", G),
                Seq(Call("localMap", Id("S"), Id("φ"), Id("x"), Id("z")), Sp, Eq, Sp,
                    Call("φ", Seq(Open, Id("s"), Sp, Mapsto, Sp, Call("x", Add(Id("z"), Id("s"))), Close))))),
            AssessedProvenance.FromLiterature(Source), Blocks(
                Paragraph(Text("The definition is also available on any additive commutative group. The theorem specializes its group "
                    + "to the full integer lattice; it does not restrict the rule to one-dimensional or separable dynamics."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("finite-disagreement-preinjectivity"), DeclarationHandle.Create(Owner + "Preinjective"),
            H("Preinjectivity on finite disagreements"), StatementSource.FromAuthor(St(
                Alphabet, Setup, Seq(Pre, Sp, Iff), All("x", Config), All("y", Config),
                Seq(Call("Set.Finite", Call("disagreement", Id("x"), Id("y"))), Sp, Rightarrow, Sp,
                    Code(Id("x")), Sp, Eq, Sp, Code(Id("y")), Sp, Rightarrow, Sp, Id("x"), Sp, Eq, Sp, Id("y")))),
            AssessedProvenance.FromLiterature(Source), Blocks(
                Paragraph(Text("The disagreement set is exactly the set of sites z at which x(z) and y(z) differ. "
                    + "Equality of images means equality at every lattice site, not just on a finite observation window."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("actual-image-patterns"), DeclarationHandle.Create(Owner + "ImagePatterns"),
            H("Jointly realized image patterns"), StatementSource.FromAuthor(St(
                Alphabet, Setup, All("F", Call("Finset", G)), All("p", Arr(Id("F"), Id("A"))),
                Seq(Id("p"), Sp, InMacro, Sp, Call("ImagePatterns", Id("S"), Id("φ"), Id("F")), Sp, Iff),
                Ex("x", Config), All("z", Id("F")), Seq(Call("p", Id("z")), Sp, Eq, Sp, Call("localMap", Id("S"), Id("φ"), Id("x"), Id("z"))))),
            AssessedProvenance.FromLiterature(Source), Blocks(
                Paragraph(Text("One complete configuration x must realize the entire pattern p simultaneously. The count imagePatternCount(F,S,φ) "
                    + "is Nat.card of this actual image-pattern type. It does not count independent local witnesses or arbitrary compatible patches."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("logarithmic-packing-bound"), DeclarationHandle.Create(Owner + "logarithmic_packing_bound"),
            H("A packing count gives a uniform logarithmic deficit"), StatementSource.FromAuthor(ScalarPackingStatement),
            AssessedProvenance.FromLiterature(Source), Blocks(
                Paragraph(Text("For natural a,b,k,u,v,f with a≥2, b,v,f positive, v≤k*b², k*b≤u and "
                    + "f≤(a^b−1)^k*a^(u−k*b), put δ=(b*log(a)−log(a^b−1))/b². "
                    + "Then δ>0 and log(f)/v≤(u/v)*log(a)−δ. "
                    + "This scalar estimate has no group hypothesis and applies to both lattice boxes and arbitrary-group finite-pattern counts."))),
            DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("strict-box-loss"), DeclarationHandle.Create(Owner + "strict_image_box_loss"),
            H("A finite collision forces strict logarithmic image loss"), StatementSource.FromAuthor(St(
                Alphabet, Finite, All("d", Nat), Seq(D(1), Sp, Le, Sp, Id("d"), Sp, Rightarrow),
                All("S", Call("Finset", G)), All("φ", Rule), Seq(D(2), Sp, Le, Sp, Card, Sp, Rightarrow),
                All("x", Config), All("y", Config),
                Seq(Call("Set.Finite", Call("disagreement", Id("x"), Id("y"))), Sp, Rightarrow, Sp,
                    Code(Id("x")), Sp, Eq, Sp, Code(Id("y")), Sp, Rightarrow, Sp, Id("x"), Sp, Neq, Sp, Id("y"), Sp, Rightarrow),
                Ex("c", Real), Seq(Id("c"), Sp, Lt, Sp, LogCard, Sp, Land),
                Ex("N", Nat), All("n", Nat), Seq(Id("N"), Sp, Le, Sp, Id("n"), Sp, Rightarrow, Rate, Sp, Le, Sp, Id("c")))),
            AssessedProvenance.FromLiterature(Source), Blocks(
                Paragraph(Text("Here box(d,n+1) consists exactly of lattice sites whose every coordinate lies between zero and n inclusive, "
                    + "and has (n+1)^d sites. Thus the denominator is the actual box volume. The finite collision, its finite disagreement set, "
                    + "and equality of the complete images are the only dynamical hypotheses.")),
                Paragraph(Text("For a disagreement core D, retain D together with all points a−s+t for a in D and s,t in S. "
                    + "Every local window touching D lies in this finite collar. Replacing the colliding collar pattern in a matching ambient context "
                    + "preserves the entire image. On disjoint translates, successive replacements eliminate one prescribed collar pattern without "
                    + "changing any image coordinate.")),
                Paragraph(Text("A maximal disjoint family of translates with centers in a finite F covers the possible centers by translated "
                    + "pairs of collar sites. If the collar has b sites, the family has at least card(F)/b² members. For any padded input shape U "
                    + "containing these translates and all local windows needed for F, actual image patterns inject into a product with "
                    + "(card(A)^b−1) choices on each translate and card(A) choices on the remaining sites. The resulting count is at most "
                    + "(card(A)^b−1)^k card(A)^(card(U)−kb). This product counts restrictions of the same normalized full configuration.")),
                Paragraph(Text("The supplied lattice-box geometry makes every fixed finite padding have volume ratio tending to one. "
                    + "The positive deficit [b log(card(A))−log(card(A)^b−1)]/b² therefore yields a uniform eventual strict upper bound. "
                    + "The box-through-boundary estimates are due to Tom Ole Diem. They control the padding volume; "
                    + "the collision and packing arguments supply the strict image-count deficit."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("lattice-equivalence"), DeclarationHandle.Create(Owner + "garden_of_eden"),
            H("Surjectivity is equivalent to preinjectivity in every finite rank"), StatementSource.FromAuthor(St(
                Alphabet, Finite, Setup,
                Seq(Call("Function.Surjective", Call("localMap", Id("S"), Id("φ"))), Sp, Iff, Sp, Pre))),
            AssessedProvenance.FromLiterature(Source), Blocks(
                Paragraph(Text("All natural ranks are included, including zero. All finite alphabet universes are included, including empty "
                    + "and singleton alphabets. A subsingleton alphabet makes both assertions immediate. At rank zero the configuration space "
                    + "is finite, finite-disagreement preinjectivity is ordinary injectivity, and the finite endomap theorem applies.")),
                Paragraph(Text("At rank one, the coordinate equivalence with Z, a finite enclosing integer window and an output translation "
                    + "transport both assertions to the existing native GardenOfEden.garden_of_eden theorem, which is applied directly. "
                    + "In higher rank and for at least two letters, surjectivity realizes every pattern on every box. "
                    + "Its logarithmic count per site is exactly log(card(A)), contradicting the strict collision loss if preinjectivity fails.")),
                Paragraph(Text("For the reverse implication, the full finite-alphabet shift is compact and the local map is continuous. "
                    + "A configuration outside the closed image has a finite cylinder missing the image. Translation gives one finite output "
                    + "pattern absent at every site. The same disjoint-packing count then gives a strict upper deficit. Preinjectivity gives the "
                    + "opposing lower comparison: arbitrary source patterns on a finite F, inserted in one fixed constant context, inject into "
                    + "actual output patterns on the finite set obtained by padding F by the negative neighborhood. Equal observations there "
                    + "give equal complete images because every output that can be affected lies in that padded set. No assumption on the "
                    + "cardinality of a complete-output fiber is used. The fixed padding has asymptotically unit volume ratio, so the two bounds contradict.")),
                Paragraph(Text("This is the classical Moore–Myhill equivalence specialized to finite-dimensional integer lattices."))), DescribeRole.Theorem)),
        [DocumentEdge.Dependency.Create(GidRef.Create("D5/S1/Dynamics/Symbolic/GardenOfEden"))]));
}
