using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Dynamics.Symbolic;

internal sealed class AmenableGardenOfEdenDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S1/Dynamics/Symbolic/AmenableGardenOfEden.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Entropy/wacker2016gardeneden");

    private static Formula Id(string s) => s == "φ" ? Varphi : F.Id(s);
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
    private static Formula St(params Formula[] lines) => Disp(new Formula.Aligned([.. lines]));
    private static Formula Config => Arr(Id("G"), Id("A"));
    private static Formula Rule => Arr(Arr(Id("S"), Id("A")), Id("A"));
    private static Formula Setup => Seq(All("u", Call("Universe")), All("v", Call("Universe")),
        All("A", Call("Type", Id("u"))), All("G", Call("Type", Id("v"))),
        OpenBracket, Call("Group", Id("G")), CloseBracket, Comma);
    private static Formula LocalSetup => Seq(All("S", Call("Finset", Id("G"))), All("φ", Rule));
    private static Formula Code(Formula x) => Call("localMap", Id("S"), Id("φ"), x);
    private static Formula Mul(Formula x, Formula y) => Seq(x, Sp, Star, Sp, y);
    private static Formula Coord => Mul(Seq(Id("t"), Caret, Grp(Minus, D(1))), Id("g"));

    private static Formula Ex(string s, Formula t) => Seq(Exists, Sp, Id(s), Colon, Sp, t, Comma);
    private static Formula Card(Formula x) => Call("card", x);
    private static Formula Pow(Formula x, Formula y) => Seq(Grp(x), Caret, Grp(y));
    private static Formula AlphabetCard => Call("Nat.card", Id("A"));
    private static Formula FiniteAlphabet => Seq(Grp(), OpenBracket, Call("Finite", Id("A")), CloseBracket, Comma);
    private static Formula Pad => Mul(Id("F"), Call("insert", D(1), Call("union", Id("S"), Id("C"))));
    private static Formula PatternCount => Call("Nat.card", Call("ImagePatterns", Id("S"), Id("φ"), Id("F")));
    private static Formula AvoidanceBound => Mul(
        Pow(Seq(Pow(AlphabetCard, Card(Id("C"))), Sp, Minus, Sp, D(1)), Card(Id("T"))),
        Pow(AlphabetCard, Seq(Card(Pad), Sp, Minus, Sp, Mul(Card(Id("T")), Card(Id("C"))))));
    private static Formula CollisionStatement => St(Setup, FiniteAlphabet, LocalSetup,
        Seq(All("x", Config), All("y", Config), Id("x"), Sp, Neq, Sp, Id("y"), Sp, Land, Sp,
            Call("Set.Finite", Call("disagreement", Id("x"), Id("y"))), Sp, Land, Sp,
            Code(Id("x")), Sp, Eq, Sp, Code(Id("y")), Sp, Rightarrow),
        Seq(Ex("C", Call("Finset", Id("G"))), Ex("p", Arr(Id("C"), Id("A"))),
            Ex("q", Arr(Id("C"), Id("A"))), Id("p"), Sp, Neq, Sp, Id("q"), Sp, Land),
        Seq(Open, All("t", Id("G")), All("z", Config), Open, All("c", Id("C")),
            Call("z", Mul(Id("t"), Id("c"))), Sp, Eq, Sp, Call("p", Id("c")), Close,
            Sp, Rightarrow, Sp, Code(Call("writePattern", Id("C"), Id("q"), Id("t"), Id("z"))),
            Sp, Eq, Sp, Code(Id("z")), Close, Sp, Land),
        Seq(All("F", Call("Finset", Id("G"))), Ex("T", Call("Finset", Id("G"))),
            Id("T"), Sp, Subseteq, Sp, Id("F"), Sp, Land),
        Seq(Open, All("t", Id("T")), All("r", Id("T")), Id("t"), Sp, Neq, Sp, Id("r"),
            Sp, Rightarrow, Sp, All("c", Id("C")), All("e", Id("C")),
            Mul(Id("t"), Id("c")), Sp, Neq, Sp, Mul(Id("r"), Id("e")), Close, Sp, Land),
        Seq(Card(Id("F")), Sp, Le, Sp, Mul(Card(Id("T")), Pow(Card(Id("C")), D(2))), Sp, Land),
        Seq(Mul(Card(Id("T")), Card(Id("C"))), Sp, Le, Sp, Card(Pad), Sp, Land),
        Seq(PatternCount, Sp, Le, Sp, AvoidanceBound));
    private static Formula GardenStatement => St(Setup, FiniteAlphabet,
        Seq(Call("MeasurableSpace", Id("G")), Colon, Eq, Call("discrete"), Comma),
        Seq(Call("NeBot", Call("maxFoelner", Seq(Id("G"), Caret, Grp(Mathrm, Grp(Id("op")))),
            Call("Measure.count", Id("G")))), Sp, Rightarrow), LocalSetup,
        Seq(Call("Function.Surjective", Call("localMap", Id("S"), Id("φ"))), Sp, Iff, Sp,
            Call("Preinjective", Id("S"), Id("φ"))));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Surjectivity and finite-disagreement preinjectivity coincide for full cellular maps over every finite alphabet on every discrete group with a nontrivial right counting Følner filter.",
        H("Full cellular maps on groups"), Blocks(
        Paragraph(Text("Let A be a finite alphabet in an arbitrary universe and G a group in an independent universe. "
            + "A finite neighborhood S and a rule φ : (S → A) → A define the full map Φ(x)(g) = φ(s ↦ x(g*s)). "
            + "Configurations are all functions G → A; the group need not be countable, finitely generated or commutative. "
            + "The neighborhood may be empty or asymmetric. Empty and singleton alphabets are included.")),
        Describe.Lean(DescribeId.Create("full-local-map"), DeclarationHandle.Create(Owner + "localMap"),
            H("The full local map"), StatementSource.FromAuthor(St(Setup, LocalSetup,
                Seq(All("x", Config), All("g", Id("G")), Call("localMap", Id("S"), Id("φ"), Id("x"), Id("g")),
                    Sp, Eq, Sp, Call("φ", Seq(Open, Id("s"), Sp, Mapsto, Sp,
                        Call("x", Mul(Id("g"), Id("s"))), Close))))),
            AssessedProvenance.FromLiterature(Source), Blocks(
                Paragraph(Text("All products are written in the displayed order. The neighborhood coordinates multiply on the right. Left translation of a configuration therefore commutes with the map."))),
            DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("finite-disagreement-preinjectivity"), DeclarationHandle.Create(Owner + "Preinjective"),
            H("Preinjectivity on finite disagreements"), StatementSource.FromAuthor(St(Setup, LocalSetup,
                Seq(Call("Preinjective", Id("S"), Id("φ")), Sp, Iff),
                Seq(All("x", Config), All("y", Config), Call("Set.Finite", Call("disagreement", Id("x"), Id("y"))),
                    Sp, Rightarrow, Sp, Code(Id("x")), Sp, Eq, Sp, Code(Id("y")), Sp, Rightarrow, Sp,
                    Id("x"), Sp, Eq, Sp, Id("y")))),
            AssessedProvenance.FromLiterature(Source), Blocks(
                Paragraph(Text("The disagreement set is exactly {g | x(g)≠y(g)}. Two configurations with finite disagreement and equal complete images must be equal. "
                    + "Equality of images is equality at every group element."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("actual-image-patterns"), DeclarationHandle.Create(Owner + "ImagePatterns"),
            H("Jointly realized image patterns"), StatementSource.FromAuthor(St(Setup, LocalSetup,
                Seq(All("F", Call("Finset", Id("G"))), All("p", Arr(Id("F"), Id("A"))),
                    Id("p"), Sp, InMacro, Sp, Call("ImagePatterns", Id("S"), Id("φ"), Id("F")), Sp, Iff),
                Seq(Exists, Sp, Id("x"), Colon, Sp, Config, Comma, All("f", Id("F")),
                    Call("p", Id("f")), Sp, Eq, Sp, Call("localMap", Id("S"), Id("φ"), Id("x"), Id("f"))))),
            AssessedProvenance.FromLiterature(Source), Blocks(
                Paragraph(Text("ImagePatterns(S,φ,F) is the range of x ↦ (f ↦ Φ(x)(f)) on all complete configurations x. "
                    + "One x must realize all coordinates of a pattern simultaneously."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("left-coordinate-replacement"), DeclarationHandle.Create(Owner + "writePattern"),
            H("Replace a pattern on a left translate"), StatementSource.FromAuthor(St(Setup,
                Seq(All("C", Call("Finset", Id("G"))), All("p", Arr(Id("C"), Id("A"))),
                    All("t", Id("G")), All("x", Config), All("g", Id("G"))),
                Seq(Call("writePattern", Id("C"), Id("p"), Id("t"), Id("x"), Id("g")), Sp, Eq, Sp,
                    Call("ite", Seq(Coord, Sp, InMacro, Sp, Id("C")), Call("p", Coord), Call("x", Id("g")))))),
            AssessedProvenance.FromLiterature(Source), Blocks(
                Paragraph(Text("On the translate t*C the new value at g is p(t⁻¹*g); outside that translate it is the original value. "
                    + "The coordinate t⁻¹*g is unique and keeps the order of multiplication explicit."))), DescribeRole.Definition),
        Describe.Lean(DescribeId.Create("collision-replacement-count"), DeclarationHandle.Create(Owner + "collision_replacement_count"),
            H("Uniform replacement and actual-image counting from a collision"), StatementSource.FromAuthor(CollisionStatement),
            AssessedProvenance.FromLiterature(Source), Blocks(
                Paragraph(Text("For distinct configurations x,y with finite disagreement and Φ(x)=Φ(y), there are a finite C and distinct patterns p,q on C. "
                    + "Whenever an ambient z has pattern p on t*C, replacing that pattern by q preserves the complete image Φ(z), for every t and z. "
                    + "This finite statement needs no amenability assumption.")),
                Paragraph(Text("For every finite F there is T contained in F whose translates t*C are pairwise disjoint. "
                    + "Writing a=Nat.card(A), E={1}∪S∪C and U=F*E, the simultaneous bounds are "
                    + "card(F) ≤ card(T)*card(C)², card(T)*card(C) ≤ card(U), and "
                    + "Nat.card(ImagePatterns(S,φ,F)) ≤ (a^card(C)−1)^card(T) * a^(card(U)−card(T)*card(C)).")),
                Paragraph(Text("The collar of the actual disagreement core D is D∪D*S⁻¹*S. Every neighborhood window touching D lies in it. "
                    + "Successive replacements on disjoint left translates preserve one complete image and eliminate p from every selected translate. "
                    + "For each actual image pattern choose one complete source and normalize it in this way. "
                    + "Record the avoiding C-patterns together with the source on the residual part of U. "
                    + "Equal records force equal inputs on every window used to compute the restriction to F, hence equal actual image patterns. "
                    + "This injection gives the count without selecting independent output coordinates."))), DescribeRole.Theorem),
        Describe.Lean(DescribeId.Create("amenable-garden-of-eden"), DeclarationHandle.Create(Owner + "garden_of_eden"),
            H("Surjectivity is equivalent to finite-disagreement preinjectivity"), StatementSource.FromAuthor(GardenStatement),
            AssessedProvenance.FromLiterature(Source), Blocks(
                Paragraph(Text("Give G the discrete measurable structure. Assume NeBot(maxFoelner(Gᵐᵒᵖ,Measure.count)), "
                    + "where the opposite group acts by (op a) • g = g*a. For every finite S and every rule φ, "
                    + "Function.Surjective(Φ) is equivalent to finite-disagreement preinjectivity. "
                    + "The hypothesis uses the maximal counting Følner filter itself, not a chosen sequence. "
                    + "Finite and trivial groups satisfy this hypothesis; uncountable groups remain in scope. "
                    + "There is no assumption that finite-set volumes diverge.")),
                Paragraph(Text("For every finite E containing 1, finite unions of right translates give "
                    + "1 ≤ card(F*E)/card(F) ≤ 1 + Σ(e∈E) card((F*e)△F)/card(F) whenever F is nonempty. "
                    + "The maximal filter is eventually supported on finite nonempty sets, and each right boundary ratio tends to zero. "
                    + "Thus each fixed finite padding has volume ratio tending to one. "
                    + "The logarithmic packing bound converts avoidance of one C-pattern into a positive deficit independent of F.")),
                Paragraph(Text("Surjectivity realizes every finite output pattern. A finite collision would supply the replacement "
                    + "and joint-count bounds above, contradicting this full count and the padding limit. "
                    + "Conversely, preinjectivity injects arbitrary patterns on F, extended into one constant ambient configuration, "
                    + "into actual image patterns on F*({1}∪S⁻¹). Nonsurjectivity of the continuous map on the compact full product "
                    + "would give a nonempty finite missing output pattern. Left equivariance makes it missing at every left translate. "
                    + "Disjoint placements yield the same positive counting deficit and contradict the preinjective lower count. "
                    + "Product compactness applies to arbitrary G; no enumeration or sequential compactness is used.")),
                Paragraph(Text("Subsingleton alphabets are treated directly before choosing any ambient letter. "
                    + "The result therefore includes empty and singleton alphabets as well as empty neighborhoods. "
                    + "This is the classical amenable-group Moore–Myhill theorem. The multiplicative finite-pattern argument "
                    + "extends the lattice formulation while retaining the same jointly realized meaning of image patterns."))), DescribeRole.Theorem)
        )));
}
