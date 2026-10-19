using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups;

internal sealed class CyclicPrimePowerActionDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef LazorecTarnauceanu =
        LibraryNoteRef.Create("D5/L/FiniteGroups/lazorec2025subgroupconjugacy");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Actual cyclic split extensions have an exact whole-lattice and inner-conjugacy enumeration.",
        H("Cyclic Prime-Power Split Extensions"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("cyclic-prime-power-cyclic-card"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/CyclicPrimePowerAction.cyclic_card"),
                H("The cardinality of a cyclic residue group"),
                StatementSource.FromAuthor(CyclicCard()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a nonzero natural number m, the multiplicative cyclic group "
                    + "Cyclic m has cardinality m."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cyclic-prime-power-kernel-card"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/CyclicPrimePowerAction.kernel_power_card"),
                H("The power kernel has the prescribed prime-power cardinality"),
                StatementSource.FromAuthor(KernelPowerCard()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a finite cyclic commutative group P of cardinality q^s, the kernel "
                    + "of x ↦ x^(q^j) has cardinality q^j for every j from zero through s. "
                    + "Here Type* denotes a carrier in an arbitrary universe, as in Lean."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cyclic-prime-power-action"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/CyclicPrimePowerAction.actionData"),
                H("An actual action of exact prime order"),
                StatementSource.FromAuthor(Action()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Cyclic m means Multiplicative (ZMod m), with generator the additive "
                    + "residue of one. ActionData p q s contains a homomorphism from "
                    + "Cyclic (q^s) to MulAut (Cyclic p), together with the assertion that "
                    + "the image of the generator has order exactly q. For primes p and q "
                    + "with q dividing p−1 and positive s, the automorphism group has order "
                    + "p−1. Cauchy's theorem supplies an automorphism of order q. Its order "
                    + "divides q^s, so the cyclic-generator extension constructs the homomorphism. "
                    + "SplitGroup A is the actual semidirect product for this action, with "
                    + "multiplication (x,u)(y,v) = (x A(u)(y), uv). finiteSplitGroup packages "
                    + "that group and its finite carrier; it assumes no subgroup-count formula."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cyclic-prime-power-lattice"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/CyclicPrimePowerAction.cyclicSubgroupEquiv"),
                H("The entire cyclic subgroup lattice"),
                StatementSource.FromAuthor(CyclicLattice()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For a finite cyclic commutative group P of order q^s, each subgroup has "
                    + "order q^j for a unique j in Fin (s+1). A subgroup H equals the kernel "
                    + "of the homomorphism x ↦ x^(card H): inclusion follows from the "
                    + "element-order theorem, and the cyclic kernel-cardinality theorem gives "
                    + "equality. Conversely the kernel of x ↦ x^(q^j) has order q^j. "
                    + "These constructions are inverse bijections, covering every subgroup."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("cyclic-prime-power-subgroup-classification"),
                DeclarationHandle.Create(
                    "D5/S3/FiniteGroups/CyclicPrimePowerAction.subgroup_classification"),
                H("Every subgroup belongs to one of three families"),
                StatementSource.FromAuthor(Classification()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Write N = Cyclic p and P = Cyclic (q^s), with A an actual ActionData. "
                        + "For every subgroup H, the inverse image along the embedding of N "
                        + "is trivial or all of N, since N has prime order. In the latter case "
                        + "H is the inverse image of its projection to P.")),
                    Paragraph(Text(
                        "In the former case projection is injective on H. Every proper subgroup "
                        + "B of P has order q^j with j < s. It lies in the subgroup generated "
                        + "by the qth power of the generator, so A acts trivially on B. "
                        + "If H has proper projection, its left coordinate defines a homomorphism "
                        + "on H. Its element orders divide p and q^s, which are coprime. "
                        + "The left coordinate is therefore always one, and H is exactly "
                        + "the embedded copy of its projected subgroup.")),
                    Paragraph(Text(
                        "If the projection is all of P, choose in H a lift of the generator. "
                        + "A nonidentity automorphism of a prime-order group has no nonidentity "
                        + "fixed point: such a point would generate the group and force the "
                        + "automorphism to be the identity. Hence x ↦ x/A(generator)(x) "
                        + "is bijective on N. Solving this equation expresses the chosen lift "
                        + "as the conjugate of the embedded generator by some x in N. "
                        + "Projection injectivity shows that this lift generates H. Thus H is "
                        + "the corresponding conjugate of the full complement."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("cyclic-prime-power-exact-counts"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/CyclicPrimePowerAction.split_counts"),
                H("Exact lattice and orbit counts"),
                StatementSource.FromAuthor(Counts()),
                AssessedProvenance.FromLiterature(LazorecTarnauceanu),
                Blocks(
                    Paragraph(Text(
                        "subgroupEnumeration is a bijection to Subgroup P plus the proper "
                        + "subgroups of P plus N. Projection and intersection with N distinguish "
                        + "these three families. The inverse-image and embedded labels are unique. "
                        + "Distinct x in N give distinct complements, by injectivity of the "
                        + "same fixed-point-free commutator map. The family sizes are s+1, s, "
                        + "and p, giving latticeCount = 2s+p+1.")),
                    Paragraph(Text(
                        "Every inverse-image subgroup is normal because P is commutative. "
                        + "Every proper embedded subgroup is central, since its action on N "
                        + "is trivial and P is commutative. Each therefore gives a singleton "
                        + "inner-conjugacy class. All p complements are conjugate to the "
                        + "embedded P, giving one further class. classesEnumeration is a "
                        + "bijection from the quotient of the entire lattice to Subgroup P "
                        + "plus its proper subgroups plus Unit. Thus classCount = 2s+2.")),
                    Paragraph(Text(
                        "These counts are stated in the proof of Proposition 2.2(ii) of "
                        + "Lazorec and Tărnăuceanu, arXiv:2508.14267v2, equation S2.Ex12. "
                        + "Under n = s+1, N = Cyclic p and P = Cyclic (q^s), they are "
                        + "2n+p−1 and 2n. The generator action has exact order q, so it is "
                        + "nontrivial and its qth power is trivial; hence the Frattini subgroup "
                        + "of P acts trivially on N, as in Lemma 2.1(ii). The Lean proof "
                        + "establishes the published counts for every actual ActionData in "
                        + "the displayed scope. Positive s includes s=1, corresponding to n=2. "
                        + "The source count formulas are known mathematics; their formal "
                        + "proof here is not a mathematical priority claim."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] xs) =>
        new Formula.Apply(F.Id(name), [.. xs]);
    private static Formula NatCall(string member, params Formula[] xs) =>
        new Formula.Apply(Seq(Operatorname, Grp(Seq(F.Id("Nat"), Dot, F.Id(member)))), [.. xs]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll,
            [new Formula.BoundVariable(FormulaIdentifier.Create(name), type)], body);
    private static Formula Ex(string name, Formula type, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.Exists,
            [new Formula.BoundVariable(FormulaIdentifier.Create(name), type)], body);
    private static Formula Equal(Formula x, Formula y) => Seq(x, Eq, y);
    private static Formula Pow(Formula x, Formula y) => Call("power", x, y);
    private static Formula CyclicCard()
    {
        var m = F.Id("m");
        Formula body = Seq(NatCall("card", Call("Cyclic", m)), Sp, Eq, Sp, m);
        body = Seq(OpenBracket, Call("NeZero", m), CloseBracket, Sp, body);
        return Disp(All("m", Seq(Mathbb, Grp(F.Id("N"))), body));
    }

    private static Formula KernelPowerCard()
    {
        var p = F.Id("P"); var q = F.Id("q"); var s = F.Id("s");
        var j = F.Id("j");
        var exponent = new Formula.Power(q, Call("val", j));
        var hom = Parenthesized(Seq(Call("powMonoidHom", exponent), Sp, Colon, Sp,
            p, To, Star, p));
        var kernel = Call("ker", hom);
        Formula body = Seq(NatCall("card", kernel), Sp, Eq, Sp, exponent);
        body = All("j", Call("Fin", Seq(s, Plus, D(1))), body);
        var cardinalityHypothesis = Seq(NatCall("card", p), Sp, Eq, Sp,
            new Formula.Power(q, s));
        body = new Formula.Logic(cardinalityHypothesis, FormulaLogicOperator.Implies, body);
        body = All("s", Seq(Mathbb, Grp(F.Id("N"))), body);
        body = All("q", Seq(Mathbb, Grp(F.Id("N"))), body);
        body = Seq(OpenBracket, Call("CommGroup", p), CloseBracket, Sp,
            OpenBracket, Call("IsCyclic", p), CloseBracket, Sp,
            OpenBracket, Call("Finite", p), CloseBracket, Sp, body);
        return Disp(All("P", Seq(F.Id("Type"), Star), body));
    }

    private static Formula Action()
    {
        var p = F.Id("p"); var q = F.Id("q"); var s = F.Id("s");
        Formula body = Call("ActionData", p, q, s);
        body = new Formula.TypeArrow(Seq(D(0), Lt, s), body);
        body = new Formula.TypeArrow(Call("Divides", q, Seq(p, Minus, D(1))), body);
        body = new Formula.TypeArrow(Call("Prime", q), body);
        body = new Formula.TypeArrow(Call("Prime", p), body);
        return Disp(All("p", F.Id("Naturals"), All("q", F.Id("Naturals"),
            All("s", F.Id("Naturals"), body))));
    }
    private static Formula CyclicLattice()
    {
        var p = F.Id("P"); var q = F.Id("q"); var s = F.Id("s");
        Formula body = Call("Equiv", Call("Subgroup", p), Call("Fin", Seq(s, Plus, D(1))));
        body = new Formula.TypeArrow(Equal(Call("card", p), Pow(q, s)), body);
        body = new Formula.TypeArrow(Call("Prime", q), body);
        body = All("q", F.Id("Naturals"), All("s", F.Id("Naturals"), body));
        body = new Formula.TypeArrow(Call("Finite", p), body);
        body = new Formula.TypeArrow(Call("IsCyclic", p), body);
        body = new Formula.TypeArrow(Call("CommGroup", p), body);
        return Disp(All("P", F.Id("Typeu"), body));
    }
    private static Formula InSplitFamily(Formula body)
    {
        var p = F.Id("p"); var q = F.Id("q"); var s = F.Id("s"); var a = F.Id("A");
        body = new Formula.TypeArrow(Call("Coprime", p, q), body);
        body = new Formula.TypeArrow(Seq(D(0), Lt, s), body);
        body = All("A", Call("ActionData", p, q, s), body);
        body = new Formula.TypeArrow(Call("NeZero", Pow(q, s)), body);
        body = new Formula.TypeArrow(Call("Fact", Call("Prime", q)), body);
        body = new Formula.TypeArrow(Call("Fact", Call("Prime", p)), body);
        return Disp(All("p", F.Id("Naturals"), All("q", F.Id("Naturals"),
            All("s", F.Id("Naturals"), body))));
    }
    private static Formula Classification()
    {
        var p = F.Id("p"); var q = F.Id("q"); var s = F.Id("s");
        var a = F.Id("A"); var h = F.Id("H"); var b = F.Id("B"); var x = F.Id("x");
        var quotient = Call("Cyclic", Pow(q, s));
        var over = Ex("B", Call("Subgroup", quotient),
            Equal(h, Call("comap", b, Call("rightHom", a))));
        var pure = Ex("B", Call("Subgroup", quotient),
            Seq(Seq(b, Neq, Sp, Call("top")), Land, Sp,
                Equal(h, Call("map", b, Call("inr", a)))));
        var complement = Ex("x", Call("Cyclic", p),
            Equal(h, Call("map", Call("range", Call("inr", a)),
                Call("conjugation", Call("inl", a, x)))));
        return InSplitFamily(All("H", Call("Subgroup", Call("SplitGroup", a)),
            Seq(Open, over, Close, Lor, Sp, Open, pure, Close,
                Lor, Sp, Open, complement, Close)));
    }
    private static Formula Counts()
    {
        var p = F.Id("p"); var s = F.Id("s"); var a = F.Id("A");
        var group = Call("SplitGroup", a);
        return InSplitFamily(Seq(
            Equal(Call("latticeCount", group), Seq(D(2), Star, s, Plus, p, Plus, D(1))),
            Land, Sp,
            Equal(Call("classCount", group), Seq(D(2), Star, s, Plus, D(2)))));
    }
}
