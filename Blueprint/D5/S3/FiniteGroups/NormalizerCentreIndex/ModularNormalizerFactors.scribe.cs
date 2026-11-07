using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NormalizerCentreIndex;

internal sealed class ModularNormalizerFactorsDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/FiniteGroups/legarreta2010normalizers");
    private const string CountingSource = "The source writes: “If we denote respectively by s(G) and ω(G) the number of normalizers and the number of conjugacy classes of normalizers of a group G, then our problem is: for which groups G do we have s(G) = ω(G)? To be more precise, we want to focus our study in a slightly different way: for which values of ω(G) the equality s(G) = ω(G) holds true independently of the choice of the group G in a suitable class?” Printed page 1169. ";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Normalizer subgroups and their conjugacy classes multiply over coprime factors.",
        H("Coprime products and modular groups"), Blocks(
            Describe.Lean(DescribeId.Create("lstg-normalizerwitness"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NormalizerCentreIndex/ModularNormalizerFactors.NormalizerWitness"),
                H("Distinct normalizer subgroups"), StatementSource.FromAuthor(Disp(WitnessBody())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(CountingSource + "The subtype contains each normalizer once, regardless of the number of subgroups producing it."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("lstg-conjequivalent"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NormalizerCentreIndex/ModularNormalizerFactors.ConjEquivalent"),
                H("Inner conjugacy of subgroups"), StatementSource.FromAuthor(Disp(ConjugacyBody())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(CountingSource + "Two subgroups are related when conjugation by one group element identifies their membership predicates. This relation includes all elements of both subgroups."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("lstg-normalizersetoid"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NormalizerCentreIndex/ModularNormalizerFactors.normalizerSetoid"),
                H("The equivalence relation on normalizers"), StatementSource.FromAuthor(Disp(SetoidBody())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(CountingSource + "The relation is ConjEquivalent on the underlying subgroups. Identity, inversion and multiplication of conjugating elements prove reflexivity, symmetry and transitivity."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("lstg-normalizerclass"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NormalizerCentreIndex/ModularNormalizerFactors.NormalizerClass"),
                H("Conjugacy classes of normalizers"), StatementSource.FromAuthor(Disp(Gforall(Eqn(Call("NormalizerClass", X("G")), Call("Quotient", Call("normalizerSetoid", X("G"))))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(CountingSource + "The quotient identifies normalizer subgroups under inner conjugacy."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("lstg-scard"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NormalizerCentreIndex/ModularNormalizerFactors.sCard"),
                H("The number of normalizers"), StatementSource.FromAuthor(Disp(Gforall(Eqn(Call("sCard", X("G")), App(Q("Cardinal", "mk"), Call("NormalizerWitness", X("G"))))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(CountingSource + "The cardinal-valued count includes infinite sets of distinct normalizers."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("lstg-omega"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NormalizerCentreIndex/ModularNormalizerFactors.omega"),
                H("The finite normalizer-class count"), StatementSource.FromAuthor(Disp(Gforall(Eqn(Call("omega", X("G")), App(Q("Nat", "card"), Call("NormalizerClass", X("G"))))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(CountingSource + "The natural-valued count is used only when NormalizerClass is finite."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("lstg-centreindex"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NormalizerCentreIndex/ModularNormalizerFactors.centreIndex"),
                H("Index of the centre"), StatementSource.FromAuthor(Disp(Gforall(Eqn(Call("centreIndex", X("G")), App(Q("Cardinal", "mk"), Seq(X("G"), Sp, Slash, Sp, App(Q("Subgroup", "center"), X("G")))))))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Question 3.3. Let G be a group satisfying the normalizer condition, and suppose that ω(G) is finite. If s(G) > ω(G), is |G : Z(G)| ω(G)-bounded? Is this true at least for finite p-groups? Printed page 1174. This is the cardinality of the quotient by the centre, including an infinite index."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("lstg-counts-prod"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NormalizerCentreIndex/ModularNormalizerFactors.counts_prod"),
                H("Counts multiply over coprime products"), StatementSource.FromAuthor(Disp(ProductCounts())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The existing subgroup-product equivalence splits every subgroup when the finite factor orders are coprime. The normalizer of a product is the product of normalizers; conjugacy also splits. The resulting bijections give both cardinality identities."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("lstg-finite-product-classes"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NormalizerCentreIndex/ModularNormalizerFactors.finite_product_classes"),
                H("Finiteness of the product quotient"), StatementSource.FromAuthor(Disp(ProductFinite())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The product-class equivalence transports finiteness from the two factor quotients."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("lstg-modular-t"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NormalizerCentreIndex/ModularNormalizerFactors.t"),
                H("The central additive embedding"), StatementSource.FromAuthor(Disp(TBody())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Multiplication by p descends from integer residues modulo p to residues modulo p²; p times p is zero in the target."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("lstg-modular-aut"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NormalizerCentreIndex/ModularNormalizerFactors.aut"),
                H("The modular automorphism"), StatementSource.FromAuthor(Disp(AutBody())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The forward multiplier is 1 + t p a and the inverse multiplier is 1 − t p a. Their product is one because products of two values of t vanish."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("lstg-modular-action"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NormalizerCentreIndex/ModularNormalizerFactors.action"),
                H("The action of the second cyclic factor"), StatementSource.FromAuthor(Disp(ActionBody())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("An element of Multiplicative (ZMod p) acts through its additive coordinate and the automorphism aut."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("lstg-modular-p"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NormalizerCentreIndex/ModularNormalizerFactors.P"),
                H("The modular group"), StatementSource.FromAuthor(Disp(All("p", Nat(), Eqn(P(), Call("SemidirectProduct", Call("Multiplicative", R()), Call("Multiplicative", Call("ZMod", X("p"))), App(Q("Modular", "action"), X("p"))))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The semidirect product has underlying coordinates in ZMod (p²) and ZMod p. For prime p its order is p³."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("lstg-modular-finitep"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NormalizerCentreIndex/ModularNormalizerFactors.finiteP"),
                H("Finite modular carrier"), StatementSource.FromAuthor(Disp(All("p", Nat(), Instance(Call("NeZero", X("p")), Call("Finite", P()))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Finiteness is transported along SemidirectProduct.equivProd from the product of the two finite residue types."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("lstg-modular-card-p"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NormalizerCentreIndex/ModularNormalizerFactors.card_p"),
                H("Order of the modular group"), StatementSource.FromAuthor(Disp(All("p", Nat(), Instance(Call("NeZero", X("p")), Eqn(App(Q("Nat", "card"), P()), Pow(X("p"), D(3))))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The coordinate bijection gives p² times p elements."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("lstg-modular-center-card"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NormalizerCentreIndex/ModularNormalizerFactors.center_card"),
                H("Order of the centre"), StatementSource.FromAuthor(Disp(PrimeAll(Eqn(App(Q("Nat", "card"), App(Q("Subgroup", "center"), P())), X("p"))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The centre consists of coordinates (t p u, 0), with u in ZMod p. Injectivity of t gives exactly p central elements."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("lstg-modular-s-card"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NormalizerCentreIndex/ModularNormalizerFactors.s_card"),
                H("Two normalizer subgroups"), StatementSource.FromAuthor(Disp(OddAll(Eqn(Call("sCard", P()), D(2))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("A subgroup containing the central order-p subgroup, or contained in it, has whole-group normalizer. Every remaining subgroup has the elementary abelian subgroup of first coordinate divisible by p as its normalizer. Both normalizers occur."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("lstg-modular-omega-card"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NormalizerCentreIndex/ModularNormalizerFactors.omega_card"),
                H("Two normalizer conjugacy classes"), StatementSource.FromAuthor(Disp(OddAll(Eqn(Call("omega", P()), D(2))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("Both normalizer subgroups are normal, so each is its own conjugacy class."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("lstg-modular-finite-classes"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NormalizerCentreIndex/ModularNormalizerFactors.finite_classes"),
                H("Finite normalizer quotient"), StatementSource.FromAuthor(Disp(OddAll(Call("Finite", Call("NormalizerClass", P()))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text("The explicit quotient equivalence with Fin 2 proves finiteness."))), DescribeRole.Theorem))));

    private static Formula X(string name) => F.Id(name);
    private static Formula Q(string owner, string name) => Seq(Operatorname, Grp(X(owner)), Dot, Operatorname, Grp(X(name)));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(X(name), [.. args]);
    private static Formula App(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula All(string name, Formula type, Formula body) => new Formula.BindMany(FormulaQuantifier.ForAll,
        [new Formula.BoundVariable(FormulaIdentifier.Create(name), type)], body);
    private static Formula Ex(string name, Formula type, Formula body) => new Formula.BindMany(FormulaQuantifier.Exists,
        [new Formula.BoundVariable(FormulaIdentifier.Create(name), type)], body);
    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.And, Parenthesized(b));
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Parenthesized(a), FormulaLogicOperator.Implies, Parenthesized(b));
    private static Formula Instance(Formula type, Formula body) => Seq(OpenBracket, type, CloseBracket, Sp, body);
    private static Formula Cast(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Pow(Formula a, Formula b) => new Formula.Power(a, b);
    private static Formula Nat() => Seq(Mathbb, Grp(X("N")));
    private static Formula Mul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula Gforall(Formula body) => All("G", X("Type"), Instance(Call("Group", X("G")), body));

    private static Formula R() => Call("ZMod", Pow(X("p"), D(2)));
    private static Formula P() => App(Q("Modular", "P"), X("p"));
    private static Formula PrimeAll(Formula body) => All("p", Nat(), Instance(Call("Fact", App(Q("Nat", "Prime"), X("p"))), body));
    private static Formula OddAll(Formula body) => PrimeAll(Imp(Seq(X("p"), Neq, Sp, D(2)), body));
    private static Formula WitnessBody()
    {
        var g = X("G"); var n = X("N"); var h = X("H");
        return Gforall(Eqn(Call("NormalizerWitness", g), Seq(OpenBrace, n, Colon, Sp, Call("Subgroup", g), Sp, Mid,
            Ex("H", Call("Subgroup", g), Eqn(n, App(Q("Subgroup", "normalizer"), Cast(h, Call("Set", g))))), CloseBrace)));
    }
    private static Formula ConjugacyBody()
    {
        var g = X("G"); var a = X("A"); var b = X("B"); var x = X("x"); var z = X("g");
        return Gforall(All("A", Call("Subgroup", g), All("B", Call("Subgroup", g),
            Eqn(Call("ConjEquivalent", a, b), Ex("g", g, All("x", g,
                Seq(x, InMacro, Sp, a, Sp, Iff, Sp, Mul(Mul(z, x), Pow(z, Seq(Minus, D(1)))), InMacro, Sp, b)))))));
    }
    private static Formula SetoidBody()
    {
        var g = X("G"); var a = X("A"); var b = X("B");
        var relation = Parenthesized(Seq(X("fun"), Sp, Parenthesized(Seq(a, Sp, b, Colon, Sp,
            Call("NormalizerWitness", g))), Sp, Mapsto, Sp,
            Call("ConjEquivalent", Call("val", a), Call("val", b))));
        return Gforall(All("h", Call("Equivalence", relation),
            Eqn(Call("normalizerSetoid", g), App(Q("Setoid", "mk"), relation, X("h")))));
    }
    private static Formula Products(Formula body) => Gforall(All("K", X("Type"), Instance(Call("Group", X("K")),
        Instance(Call("Finite", X("G")), Instance(Call("Finite", X("K")),
            Imp(App(Q("Nat", "Coprime"), App(Q("Nat", "card"), X("G")), App(Q("Nat", "card"), X("K"))), body))))));
    private static Formula ProductCounts()
    {
        var g = X("G"); var k = X("K"); var product = Seq(g, Sp, Times, Sp, k);
        return Products(And(Eqn(Call("sCard", product), Mul(Call("sCard", g), Call("sCard", k))),
            Eqn(Call("omega", product), Mul(Call("omega", g), Call("omega", k)))));
    }
    private static Formula ProductFinite() => Products(
        Instance(Call("Finite", Call("NormalizerClass", X("G"))), Instance(Call("Finite", Call("NormalizerClass", X("K"))),
            Call("Finite", Call("NormalizerClass", Seq(X("G"), Sp, Times, Sp, X("K")))))));
    private static Formula TBody()
    {
        var p = X("p"); var h = X("h");
        var baseMap = App(Q("AddMonoidHom", "comp"), App(Q("AddMonoidHom", "mulLeft"), Cast(p, R())),
            App(Q("Int", "castAddHom"), R()));
        return All("p", Nat(), All("h", Eqn(App(baseMap, Cast(p, new Formula.Integers())), D(0)),
            Eqn(App(Q("Modular", "t"), p), App(Q("ZMod", "lift"), p,
                Seq(Langle, baseMap, Comma, Sp, h, Rangle)))));
    }
    private static Formula AutBody()
    {
        var p = X("p"); var a = X("a"); var ta = App(Q("Modular", "t"), p, a);
        var forward = Parenthesized(Seq(D(1), Plus, ta));
        var inverse = Parenthesized(Seq(D(1), Minus, ta));
        var unit = Cast(Seq(Langle, forward, Comma, Sp, inverse, Comma, Sp, X("h"), Comma, Sp, X("k"), Rangle),
            Pow(R(), Seq(Star)));
        var addAut = App(Q("AddAut", "mulLeft"), unit);
        return All("p", Nat(), All("a", Call("ZMod", p),
            All("h", Eqn(Mul(forward, inverse), D(1)), All("k", Eqn(Mul(inverse, forward), D(1)),
                Eqn(App(Q("Modular", "aut"), p, a), App(Q("AddEquiv", "toMultiplicative"),
                    App(Q("Multiplicative", "toAdd"), addAut)))))));
    }
    private static Formula ActionBody()
    {
        var p = X("p"); var a = X("a"); var b = X("b");
        var carrier = Call("Multiplicative", Call("ZMod", p));
        Formula Value(Formula x) => App(Q("Modular", "aut"), p, App(Q("Multiplicative", "toAdd"), x));
        var function = Parenthesized(Seq(X("fun"), Sp, Parenthesized(Seq(a, Colon, Sp, carrier)), Sp, Mapsto, Sp, Value(a)));
        var oneLaw = Eqn(Value(D(1)), D(1));
        var mulLaw = All("a", carrier, All("b", carrier, Eqn(Value(Mul(a, b)), Mul(Value(a), Value(b)))));
        return All("p", Nat(), All("h", oneLaw, All("k", mulLaw,
            Eqn(App(Q("Modular", "action"), p), App(Q("MonoidHom", "mk"),
                App(Q("OneHom", "mk"), function, X("h")), X("k"))))));
    }
}
