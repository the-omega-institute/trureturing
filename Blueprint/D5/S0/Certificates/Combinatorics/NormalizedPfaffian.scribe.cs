using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Certificates.Combinatorics;

internal sealed class NormalizedPfaffianDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The original normalized Pfaffian pair-listing core and its counted crossing convention bridge over arbitrary commutative rings.",
        H("Normalized Pfaffian listings and counted crossing convention"),
        Blocks(
Describe.Lean(DescribeId.Create("partner-map"),
            DeclarationHandle.Create("D5/S0/Certificates/Combinatorics/NormalizedPfaffian.P"),
            H("Involutive partner maps"), StatementSource.FromAuthor(PairDefinition()),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("For each natural k, P(k) consists of all functions on Fin(2k) that square to the identity and have no fixed points. The two-element orbits form the unordered pairs. The empty function is included when k is zero."))),
            DescribeRole.Definition),
Describe.Lean(DescribeId.Create("pfaffian"),
            DeclarationHandle.Create("D5/S0/Certificates/Combinatorics/NormalizedPfaffian.pfaffian"),
            H("The Pfaffian over a commutative ring"), StatementSource.FromAuthor(NormDefinition()),
            AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text("Let R be any commutative ring and A a matrix on Fin(2n). A permutation sigma is normalized when each pair sigma(2i), sigma(2i+1) is increasing and the first endpoints increase with i. The set L(n) below contains precisely these permutations. The coefficient is the integer value of the permutation sign, cast into R. Every pairing is permitted independently of any graph or weights. No division by a factorial or a power of two occurs. For n = 0 the unique empty permutation contributes the empty product, which is one. The convention agrees with the normalized partitions in Ishikawa and Koutschan, Zeilberger's holonomic ansatz for Pfaffians, arXiv:1201.5253v2."))),
            DescribeRole.Definition),

            Describe.Lean(DescribeId.Create("canonical-mate"),
                DeclarationHandle.Create("D5/S0/Certificates/Combinatorics/NormalizedPfaffian.canonical_mate"),
                H("Canonical slots are partners"), StatementSource.FromAuthor(CanonMate()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A partner map p on Fin(2n) is involutive and has no fixed point. Choose its lower endpoints x < p(x), enumerate them increasingly, and put each x immediately before p(x). Exactly n lower endpoints occur: applying p exchanges the lower endpoints with their complement. The resulting flattening is a bijection c(p). Thus it is a genuine permutation, including when n = 0. Its increasing pairs are ordered by their first endpoints."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("listing-equivalence"),
                DeclarationHandle.Create("D5/S0/Certificates/Combinatorics/NormalizedPfaffian.listingEquiv"),
                H("Every pairing occurs once"), StatementSource.FromAuthor(CanonEquivalence()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Conjugating the consecutive partner map by a listing s gives pairingOfListing(s). The canonical listing of this partner map is s whenever s satisfies the normalized-listing inequalities. Conversely, conjugation by c(p) recovers p. These inverse constructions give a bijection from all normalized listing permutations to P(n). The enumeration is independent of a graph, edge support, orientation or weights."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("listing-normalization"),
                DeclarationHandle.Create("D5/S0/Certificates/Combinatorics/NormalizedPfaffian.listing_value_canonical"),
                H("Signed normalization"), StatementSource.FromAuthor(CanonNormalization()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("Let f(x,y) be an integer unit for every pair of labels, with f(y,x) = -f(x,y) whenever x and y differ. Define L(f,s) as sign(s) times the product of f(s(2i),s(2i+1)) over i in Fin(n). The value uses integer units throughout.")),
                    Paragraph(Text("To normalize s, sort its unordered pairs by their smaller endpoints and reverse each decreasing pair. The whole-pair permutation acts on two copies of Fin(n), so its sign is the square of a sign and equals one. Each individual reversal contributes one transposition and negates exactly its paired factor. The two signs cancel. Reindexing the finite product by the pair permutation proves the displayed equality without dividing by a ring element or excluding an empty pairing."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("listing-partners"),
                DeclarationHandle.Create("D5/S0/Certificates/Combinatorics/NormalizedPfaffian.pairing_eq_iff"),
                H("Recognizing a partner map"), StatementSource.FromAuthor(CanonPartners()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A permutation lists a given partner map if and only if each pair of consecutive slots has that partner relation. The forward implication is conjugation of the consecutive pairing. For the reverse implication, every slot is either the first or the second slot of one pair. The first slots satisfy the stated equation, and involutivity determines the second slots. This criterion connects arbitrary listings to actual matching adjacency."))),
                DescribeRole.Theorem),

            Describe.Lean(DescribeId.Create("normalized-pfaffian-count-inversion-pairs"),
                DeclarationHandle.Create("D5/S0/Certificates/Combinatorics/NormalizedPfaffian.inversionPairs"), H("Listing inversion pairs"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a permutation of Fin(2*n), this finite set contains exactly the position pairs u<v with s(v)<s(u). It is the inversion statistic of the listing itself."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("normalized-pfaffian-count-lower-endpoints"),
                DeclarationHandle.Create("D5/S0/Certificates/Combinatorics/NormalizedPfaffian.lowerEndpoints"), H("Lower endpoints of a pairing"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a fixed point free pairing p, this finite set contains every a with a<p(a), so each edge is represented exactly once by its lower endpoint."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("normalized-pfaffian-count-crossing-pairs"),
                DeclarationHandle.Create("D5/S0/Certificates/Combinatorics/NormalizedPfaffian.crossingPairs"), H("Crossing edge pairs"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("CrossingPairs p contains ordered lower endpoints a<c satisfying a<c<p(a)<p(c)."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("normalized-pfaffian-count-nesting-pairs"),
                DeclarationHandle.Create("D5/S0/Certificates/Combinatorics/NormalizedPfaffian.nestingPairs"), H("Nested edge pairs"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("NestingPairs p contains ordered lower endpoints a<c satisfying a<c<p(c)<p(a), with each unordered nested edge pair counted once."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("normalized-pfaffian-count-inversion-equivalence"),
                DeclarationHandle.Create("D5/S0/Certificates/Combinatorics/NormalizedPfaffian.inversionCrossNestEquiv"), H("Crossing and two-way nesting equivalence"),
                StatementSource.FromAuthor(CountEquivalence()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every normalized listing s, with p=pairingOfListing s, the explicit inverse maps InvType s to CrossType p or to NestType p together with Fin 2. The three cases are (second i, first j) crossing, (second i, first j) nesting orientation zero, and (second i, second j) nesting orientation one; both inverse laws are proved."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("normalized-pfaffian-count-card"),
                DeclarationHandle.Create("D5/S0/Certificates/Combinatorics/NormalizedPfaffian.inversion_card_eq_cross_add_two_nesting_card"), H("Inversion cardinality identity"),
                StatementSource.FromAuthor(CountIdentity()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The equivalence gives the exact finite identity card(Inv)=card(Cross)+2*card(Nest), including n=0 and the empty listing."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("normalized-pfaffian-count-crossing-unit"),
                DeclarationHandle.Create("D5/S0/Certificates/Combinatorics/NormalizedPfaffian.crossingUnit"), H("Crossing sign unit"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The crossing unit is the integer sign unit (-1) raised to the cardinality of the crossing-pair subtype."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("normalized-pfaffian-count-crossing-coefficient"),
                DeclarationHandle.Create("D5/S0/Certificates/Combinatorics/NormalizedPfaffian.crossingCoefficient"), H("Crossing coefficient in a commutative ring"),
                StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("CrossingCoefficient casts the integer value of crossingUnit into an arbitrary CommRing coefficient type."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("normalized-pfaffian-count-pfaffian-crossing-sum"),
                DeclarationHandle.Create("D5/S0/Certificates/Combinatorics/NormalizedPfaffian.pfaffian_eq_crossing_sum"), H("Original Pfaffian equals the independent crossing-signed edge-once sum"),
                StatementSource.FromAuthor(CrossingIdentity()), AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every n, every commutative ring R, and every matrix A over R, the original normalized Pfaffian sum is equal term by term to the sum over the same normalized listings whose coefficient is (-1) raised to the number of crossing edge pairs and whose product ranges over lowerEndpoints(pairingOfListing s), using each paired matrix entry once. The proof uses the pinned permutation-sign product formula, the counted equivalence, the original listing normalization, and no skew-symmetry, division, cancellation, or integer-only specialization."))), DescribeRole.Theorem)
        )));

    private static Formula PairCall(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula PairAll(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula PairEq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula PairBoth(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula PairNat => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula PairFin(Formula n) => PairCall("Fin", n);
    private static Formula PairTimes(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula PairDefinition()
    {
        Formula k = F.Id("k"), p = F.Id("p"), x = F.Id("x");
        Formula labels = PairFin(PairTimes(D(2), k));
        Formula conditions = PairBoth(PairAll("x", labels, PairEq(PairCall("Apply", p, PairCall("Apply", p, x)), x)),
            PairAll("x", labels, new Formula.Relation(PairCall("Apply", p, x), FormulaRelationOperator.NotEqual, x)));
        return Disp(PairAll("k", PairNat, PairEq(PairCall("P", k), Seq(OpenBrace, p, Colon,
            new Formula.TypeArrow(labels, labels), Sp, Mid, Sp, conditions, CloseBrace))));
    }

    private static Formula NormCall(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula NormAll(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula NormEq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula NormLt(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.LessThan, b);
    private static Formula NormBoth(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula NormImp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula NormNat => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula NormType => NormCall("Type");
    private static Formula NormFin(Formula n) => NormCall("Fin", n);
    private static Formula NormTimes(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula NormAdd(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula NormDefinition()
    {
        Formula r = F.Id("R"), n = F.Id("n"), a = F.Id("A"), s = F.Id("sigma"), i = F.Id("i"), j = F.Id("j");
        Formula labels = NormFin(NormTimes(D(2), n));
        Formula first = NormCall("Apply", s, NormTimes(D(2), i));
        Formula second = NormCall("Apply", s, NormAdd(NormTimes(D(2), i), D(1)));
        Formula normalized = NormBoth(NormAll("i", NormFin(n), NormLt(first, second)),
            NormAll("i", NormFin(n), NormAll("j", NormFin(n), NormImp(NormLt(i, j), NormLt(first, NormCall("Apply", s, NormTimes(D(2), j)))))));
        Formula listings = Seq(OpenBrace, s, Colon, NormCall("Perm", labels), Sp, Mid, Sp, normalized, CloseBrace);
        Formula product = Seq(new Formula.Subscript(Prod, Seq(i, Sp, InMacro, Sp, NormFin(n))), Sp,
            NormCall("Apply", a, first, second));
        Formula sum = Seq(new Formula.Subscript(Sum, Seq(s, Sp, InMacro, Sp, listings)), Sp,
            NormTimes(NormCall("intCast", NormCall("sign", s)), product));
        return Disp(NormAll("R", NormType, Seq(OpenBracket, NormCall("CommRing", r), CloseBracket, Sp,
            NormAll("n", NormNat, NormAll("A", NormCall("Matrix", labels, labels, r), NormEq(NormCall("pfaffian", a), sum))))));
    }

    private static Formula CanonCall(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. args]);
    private static Formula CanonAll(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula CanonEq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula CanonNe(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula CanonImp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
    private static Formula CanonNat => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula CanonMul(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Multiply, b);
    private static Formula CanonAdd(Formula a, Formula b) => new Formula.Binary(a, FormulaBinaryOperator.Add, b);
    private static Formula CanonLabels(Formula n) => CanonCall("Fin", CanonMul(D(2), n));
    private static Formula CanonMate()
    {
        Formula n = F.Id("n"), p = F.Id("p"), i = F.Id("i"), c = CanonCall("canonicalListing", p);
        return Disp(CanonAll("n", CanonNat, CanonAll("p", CanonCall("P", n), CanonAll("i", CanonCall("Fin", n),
            CanonEq(CanonCall("Apply", p, CanonCall("Apply", c, CanonMul(D(2), i))),
                CanonCall("Apply", c, CanonAdd(CanonMul(D(2), i), D(1))))))));
    }
    private static Formula CanonEquivalence()
    {
        Formula n = F.Id("n");
        return Disp(CanonAll("n", CanonNat, CanonEq(CanonCall("TypeOf", CanonCall("listingEquiv", n)),
            CanonCall("Equiv", CanonCall("normalizedListings", n), CanonCall("P", n)))));
    }
    private static Formula CanonNormalization()
    {
        Formula n = F.Id("n"), f = F.Id("f"), s = F.Id("s"), x = F.Id("x"), y = F.Id("y");
        Formula skew = CanonAll("x", CanonLabels(n), CanonAll("y", CanonLabels(n), CanonImp(CanonNe(x, y),
            CanonEq(CanonCall("Apply", f, y, x), new Formula.Negate(CanonCall("Apply", f, x, y))))));
        return Disp(CanonAll("n", CanonNat, CanonAll("f", CanonCall("Function", CanonLabels(n), CanonLabels(n), CanonCall("IntegerUnits")),
            CanonAll("s", CanonCall("Perm", CanonLabels(n)), CanonImp(skew,
                CanonEq(CanonCall("listingValue", f, s),
                    CanonCall("listingValue", f, CanonCall("canonicalListing", CanonCall("pairingOfListing", s)))))))));
    }
    private static Formula CanonPartners()
    {
        Formula n = F.Id("n"), p = F.Id("p"), s = F.Id("s"), i = F.Id("i");
        Formula pairs = CanonAll("i", CanonCall("Fin", n),
            CanonEq(CanonCall("Apply", p, CanonCall("Apply", s, CanonMul(D(2), i))),
                CanonCall("Apply", s, CanonAdd(CanonMul(D(2), i), D(1)))));
        return Disp(CanonAll("n", CanonNat, CanonAll("s", CanonCall("Perm", CanonLabels(n)), CanonAll("p", CanonCall("P", n),
            new Formula.Logic(CanonEq(CanonCall("pairingOfListing", s), p), FormulaLogicOperator.Iff, pairs)))));
    }

    private static Formula CountStatement(Formula conclusion)
    {
        Formula n = F.Id("n"), s = F.Id("sigma");
        Formula member = new Formula.Relation(s, FormulaRelationOperator.MemberOf, NormCall("normalizedListings", n));
        return Disp(NormAll("n", NormNat, NormAll("sigma", NormCall("Perm", CanonLabels(n)),
            NormImp(member, conclusion))));
    }
    private static Formula CountEquivalence()
    {
        Formula s = F.Id("sigma"), p = NormCall("pairingOfListing", s);
        return CountStatement(NormCall("Equiv", NormCall("InvType", s),
            NormCall("Sum", NormCall("CrossType", p),
                NormCall("Prod", NormCall("NestType", p), NormFin(D(2))))));
    }
    private static Formula CountIdentity()
    {
        Formula s = F.Id("sigma"), p = NormCall("pairingOfListing", s);
        return CountStatement(NormEq(NormCall("FintypeCard", NormCall("InvType", s)),
            NormAdd(NormCall("FintypeCard", NormCall("CrossType", p)),
                NormTimes(D(2), NormCall("FintypeCard", NormCall("NestType", p))))));
    }
    private static Formula CrossingIdentity()
    {
        Formula n = F.Id("n"), r = F.Id("R"), a = F.Id("A"), s = F.Id("sigma"), x = F.Id("x");
        Formula p = NormCall("pairingOfListing", s), labels = CanonLabels(n);
        Formula product = Seq(new Formula.Subscript(Prod,
            Seq(x, Sp, InMacro, Sp, NormCall("lowerEndpoints", p))), Sp,
            NormCall("Apply", a, x, NormCall("Apply", p, x)));
        Formula sum = Seq(new Formula.Subscript(Sum,
            Seq(s, Sp, InMacro, Sp, NormCall("normalizedListings", n))), Sp,
            NormTimes(NormCall("crossingCoefficient", p), product));
        return Disp(NormAll("n", NormNat, NormAll("R", NormType,
            Seq(OpenBracket, NormCall("CommRing", r), CloseBracket, Sp,
                NormAll("A", NormCall("Matrix", labels, labels, r), NormEq(NormCall("pfaffian", a), sum))))));
    }
}
