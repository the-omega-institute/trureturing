using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.CoxeterMagic;

internal sealed class ElekMagicWordConverseRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/FiniteGroups/CoxeterMagic/ElekMagicWordConverseRefutation.";
    private static readonly LibraryNoteRef Elek =
        LibraryNoteRef.Create("D5/L/FiniteGroups/elek2026magicwords");
    private static readonly LibraryNoteRef BjornerBrenti =
        LibraryNoteRef.Create("D5/L/FiniteGroups/bjornerbrenti2005bruhat");
    private static readonly LibraryNoteRef Umutabazi =
        LibraryNoteRef.Create("D5/L/FiniteGroups/umutabazi2022zircons");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A crystallographic type B₂ Boolean Bruhat interval has no magic word.",
        H("A Boolean Bruhat interval with no magic word"),
        Blocks(
            Definition("cartanExponent", "Braid exponent from a Cartan product",
                CartanExponentFormula(), AssessedProvenance.FromRepo(Elek),
                "The input is an integer and the output is a natural number. Output zero encodes "
                    + "infinite braid exponent. Cartan products off the diagonal are nonnegative."),
            Definition("CartanOrigin", "Cartan origin of a Coxeter matrix",
                CartanOriginFormula(), AssessedProvenance.FromRepo(Elek),
                "The index type S is finite. The integral matrix A has diagonal entries two, "
                    + "nonpositive off-diagonal entries and symmetric zero support. Off the "
                    + "diagonal its entry products determine the braid exponents of M."),
            Definition("retained", "Letters selected by a positional mask",
                RetainedFormula(), AssessedProvenance.FromRepo(Elek),
                "The result is a list on S. Square brackets with no entries denote the empty list. "
                    + "Each step pairs a letter with a Boolean, retaining the letter exactly when "
                    + "the Boolean is true. Recursion stops when either list is exhausted."),
            Definition("positionalProduct", "Product of selected letters",
                PositionalProductFormula(), AssessedProvenance.FromRepo(Elek),
                "The Coxeter system multiplies the simple reflections at the retained positions "
                    + "in their original order. The empty list has product the group identity. "
                    + "The length condition for a mask is imposed by MaskFor."),
            Definition("MaskFor", "Masks of the required length and product",
                MaskForFormula(), AssessedProvenance.FromRepo(Elek),
                "There is one Boolean entry per letter of Q, and the retained product is u. "
                    + "Distinct masks can have the same product, including when some retained "
                    + "words are nonreduced."),
            Definition("BruhatLE", "Bruhat comparison by subwords",
                BruhatLEFormula(), AssessedProvenance.FromLiterature(BjornerBrenti),
                "Björner and Brenti’s subword criterion uses a reduced expression of the "
                    + "upper element and a reduced subword for the lower element. The deletion "
                    + "condition can shorten any retained word to a reduced subword with the same "
                    + "product, so the existence tests coincide."),
            Definition("BruhatInterval", "The full Bruhat interval",
                BruhatIntervalFormula(), AssessedProvenance.FromRepo(BjornerBrenti),
                "The braces denote the subtype of W containing every element satisfying both "
                    + "Bruhat comparisons."),
            Definition("IsHypercube", "Boolean order on the interval",
                IsHypercubeFormula(), AssessedProvenance.FromLiterature(Elek),
                "The equivalence f is a bijection from the full interval to the finite subsets "
                    + "of Fin n. Subtype.val takes an interval element to its underlying group "
                    + "element. The bijection preserves and reflects order for every pair."),
            Definition("MagicFor", "A magic word for the interval",
                MagicForFormula(), AssessedProvenance.FromLiterature(Elek),
                "Q is reduced and has product w. Exactly one length-matched Boolean mask has "
                    + "product v. The count includes masks with nonreduced retained words."),
            Describe.Lean(
                DescribeId.Create("elek-magic-word-converse-claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("Elek’s Conjecture 3.3"),
                StatementSource.FromAuthor(Disp(ClaimFormula())),
                AssessedProvenance.FromLiterature(Elek),
                Blocks(
                    Paragraph(Text("“A Bruhat interval [v,w] is a hypercube if and only if "
                        + "there exists a magic word Q for [v,w].”")),
                    Paragraph(Text("The Cartan-origin hypothesis represents the Kac–Moody "
                        + "Weyl-group setting. The group itself may be infinite. The comparison "
                        + "hypothesis restricts the claim to pairs v ≤ w.")),
                    Paragraph(Text("In sts the masks 000 and 101 both give the identity, and "
                        + "101 retains the nonreduced word ss. Deletion preserves the existence "
                        + "of a product and can change the number of masks."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("elek-magic-word-converse-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The type B₂ counterexample"),
                StatementSource.FromAuthor(Disp(new Formula.Not(F.Id("claim")))),
                AssessedProvenance.FromRepo(Elek, BjornerBrenti, Umutabazi),
                Blocks(
                    Paragraph(Text("Use the canonical presentation with simple reflections s,t "
                        + "and braid exponent four, induced by the type B₂ Cartan matrix. "
                        + "The homomorphism to the dihedral group of order eight sends s and t to "
                        + "two adjacent reflections. Testing words through length three under "
                        + "this map and using a shortest word in the presentation gives "
                        + "length(sts) = 3 and forces sts as its only reduced expression.")),
                    Paragraph(Text("The subword products below sts are e, s, t, st, ts and sts. "
                        + "Exactly s, st, ts and sts are above s. The Bruhat comparisons on "
                        + "these four elements agree in both directions with subset inclusion "
                        + "under the map to the empty set, {0}, {1} and {0,1}, respectively.")),
                    Paragraph(Text("The masks 100 and 001 retain different positions of the "
                        + "only reduced word sts and both give s. The Boolean-to-magic implication "
                        + "therefore fails. Umutabazi uses the same interval for a left-descent "
                        + "criterion. Elek’s Lemma 2.17 gives the related last-letter obstruction "
                        + "to uniqueness even among reduced subwords."))),
                DescribeRole.Theorem))));

    private static DocumentBlock.Describe Definition(
        string name, string title, Formula formula, AssessedProvenance provenance, string explanation) =>
        Describe.Lean(
            DescribeId.Create("elek-magic-word-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name),
            H(title),
            StatementSource.FromAuthor(Disp(formula)),
            provenance,
            Blocks(Paragraph(Text(explanation))),
            DescribeRole.Definition);

    private static Formula CartanExponentFormula()
    {
        var a = F.Id("a");
        var exceptional = new Formula.SetLiteral([D(0), D(1), D(2), D(3)]);
        return new Formula.Aligned([
            Equal(Call("cartanExponent", D(0)), D(2)),
            Equal(Call("cartanExponent", D(1)), D(3)),
            Equal(Call("cartanExponent", D(2)), D(4)),
            Equal(Call("cartanExponent", D(3)), D(6)),
            All("a", new Formula.Integers(),
                Implies(new Formula.Not(Parenthesized(Relation(a, FormulaRelationOperator.MemberOf, exceptional))),
                    Equal(Call("cartanExponent", a), D(0)))),
        ]);
    }

    private static Formula CartanOriginFormula()
    {
        var s = F.Id("S");
        var m = F.Id("M");
        var a = F.Id("A");
        var i = F.Id("i");
        var j = F.Id("j");
        var aij = Apply(a, i, j);
        var aji = Apply(a, j, i);
        var diagonal = All("i", s, Equal(Apply(a, i, i), D(2)));
        var exponent = Call("cartanExponent", new Formula.Binary(aij, FormulaBinaryOperator.Multiply, aji));
        var zeroSupport = Logic(Equal(aij, D(0)), FormulaLogicOperator.Iff, Equal(aji, D(0)));
        var offDiagonalEntries = And(Relation(aij, FormulaRelationOperator.LessThanOrEqual, D(0)),
            And(zeroSupport, Equal(Apply(m, i, j), exponent)));
        var offDiagonal = All("i", s, All("j", s,
            Implies(Relation(i, FormulaRelationOperator.NotEqual, j), offDiagonalEntries)));
        var matrix = ExistsIn("A", Call("Matrix", s, s, new Formula.Integers()),
            And(diagonal, offDiagonal));
        return All("S", F.Id("Type"), All("M", Call("CoxeterMatrix", s),
            IffWith(Call("CartanOrigin", m), And(Call("Finite", s), matrix))));
    }

    private static Formula RetainedFormula()
    {
        var s = F.Id("S");
        var i = F.Id("i");
        var q = F.Id("Q");
        var mask = F.Id("mask");
        var word = Call("List", s);
        var empty = Seq(OpenBracket, CloseBracket);
        var nonemptyWord = Qualified("List", "cons", i, q);
        var tail = Call("retained", q, mask);
        return All("S", F.Id("Type"), Parenthesized(new Formula.Aligned([
            All("mask", Masks, Equal(Call("retained", empty, mask), empty)),
            All("i", s, All("Q", word, Equal(Call("retained", nonemptyWord, empty), empty))),
            All("i", s, All("Q", word, All("mask", Masks,
                Equal(Call("retained", nonemptyWord, Qualified("List", "cons", F.Id("true"), mask)),
                    Qualified("List", "cons", i, tail))))),
            All("i", s, All("Q", word, All("mask", Masks,
                Equal(Call("retained", nonemptyWord, Qualified("List", "cons", F.Id("false"), mask)),
                    tail)))),
        ])));
    }

    private static Formula PositionalProductFormula()
    {
        var cs = F.Id("cs");
        var q = F.Id("Q");
        var mask = F.Id("mask");
        return InCoxeterSystem(All("Q", Words, All("mask", Masks,
            Equal(Call("positionalProduct", cs, q, mask), WordProduct(cs, Call("retained", q, mask))))));
    }

    private static Formula MaskForFormula()
    {
        var cs = F.Id("cs");
        var q = F.Id("Q");
        var u = F.Id("u");
        var mask = F.Id("mask");
        var sameLength = Equal(Qualified("List", "length", mask), Qualified("List", "length", q));
        var targetProduct = Equal(Call("positionalProduct", cs, q, mask), u);
        return InCoxeterSystem(All("Q", Words, All("u", F.Id("W"), All("mask", Masks,
            IffWith(Call("MaskFor", cs, q, u, mask), And(sameLength, targetProduct))))));
    }

    private static Formula BruhatLEFormula()
    {
        var cs = F.Id("cs");
        var u = F.Id("u");
        var w = F.Id("w");
        var q = F.Id("Q");
        var hasMask = ExistsIn("mask", Masks, Call("MaskFor", cs, q, u, F.Id("mask")));
        var upperWord = And(Qualified("CoxeterSystem", "IsReduced", cs, q),
            And(Equal(WordProduct(cs, q), w), hasMask));
        return InCoxeterSystem(All("u", F.Id("W"), All("w", F.Id("W"),
            IffWith(Call("BruhatLE", cs, u, w), ExistsIn("Q", Words, upperWord)))));
    }

    private static Formula BruhatIntervalFormula()
    {
        var cs = F.Id("cs");
        var u = F.Id("u");
        var v = F.Id("v");
        var w = F.Id("w");
        var subtype = Seq(OpenBrace, u, Colon, Sp, F.Id("W"), Sp, Mid, Sp,
            And(Call("BruhatLE", cs, v, u), Call("BruhatLE", cs, u, w)), CloseBrace);
        return OnEndpoints(Equal(Call("BruhatInterval", cs, v, w), subtype));
    }

    private static Formula IsHypercubeFormula()
    {
        var cs = F.Id("cs");
        var v = F.Id("v");
        var w = F.Id("w");
        var x = F.Id("x");
        var y = F.Id("y");
        var f = F.Id("f");
        var interval = Call("BruhatInterval", cs, v, w);
        var subsets = Call("Finset", Call("Fin", F.Id("n")));
        var pairwise = All("x", interval, All("y", interval,
            Logic(Call("BruhatLE", cs, Qualified("Subtype", "val", x), Qualified("Subtype", "val", y)),
                FormulaLogicOperator.Iff, Relation(Apply(f, x), FormulaRelationOperator.SubsetOf, Apply(f, y)))));
        return OnEndpoints(IffWith(Call("IsHypercube", cs, v, w),
            ExistsIn("n", Seq(Mathbb, Grp(F.Id("N"))),
                ExistsIn("f", Call("Equiv", interval, subsets), pairwise))));
    }

    private static Formula MagicForFormula()
    {
        var cs = F.Id("cs");
        var v = F.Id("v");
        var w = F.Id("w");
        var q = F.Id("Q");
        var mask = F.Id("mask");
        var other = F.Id("other");
        var uniqueMask = ExistsIn("mask", Masks,
            And(Call("MaskFor", cs, q, v, mask),
                All("other", Masks, Implies(Call("MaskFor", cs, q, v, other), Equal(other, mask)))));
        return OnEndpoints(All("Q", Words, IffWith(Call("MagicFor", cs, v, w, q),
            And(Qualified("CoxeterSystem", "IsReduced", cs, q),
                And(Equal(WordProduct(cs, q), w), uniqueMask)))));
    }

    private static Formula ClaimFormula()
    {
        var cs = F.Id("cs");
        var v = F.Id("v");
        var w = F.Id("w");
        var hasMagicWord = ExistsIn("Q", Words, Call("MagicFor", cs, v, w, F.Id("Q")));
        var equivalence = IffWith(Call("IsHypercube", cs, v, w), hasMagicWord);
        return IffWith(F.Id("claim"), OnEndpoints(
            Implies(Call("CartanOrigin", F.Id("M")),
                Implies(Call("BruhatLE", cs, v, w), equivalence))));
    }

    private static Formula InCoxeterSystem(Formula body)
    {
        var s = F.Id("S");
        var m = F.Id("M");
        var group = F.Id("W");
        return All("S", F.Id("Type"), All("M", Call("CoxeterMatrix", s),
            All("W", F.Id("Type"), Seq(OpenBracket, Call("Group", group), CloseBracket, Sp,
                All("cs", Call("CoxeterSystem", m, group), body)))));
    }

    private static Formula OnEndpoints(Formula body) =>
        InCoxeterSystem(All("v", F.Id("W"), All("w", F.Id("W"), body)));

    private static Formula Words => Call("List", F.Id("S"));
    private static Formula Masks => Call("List", F.Id("Bool"));
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);

    private static Formula WordProduct(Formula cs, Formula word) =>
        Qualified("CoxeterSystem", "wordProd", cs, word);

    private static Formula Qualified(string owner, string name, params Formula[] arguments) =>
        Apply(Seq(F.Id(owner), Dot, F.Id(name)), arguments);

    private static Formula Call(string name, params Formula[] arguments) =>
        Apply(Seq(Operatorname, Grp(F.Id(name))), arguments);

    private static Formula Apply(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);

    private static Formula Equal(Formula left, Formula right) =>
        Relation(left, FormulaRelationOperator.Equal, right);

    private static Formula Relation(Formula left, FormulaRelationOperator op, Formula right) =>
        new Formula.Relation(left, op, right);

    private static Formula Logic(Formula left, FormulaLogicOperator op, Formula right) =>
        new Formula.Logic(left, op, right);

    private static Formula And(Formula left, Formula right) => Logic(left, FormulaLogicOperator.And, right);
    private static Formula Implies(Formula left, Formula right) => Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula IffWith(Formula left, Formula right) =>
        Logic(left, FormulaLogicOperator.Iff, Parenthesized(right));

    private static Formula All(string name, Formula type, Formula body) =>
        Bind(FormulaQuantifier.ForAll, name, type, body);

    private static Formula ExistsIn(string name, Formula type, Formula body) =>
        Bind(FormulaQuantifier.Exists, name, type, body);

    private static Formula Bind(FormulaQuantifier quantifier, string name, Formula type, Formula body) =>
        new Formula.Bind(quantifier, FormulaIdentifier.Create(name), type, body);
}
